//! Import edits for moving one Python module file.
//!
//! The move may cross package directories or configured module search paths. A coordinated
//! `.py`/`.pyi` pair is treated as one module. Existing import forms and explicit aliases are
//! preserved; unaliased import bindings and their direct semantic uses are renamed when safe. An
//! existing destination-package binding may be reused only when ty can prove that it refers to the
//! same package as the destination.
//!
//! The supported core is deliberately narrow. Source and destination paths must each have one
//! ordinary module identity, outside stdlib search paths, and destination components must be ASCII
//! names that do not begin with `__`. Package moves, unrelated batches, PEP 561 `-stubs` packages,
//! ambiguous bindings, package-member collisions, and edits requiring import restructuring or
//! synthesized aliases are rejected as a whole.
//!
//! Dynamic strings, stringized annotations, and references rooted in arbitrary expressions are
//! outside the semantic-retargeting contract and may be left unchanged.

use std::collections::hash_map::Entry;
use std::sync::atomic::{AtomicBool, Ordering};

use crate::references::contains_identifier;
use ruff_db::files::{File, system_path_to_file};
use ruff_db::source::source_text;
use ruff_db::system::{SystemPath, SystemPathBuf};
use ruff_python_ast::token::{TokenKind, Tokens};
use ruff_python_ast::{
    self as ast, AnyNodeRef,
    visitor::source_order::{SourceOrderVisitor, TraversalSignal},
};
use ruff_text_size::{Ranged, TextRange};
use rustc_hash::{FxHashMap, FxHashSet};
use ty_module_resolver::{
    Module, ModuleName, ModuleResolveMode, SearchPath, file_to_module, resolve_module,
    resolve_real_module, search_paths,
};
use ty_project::Db;
use ty_python_core::definition::{Definition, DefinitionKind};
use ty_python_core::scope::FileScopeId;
use ty_python_core::semantic_index;
use ty_python_semantic::types::Type;
use ty_python_semantic::{
    Db as SemanticDb, HasType, ImportAliasResolution, ResolvedDefinition, SemanticModel,
    definitions_for_name,
};

/// A text edit to apply before moving a module file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FileRenameEdit {
    file: File,
    range: TextRange,
    new_text: String,
}

/// The requested module move cannot be represented safely by syntax-preserving edits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UnsupportedFileRename;

impl FileRenameEdit {
    /// Decomposes this edit into its target file, range, and replacement text.
    pub fn into_parts(self) -> (File, TextRange, String) {
        (self.file, self.range, self.new_text)
    }
}

/// A Python module file move received from the client.
#[derive(Debug, Clone)]
pub struct PathRename {
    old_path: SystemPathBuf,
    new_path: SystemPathBuf,
}

impl PathRename {
    /// Creates a file rename from `old_path` to `new_path`.
    pub fn file(old_path: SystemPathBuf, new_path: SystemPathBuf) -> Self {
        Self { old_path, new_path }
    }
}

struct ModuleMove {
    old: ModuleName,
    new: ModuleName,
    destination_search_path: SearchPath,
    anchors: FxHashSet<File>,
}

impl ModuleMove {
    fn rewrite(&self, name: &ModuleName) -> Option<&ModuleName> {
        (name == &self.old).then_some(&self.new)
    }

    fn contains_module(&self, db: &dyn SemanticDb, module: Module<'_>) -> bool {
        module
            .file(db)
            .is_some_and(|file| self.anchors.contains(&file))
    }

    /// Returns whether an existing expression depends on package-loading side effects changed by
    /// the rewritten import. References rooted at the moved module itself are handled separately.
    fn changes_package_path_for_existing_expression(&self, name: &ModuleName) -> bool {
        if name.starts_with(&self.old) {
            return false;
        }

        let uses_removed_old_prefix = std::iter::successors(self.old.parent(), ModuleName::parent)
            .any(|prefix| !self.new.starts_with(&prefix) && name.starts_with(&prefix));
        let uses_added_new_path = self
            .new
            .ancestors()
            .any(|prefix| !self.old.starts_with(&prefix) && name.starts_with(&prefix));

        uses_removed_old_prefix || uses_added_new_path
    }
}

struct ImportingModule {
    name_after_move: ModuleName,
    is_package: bool,
    moved: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ImportBindingKind {
    Import,
    ImportFrom,
}

#[derive(Debug)]
struct RenamedImportBinding {
    new: String,
    kind: ImportBindingKind,
}

enum TrackedImportBinding {
    Stable,
    Renamed(RenamedImportBinding),
}

#[derive(Default)]
struct RenamedImportBindings {
    by_scope: FxHashMap<FileScopeId, FxHashMap<String, TrackedImportBinding>>,
    old_names: FxHashSet<String>,
    new_names: FxHashSet<String>,
}

impl RenamedImportBindings {
    fn insert(
        &mut self,
        scope: FileScopeId,
        old: &str,
        new: &str,
        kind: ImportBindingKind,
    ) -> bool {
        if old == new {
            return self.insert_stable(scope, old);
        }
        self.old_names.insert(old.to_string());
        self.new_names.insert(new.to_string());

        match self
            .by_scope
            .entry(scope)
            .or_default()
            .entry(old.to_string())
        {
            Entry::Vacant(entry) => {
                entry.insert(TrackedImportBinding::Renamed(RenamedImportBinding {
                    new: new.to_string(),
                    kind,
                }));
                true
            }
            Entry::Occupied(entry) => matches!(
                entry.get(),
                TrackedImportBinding::Renamed(binding)
                    if binding.new == new && binding.kind == kind
            ),
        }
    }

    fn insert_stable(&mut self, scope: FileScopeId, name: &str) -> bool {
        match self
            .by_scope
            .entry(scope)
            .or_default()
            .entry(name.to_string())
        {
            Entry::Vacant(entry) => {
                entry.insert(TrackedImportBinding::Stable);
                true
            }
            Entry::Occupied(_) => false,
        }
    }

    fn binding_for_name<'a>(
        &'a self,
        model: &SemanticModel<'_>,
        name: &ast::ExprName,
    ) -> Option<&'a RenamedImportBinding> {
        let index = semantic_index(model.db(), model.file());
        let scope = model.scope(name.into())?;
        for (visible_scope, _) in index.visible_ancestor_scopes(scope) {
            if let Some(symbol) = index
                .place_table(visible_scope)
                .symbol_by_name(name.id.as_str())
            {
                if !symbol.is_bound() {
                    continue;
                }
                return match self
                    .by_scope
                    .get(&visible_scope)
                    .and_then(|bindings| bindings.get(name.id.as_str()))
                {
                    Some(TrackedImportBinding::Renamed(binding)) => Some(binding),
                    Some(TrackedImportBinding::Stable) | None => None,
                };
            }
        }
        None
    }

    fn contains_old_name(&self, name: &str) -> bool {
        self.old_names.contains(name)
    }

    fn contains_new_name(&self, name: &str) -> bool {
        self.new_names.contains(name)
    }

    fn destination_name_is_affected(
        &self,
        model: &SemanticModel<'_>,
        name: &ast::ExprName,
    ) -> bool {
        if !self.contains_new_name(name.id.as_str()) {
            return false;
        }

        let index = semantic_index(model.db(), model.file());
        let Some(scope) = model.scope(name.into()) else {
            return true;
        };
        for (visible_scope, scope_info) in index.visible_ancestor_scopes(scope) {
            if self.by_scope.get(&visible_scope).is_some_and(|bindings| {
                bindings.values().any(|binding| {
                    matches!(
                        binding,
                        TrackedImportBinding::Renamed(binding)
                            if binding.new == name.id.as_str()
                    )
                })
            }) {
                return true;
            }
            // Class-body lookup can still fall through to an enclosing scope before a local
            // assignment, so only non-class bindings stop the search.
            if index
                .place_table(visible_scope)
                .symbol_by_name(name.id.as_str())
                .is_some_and(ty_python_core::symbol::Symbol::is_bound)
                && !scope_info.kind().is_class()
            {
                return false;
            }
        }
        false
    }
}

/// Compute edits for a single logical module-file move.
///
/// A paired `.py` and `.pyi` move is accepted as one logical move. Directory
/// moves, unrelated file batches, extension changes, and partial source/stub
/// moves are intentionally unsupported and return [`UnsupportedFileRename`].
pub fn will_rename_paths(
    db: &dyn Db,
    renames: &[PathRename],
) -> Result<Vec<FileRenameEdit>, UnsupportedFileRename> {
    let project = db.project();
    let indexed_files = project.files(db);
    let open_files = project.open_files(db);

    will_rename_paths_in_files(
        db,
        renames,
        (&indexed_files)
            .into_iter()
            .chain(open_files.iter().copied()),
    )
}

/// Compute rename edits while considering only `files` as possible consumers.
///
/// The moved files are always included so that their relative imports can be updated. Filtering
/// consumers before analysis prevents an unsupported reference outside the caller's ownership
/// boundary from cancelling otherwise safe edits inside it.
fn will_rename_paths_in_files(
    db: &dyn Db,
    renames: &[PathRename],
    files: impl IntoIterator<Item = File>,
) -> Result<Vec<FileRenameEdit>, UnsupportedFileRename> {
    let Some(module_move) = module_move(db, renames) else {
        return Err(UnsupportedFileRename);
    };
    if module_move.old == module_move.new {
        return Ok(Vec::new());
    }

    let needle = module_move.old.last_component();
    let mut files: FxHashSet<_> = files.into_iter().collect();
    files.extend(module_move.anchors.iter().copied());
    let mut files: Vec<_> = files.into_iter().collect();
    files.sort_unstable();
    let result = std::sync::Mutex::new(Vec::new());
    let supported = AtomicBool::new(true);

    {
        let db = Db::dyn_clone(db);
        let result = &result;
        let supported = &supported;
        let module_move = &module_move;

        rayon::scope(move |scope| {
            for file in files {
                let db = Db::dyn_clone(&*db);
                scope.spawn(move |_| {
                    if !supported.load(Ordering::Relaxed) {
                        return;
                    }
                    let db = &*db;
                    let source = source_text(db, file);
                    if source.read_error().is_some() {
                        supported.store(false, Ordering::Relaxed);
                        return;
                    }
                    if !module_move.anchors.contains(&file) && !contains_identifier(&source, needle)
                    {
                        return;
                    }
                    let parsed = ruff_db::parsed::parsed_module(db, file);
                    let module = parsed.load(db);
                    let importing_module = file_to_module(db, file).map(|module| {
                        let old_name = module.name(db);
                        let new_name = module_move.rewrite(old_name);
                        ImportingModule {
                            name_after_move: new_name.unwrap_or(old_name).clone(),
                            is_package: module.kind(db).is_package(),
                            moved: new_name.is_some(),
                        }
                    });

                    let model = SemanticModel::new(db, file);
                    let Some(renamed_bindings) =
                        renamed_import_bindings(&model, module.syntax(), module_move)
                    else {
                        supported.store(false, Ordering::Relaxed);
                        return;
                    };
                    let mut edits = Vec::new();
                    let mut file_supported = true;
                    let mut finder = ModuleMoveFinder {
                        model: &model,
                        tokens: module.tokens(),
                        source: source.as_str(),
                        module_move,
                        importing_module: importing_module.as_ref(),
                        edits: &mut edits,
                        supported: &mut file_supported,
                        renamed_bindings: &renamed_bindings,
                    };
                    AnyNodeRef::from(module.syntax()).visit_source_order(&mut finder);

                    if file_supported {
                        result.lock().unwrap().extend(edits);
                    } else {
                        supported.store(false, Ordering::Relaxed);
                    }
                });
            }
        });
    }

    if !supported.load(Ordering::Relaxed) {
        return Err(UnsupportedFileRename);
    }

    let mut edits = result.into_inner().unwrap();
    edits.sort_by(|left, right| {
        left.file
            .cmp(&right.file)
            .then_with(|| left.range.start().cmp(&right.range.start()))
            .then_with(|| left.range.end().cmp(&right.range.end()))
            .then_with(|| left.new_text.cmp(&right.new_text))
    });
    edits.dedup();
    // Overlapping edits cannot be represented safely in an LSP workspace edit.
    if edits.windows(2).any(|edits| {
        edits[0].file == edits[1].file
            && (edits[0].range.start() == edits[1].range.start()
                || edits[0].range.end() > edits[1].range.start())
    }) {
        return Err(UnsupportedFileRename);
    }
    Ok(edits)
}

fn module_move(db: &dyn Db, renames: &[PathRename]) -> Option<ModuleMove> {
    if renames.len() > 2
        || renames.len() == 2
            && (paired_python_path(&renames[0].old_path).as_deref()
                != Some(renames[1].old_path.as_path())
                || paired_python_path(&renames[0].new_path).as_deref()
                    != Some(renames[1].new_path.as_path()))
    {
        return None;
    }

    let file_renames: FxHashMap<_, _> = renames
        .iter()
        .filter_map(|rename| {
            system_path_to_file(db, &rename.old_path)
                .ok()
                .map(|file| (file, rename.new_path.as_path()))
        })
        .collect();
    if file_renames.len() != renames.len() {
        return None;
    }

    let mut semantic_move: Option<(ModuleName, ModuleName, SearchPath)> = None;
    let mut anchors = FxHashSet::default();

    for rename in renames {
        if !paired_file_moves_consistently(db, rename, &file_renames) {
            return None;
        }
        let (old, new, destination_search_path, anchor) = module_move_for_path(db, rename)?;
        anchors.insert(anchor);
        match &semantic_move {
            None => semantic_move = Some((old, new, destination_search_path)),
            Some((semantic_old, semantic_new, semantic_destination_search_path))
                if semantic_old == &old
                    && semantic_new == &new
                    && semantic_destination_search_path == &destination_search_path => {}
            Some(_) => return None,
        }
    }

    let (old, new, destination_search_path) = semantic_move?;
    Some(ModuleMove {
        old,
        new,
        destination_search_path,
        anchors,
    })
}

fn paired_file_moves_consistently(
    db: &dyn Db,
    rename: &PathRename,
    file_renames: &FxHashMap<File, &SystemPath>,
) -> bool {
    let Ok(old_file) = system_path_to_file(db, &rename.old_path) else {
        return false;
    };
    let Some(old_module) = file_to_module(db, old_file) else {
        return false;
    };
    let paired_file = if old_file.is_stub(db) {
        resolve_real_module(db, old_file, old_module.name(db)).and_then(|module| module.file(db))
    } else {
        resolve_module(db, old_file, old_module.name(db))
            .and_then(|module| module.file(db))
            .filter(|file| file.is_stub(db))
    };
    let Some(paired_file) = paired_file.filter(|paired_file| *paired_file != old_file) else {
        return true;
    };
    let Some(paired_new_path) = paired_python_path(&rename.new_path) else {
        return false;
    };
    file_renames
        .get(&paired_file)
        .is_some_and(|new_path| *new_path == paired_new_path.as_path())
}

fn paired_python_path(path: &SystemPath) -> Option<SystemPathBuf> {
    Some(match path.extension()? {
        "py" => path.with_extension("pyi"),
        "pyi" => path.with_extension("py"),
        _ => return None,
    })
}

fn module_move_for_path(
    db: &dyn Db,
    rename: &PathRename,
) -> Option<(ModuleName, ModuleName, SearchPath, File)> {
    if rename.old_path.extension() != rename.new_path.extension()
        || !matches!(rename.new_path.extension(), Some("py" | "pyi"))
        || rename.old_path.file_stem() == Some("__init__")
        || rename.new_path.file_stem() == Some("__init__")
    {
        return None;
    }

    let old_identity = unique_module_identity_for_path(db, &rename.old_path)?;
    let new_identity = unique_module_identity_for_path(db, &rename.new_path)?;
    let old_file = system_path_to_file(db, &rename.old_path).ok()?;
    let old_module = file_to_module(db, old_file)?;
    if old_module.name(db) != &old_identity.name
        || old_module.search_path(db) != Some(&old_identity.search_path)
        || old_identity.name == new_identity.name
            && old_identity.search_path != new_identity.search_path
    {
        return None;
    }
    if new_identity
        .name
        .components()
        .any(|component| !component.is_ascii() || component.starts_with("__"))
    {
        return None;
    }
    if ruff_python_stdlib::sys::is_builtin_module(
        db.python_version().minor,
        new_identity.name.as_str(),
    ) {
        return None;
    }
    if !destination_is_available(db, old_file, &new_identity) {
        return None;
    }

    Some((
        old_identity.name,
        new_identity.name,
        new_identity.search_path,
        old_file,
    ))
}

struct ModulePathIdentity {
    name: ModuleName,
    search_path: SearchPath,
}

/// Resolves a filesystem path back to exactly one importable module identity.
///
/// Search-path precedence is intentionally ignored here: a path below overlapping roots is
/// ambiguous even when the regular module resolver would consistently choose one spelling.
fn unique_module_identity_for_path(db: &dyn Db, path: &SystemPath) -> Option<ModulePathIdentity> {
    let path = SystemPath::absolute(path, db.system().current_directory());
    let stem = path.file_stem()?;
    let mut identity: Option<ModulePathIdentity> = None;

    for search_path in search_paths(db, ModuleResolveMode::StubsAllowed) {
        let Some(root) = search_path.as_system_path() else {
            continue;
        };
        let Ok(relative) = path.strip_prefix(root) else {
            continue;
        };
        if search_path.is_standard_library() {
            return None;
        }
        let Some(parent) = relative.parent() else {
            continue;
        };
        let Some(name) = ModuleName::from_components(
            parent
                .components()
                .map(|component| component.as_str())
                .chain(std::iter::once(stem)),
        ) else {
            continue;
        };

        match &identity {
            None => {
                identity = Some(ModulePathIdentity {
                    name,
                    search_path: search_path.clone(),
                });
            }
            Some(existing) if existing.name == name => {}
            Some(_) => return None,
        }
    }

    identity
}

fn destination_is_available(db: &dyn Db, old_file: File, destination: &ModulePathIdentity) -> bool {
    let new_name = &destination.name;
    let destination_search_path = &destination.search_path;

    if resolve_module(db, old_file, new_name)
        .is_some_and(|module| module.file(db) != Some(old_file))
    {
        return false;
    }
    if destination_package_path_statically_binds_member(db, old_file, new_name) {
        return false;
    }

    new_name.parent().is_none_or(|parent| {
        parent.ancestors().all(|parent| {
            let Some(module) = resolve_module(db, old_file, &parent) else {
                return true;
            };
            if !module.kind(db).is_package() {
                return false;
            }
            module
                .file(db)
                .is_none_or(|_| module.search_path(db) == Some(destination_search_path))
        })
    })
}

fn destination_package_path_statically_binds_member(
    db: &dyn Db,
    importing_file: File,
    destination: &ModuleName,
) -> bool {
    destination.ancestors().any(|child| {
        let Some(parent) = child.parent() else {
            return false;
        };
        package_statically_binds_member(db, importing_file, &parent, child.last_component())
    })
}

fn package_statically_binds_member(
    db: &dyn Db,
    importing_file: File,
    package_name: &ModuleName,
    member: &str,
) -> bool {
    let mut initializer_files = FxHashSet::default();
    for package in [
        resolve_module(db, importing_file, package_name),
        resolve_real_module(db, importing_file, package_name),
    ]
    .into_iter()
    .flatten()
    {
        if package.kind(db).is_package()
            && let Some(file) = package.file(db)
        {
            initializer_files.insert(file);
        }
    }

    initializer_files.into_iter().any(|file| {
        let symbols = semantic_index(db, file).place_table(FileScopeId::global());
        [member, "__getattr__"].into_iter().any(|name| {
            symbols
                .symbol_by_name(name)
                .is_some_and(|symbol| symbol.is_bound() || symbol.is_declared())
        })
    })
}

struct ModuleMoveFinder<'a, 'db> {
    model: &'a SemanticModel<'db>,
    tokens: &'a Tokens,
    source: &'a str,
    module_move: &'a ModuleMove,
    importing_module: Option<&'a ImportingModule>,
    edits: &'a mut Vec<FileRenameEdit>,
    supported: &'a mut bool,
    renamed_bindings: &'a RenamedImportBindings,
}

impl<'ast> SourceOrderVisitor<'ast> for ModuleMoveFinder<'_, '_> {
    fn enter_node(&mut self, node: AnyNodeRef<'ast>) -> TraversalSignal {
        match node {
            AnyNodeRef::StmtImport(import) => {
                self.check_import(import);
                TraversalSignal::Skip
            }
            AnyNodeRef::StmtImportFrom(import_from) => {
                self.check_import_from(import_from);
                TraversalSignal::Skip
            }
            AnyNodeRef::StmtGlobal(ast::StmtGlobal { names, .. })
            | AnyNodeRef::StmtNonlocal(ast::StmtNonlocal { names, .. }) => {
                if names.iter().any(|name| {
                    self.renamed_bindings.contains_old_name(name.as_str())
                        || self.renamed_bindings.contains_new_name(name.as_str())
                }) {
                    *self.supported = false;
                }
                TraversalSignal::Skip
            }
            AnyNodeRef::ExprName(name) => {
                if self
                    .renamed_bindings
                    .destination_name_is_affected(self.model, name)
                {
                    *self.supported = false;
                    return TraversalSignal::Skip;
                }
                if self.check_module_expression(ast::ExprRef::Name(name)) {
                    TraversalSignal::Skip
                } else {
                    TraversalSignal::Traverse
                }
            }
            AnyNodeRef::ExprAttribute(attribute) => {
                if self.check_module_expression(ast::ExprRef::Attribute(attribute)) {
                    TraversalSignal::Skip
                } else {
                    TraversalSignal::Traverse
                }
            }
            _ => TraversalSignal::Traverse,
        }
    }
}

impl ModuleMoveFinder<'_, '_> {
    fn check_import(&mut self, import: &ast::StmtImport) {
        for alias in &import.names {
            let Some(module) = self.model.resolve_module(Some(alias.name.as_str()), 0) else {
                continue;
            };
            let old_name = module.name(self.model.db());

            if let Some(new_name) = self.module_move.rewrite(old_name) {
                if alias.asname.is_none()
                    && old_name.first_component() == new_name.first_component()
                    && self.import_binding_has_incompatible_definition(
                        alias,
                        old_name.first_component(),
                    )
                {
                    *self.supported = false;
                    return;
                }
                if alias.asname.is_none()
                    && old_name.first_component() != new_name.first_component()
                    && self.import_binding_conflicts(new_name.first_component(), alias)
                {
                    return;
                }
                self.add_edit(alias.name.range, new_name.as_str());
            }
        }
    }

    fn check_import_from(&mut self, import: &ast::StmtImportFrom) {
        let Ok(old_parent) =
            ModuleName::from_import_statement(self.model.db(), self.model.file(), import)
        else {
            return;
        };

        if old_parent != self.module_move.old
            && self.module_move.old.starts_with(&old_parent)
            && import.names.iter().any(|alias| alias.name.as_str() == "*")
        {
            *self.supported = false;
            return;
        }

        let default_parent = self
            .module_move
            .rewrite(&old_parent)
            .cloned()
            .unwrap_or_else(|| old_parent.clone());
        let mut statement_parent = None;
        let mut alias_edits = Vec::new();

        for alias in &import.names {
            if moved_import_from_reexport_is_unsupported(
                self.model,
                self.module_move,
                &old_parent,
                alias,
            ) {
                *self.supported = false;
                return;
            }
            let alias_parent = if let Some(new_name) =
                moved_import_from_submodule(self.model, self.module_move, &old_parent, alias)
            {
                // Converting `from package import module` into `import module` would
                // require replacing the full statement and preserving arbitrary trivia.
                // Keep that structural conversion outside the supported scope.
                let Some(new_parent) = new_name.parent() else {
                    *self.supported = false;
                    return;
                };

                if alias.name.as_str() != new_name.last_component() {
                    if alias.asname.is_none()
                        && self.import_binding_conflicts(new_name.last_component(), alias)
                    {
                        return;
                    }
                    alias_edits.push((alias.name.range, new_name.last_component().to_string()));
                }
                new_parent
            } else {
                default_parent.clone()
            };

            if statement_parent
                .as_ref()
                .is_some_and(|parent| parent != &alias_parent)
            {
                *self.supported = false;
                return;
            }
            statement_parent.get_or_insert(alias_parent);
        }

        let statement_parent = statement_parent.unwrap_or(default_parent);
        let importing_context_changed = import.level > 0
            && self
                .importing_module
                .is_some_and(|importing_module| importing_module.moved);
        if statement_parent != old_parent || importing_context_changed {
            self.add_import_from_module_edit(import, &statement_parent);
        }
        for (range, new_name) in alias_edits {
            self.add_edit(range, new_name);
        }
    }

    fn check_module_expression(&mut self, expression: ast::ExprRef<'_>) -> bool {
        if let ast::ExprRef::Name(name) = expression
            && self.reject_mixed_import_binding(name)
        {
            return true;
        }
        if let ast::ExprRef::Name(name) = expression
            && name.ctx == ast::ExprContext::Del
            && let Some(binding) = self.renamed_bindings.binding_for_name(self.model, name)
        {
            self.add_edit(name.range, &binding.new);
            return true;
        }
        let Some((root, expression_name)) = module_expression_identity(self.model, expression)
        else {
            if let ast::ExprRef::Name(name) = expression
                && self
                    .renamed_bindings
                    .binding_for_name(self.model, name)
                    .is_some()
            {
                *self.supported = false;
                return true;
            }
            return false;
        };
        if self
            .module_move
            .changes_package_path_for_existing_expression(&expression_name)
        {
            *self.supported = false;
            return true;
        }
        let inferred_type = expression.inferred_type(self.model);
        let Some(Type::ModuleLiteral(module)) = inferred_type else {
            if expression_name == self.module_move.old {
                *self.supported = false;
                return true;
            }
            return false;
        };
        let module = module.module(self.model.db());
        let old_name = module.name(self.model.db());
        if self.module_move.contains_module(self.model.db(), module)
            && self.module_move.rewrite(old_name).is_none()
        {
            *self.supported = false;
            return true;
        }
        if &expression_name != old_name {
            if expression_name == self.module_move.old
                || self.module_move.rewrite(old_name).is_some()
            {
                *self.supported = false;
                return true;
            }
            return false;
        }
        let Some(new_name) = self.module_move.rewrite(old_name) else {
            if self
                .renamed_bindings
                .binding_for_name(self.model, root)
                .is_some()
            {
                *self.supported = false;
                return true;
            }
            return false;
        };
        let Some(Type::ModuleLiteral(root_module)) = root.inferred_type(self.model) else {
            return false;
        };
        let old_root = root_module.module(self.model.db()).name(self.model.db());
        let new_root = self
            .module_move
            .rewrite(old_root)
            .cloned()
            .unwrap_or_else(|| old_root.clone());

        let root_name = root.id.as_str();
        if module_root_binding_is_mixed(self.model, root, old_root) {
            *self.supported = false;
            return true;
        }
        let range = expression.range();
        let Some(original) = render_from_root(root_name, old_root, &expression_name) else {
            *self.supported = false;
            return true;
        };
        let source_range = usize::from(range.start())..usize::from(range.end());
        if self.source.get(source_range) != Some(original.as_str()) {
            *self.supported = false;
            return true;
        }
        let renamed_binding = self.renamed_bindings.binding_for_name(self.model, root);
        let replacement = match renamed_binding {
            Some(RenamedImportBinding {
                kind: ImportBindingKind::Import,
                ..
            }) => Some(new_name.as_str().to_string()),
            Some(RenamedImportBinding {
                new,
                kind: ImportBindingKind::ImportFrom,
            }) => Some(new.clone()),
            None => render_from_root(root_name, &new_root, new_name),
        };
        let Some(replacement) = replacement else {
            *self.supported = false;
            return true;
        };
        if self.replacement_binding_conflicts(root, &replacement) {
            *self.supported = false;
            return true;
        }

        self.add_edit(range, replacement);
        true
    }

    fn reject_mixed_import_binding(&mut self, name: &ast::ExprName) -> bool {
        let Some(new_binding) = self.renamed_bindings.binding_for_name(self.model, name) else {
            return false;
        };
        let definitions = definitions_for_name(
            self.model,
            name.id.as_str(),
            name.into(),
            ImportAliasResolution::PreserveAliases,
        );
        let db = self.model.db();
        let mut has_changed_module_binding = false;
        let mut has_inconsistent_binding = false;
        for definition in &definitions {
            let changes_consistently = (|| {
                let ResolvedDefinition::Module(file) = definition else {
                    return false;
                };
                let Some(module) = file_to_module(db, *file) else {
                    return false;
                };
                let old_name = module.name(db);
                let Some(new_name) = self.module_move.rewrite(old_name) else {
                    return false;
                };
                let rewritten_binding = match new_binding.kind {
                    ImportBindingKind::Import => new_name.first_component(),
                    ImportBindingKind::ImportFrom => new_name.last_component(),
                };
                rewritten_binding == new_binding.new
            })();
            has_changed_module_binding |= changes_consistently;
            has_inconsistent_binding |= !changes_consistently;
        }
        if has_changed_module_binding && has_inconsistent_binding {
            *self.supported = false;
            true
        } else {
            false
        }
    }

    fn import_binding_conflicts(&mut self, new_binding: &str, alias: &ast::Alias) -> bool {
        let index = semantic_index(self.model.db(), self.model.file());
        let scope = index
            .expect_single_definition(alias)
            .file_scope(self.model.db());
        if self
            .binding_in_scope_is_compatible_destination_package(scope, new_binding)
            .is_some_and(|compatible| !compatible)
        {
            *self.supported = false;
            true
        } else {
            false
        }
    }

    fn replacement_binding_conflicts(&self, root: &ast::ExprName, replacement: &str) -> bool {
        let Some(new_binding) = replacement
            .split('.')
            .next()
            .filter(|new_binding| *new_binding != root.id.as_str())
        else {
            return false;
        };
        let Some(scope) = self.model.scope(root.into()) else {
            return true;
        };
        self.visible_binding_is_compatible_destination_package(scope, new_binding)
            .is_some_and(|compatible| !compatible)
    }

    fn visible_binding_is_compatible_destination_package(
        &self,
        scope: FileScopeId,
        binding: &str,
    ) -> Option<bool> {
        let index = semantic_index(self.model.db(), self.model.file());
        index.visible_ancestor_scopes(scope).find_map(|(scope, _)| {
            self.binding_in_scope_is_compatible_destination_package(scope, binding)
        })
    }

    /// Returns `None` when the scope has no binding and otherwise whether every definition is an
    /// import of the destination's package root.
    fn binding_in_scope_is_compatible_destination_package(
        &self,
        scope: FileScopeId,
        binding: &str,
    ) -> Option<bool> {
        let index = semantic_index(self.model.db(), self.model.file());
        let places = index.place_table(scope);
        let symbol = places.symbol_id(binding)?;
        if !places.symbol(symbol).is_bound() {
            return None;
        }

        if !resolve_module(
            self.model.db(),
            self.model.file(),
            &ModuleName::new(binding)?,
        )
        .is_some_and(|module| self.module_is_destination_root_package(module, binding))
        {
            return Some(false);
        }

        let mut saw_definition = false;
        for reachable in index.use_def_map(scope).reachable_symbol_bindings(symbol) {
            let Some(definition) = reachable.binding.definition() else {
                continue;
            };
            if !self.definition_is_compatible_destination_package_import(definition, binding) {
                return Some(false);
            }
            saw_definition = true;
        }
        Some(saw_definition)
    }

    fn definition_is_compatible_destination_package_import(
        &self,
        definition: Definition<'_>,
        binding: &str,
    ) -> bool {
        let DefinitionKind::Import(import) = definition.kind(self.model.db()) else {
            return false;
        };
        let parsed = ruff_db::parsed::parsed_module(self.model.db(), self.model.file());
        let module = parsed.load(self.model.db());
        let alias = import.alias(&module);
        let Some(imported) = self.model.resolve_module(Some(alias.name.as_str()), 0) else {
            return false;
        };
        let imported_name = imported.name(self.model.db());
        if let Some(asname) = &alias.asname {
            asname.as_str() == binding && imported_name.as_str() == binding
        } else {
            imported_name.first_component() == binding
        }
    }

    fn module_is_destination_root_package(&self, module: Module<'_>, binding: &str) -> bool {
        binding == self.module_move.new.first_component()
            && self.module_move.new.parent().is_some()
            && module.name(self.model.db()).as_str() == binding
            && module.kind(self.model.db()).is_package()
            && module
                .search_path(self.model.db())
                .is_none_or(|search_path| search_path == &self.module_move.destination_search_path)
    }

    fn import_binding_has_incompatible_definition(
        &self,
        alias: &ast::Alias,
        binding: &str,
    ) -> bool {
        let index = semantic_index(self.model.db(), self.model.file());
        let import_definition = index.expect_single_definition(alias);
        let scope = import_definition.file_scope(self.model.db());
        let Some(symbol) = index.place_table(scope).symbol_id(binding) else {
            return true;
        };
        let module = ruff_db::parsed::parsed_module(self.model.db(), self.model.file());
        let module = module.load(self.model.db());
        index
            .use_def_map(scope)
            .reachable_symbol_bindings(symbol)
            .filter_map(|binding| binding.binding.definition())
            .any(|definition| match definition.kind(self.model.db()) {
                DefinitionKind::Import(import) => {
                    let alias = import.alias(&module);
                    if let Some(asname) = &alias.asname {
                        asname.as_str() != binding || alias.name.as_str() != binding
                    } else {
                        alias
                            .name
                            .split('.')
                            .next()
                            .is_none_or(|root| root != binding)
                    }
                }
                _ => true,
            })
    }

    fn add_import_from_module_edit(&mut self, import: &ast::StmtImportFrom, new_name: &ModuleName) {
        let Some(range) = import_from_module_range(self.tokens, import) else {
            return;
        };
        let replacement = render_import_from_module(import, new_name, self.importing_module);
        self.add_edit(range, replacement);
    }

    fn add_edit(&mut self, range: TextRange, new_text: impl Into<String>) {
        let new_text = new_text.into();
        let source_range = usize::from(range.start())..usize::from(range.end());
        if self.source.get(source_range) == Some(new_text.as_str()) {
            return;
        }
        self.edits.push(FileRenameEdit {
            file: self.model.file(),
            range,
            new_text,
        });
    }
}

/// Returns whether `root` mixes the expected module import with another binding.
///
/// Explicit aliases and other bindings keep their local spelling when the
/// module moves. Unaliased imports change the bound name with the import and
/// therefore require matching edits at their use sites.
fn module_root_binding_is_mixed(
    model: &SemanticModel<'_>,
    root: &ast::ExprName,
    expected: &ModuleName,
) -> bool {
    if root.id != expected.first_component() && root.id != expected.last_component() {
        return false;
    }
    let definitions = definitions_for_name(
        model,
        root.id.as_str(),
        root.into(),
        ImportAliasResolution::PreserveAliases,
    );
    let db = model.db();
    let mut has_expected_module = false;
    let mut has_other = has_non_import_binding(model, root);
    for definition in definitions {
        let matches_expected = match definition {
            ResolvedDefinition::Module(file) => {
                file_to_module(db, file).is_some_and(|module| module.name(db) == expected)
            }
            ResolvedDefinition::Definition(_) | ResolvedDefinition::FileWithRange(_) => false,
        };
        has_expected_module |= matches_expected;
        has_other |= !matches_expected;
    }
    has_expected_module && has_other
}

fn has_non_import_binding(model: &SemanticModel<'_>, root: &ast::ExprName) -> bool {
    let index = semantic_index(model.db(), model.file());
    let Some(scope) = model.scope(root.into()) else {
        return true;
    };
    index
        .visible_ancestor_scopes(scope)
        .find_map(|(scope, _)| {
            let symbol = index.place_table(scope).symbol_id(root.id.as_str())?;
            Some(
                index
                    .use_def_map(scope)
                    .reachable_symbol_bindings(symbol)
                    .filter_map(|binding| binding.binding.definition())
                    .any(|definition| !definition.kind(model.db()).is_import()),
            )
        })
        .unwrap_or(false)
}

fn render_from_root(root: &str, root_name: &ModuleName, full_name: &ModuleName) -> Option<String> {
    if root_name == full_name {
        Some(root.to_string())
    } else {
        full_name
            .relative_to(root_name)
            .map(|suffix| format!("{root}.{suffix}"))
    }
}

fn module_expression_identity<'a>(
    model: &SemanticModel<'_>,
    expression: ast::ExprRef<'a>,
) -> Option<(&'a ast::ExprName, ModuleName)> {
    let mut attributes = Vec::new();
    let root = match expression {
        ast::ExprRef::Name(name) => name,
        ast::ExprRef::Attribute(attribute) => {
            let root = expression_chain_root_and_attributes(&attribute.value, &mut attributes)?;
            attributes.push(attribute.attr.as_str());
            root
        }
        _ => return None,
    };
    let Type::ModuleLiteral(module) = root.inferred_type(model)? else {
        return None;
    };
    let root_name = module.module(model.db()).name(model.db());
    let name = ModuleName::from_components(root_name.components().chain(attributes))?;
    Some((root, name))
}

fn expression_chain_root_and_attributes<'a>(
    expression: &'a ast::Expr,
    attributes: &mut Vec<&'a str>,
) -> Option<&'a ast::ExprName> {
    match expression {
        ast::Expr::Name(name) => Some(name),
        ast::Expr::Attribute(attribute) => {
            let root = expression_chain_root_and_attributes(&attribute.value, attributes)?;
            attributes.push(attribute.attr.as_str());
            Some(root)
        }
        _ => None,
    }
}

fn is_direct_submodule_import(
    parent: &ModuleName,
    alias: &ast::Alias,
    module_name: &ModuleName,
) -> bool {
    module_name.parent().as_ref() == Some(parent)
        && module_name.last_component() == alias.name.as_str()
}

fn moved_import_from_submodule(
    model: &SemanticModel<'_>,
    module_move: &ModuleMove,
    old_parent: &ModuleName,
    alias: &ast::Alias,
) -> Option<ModuleName> {
    let Some(Type::ModuleLiteral(module)) = alias.inferred_type(model) else {
        return None;
    };
    let old_name = module.module(model.db()).name(model.db());
    is_direct_submodule_import(old_parent, alias, old_name)
        .then(|| module_move.rewrite(old_name).cloned())
        .flatten()
}

fn moved_import_from_reexport_is_unsupported(
    model: &SemanticModel<'_>,
    module_move: &ModuleMove,
    old_parent: &ModuleName,
    alias: &ast::Alias,
) -> bool {
    let Some(Type::ModuleLiteral(module)) = alias.inferred_type(model) else {
        return false;
    };
    let old_name = module.module(model.db()).name(model.db());
    let aliased_package_reexport = alias.asname.is_some()
        && file_to_module(model.db(), model.file())
            .is_some_and(|module| module.kind(model.db()).is_package());
    module_move.rewrite(old_name).is_some()
        && (aliased_package_reexport || !is_direct_submodule_import(old_parent, alias, old_name))
}

fn renamed_import_bindings(
    model: &SemanticModel<'_>,
    module: &ast::ModModule,
    module_move: &ModuleMove,
) -> Option<RenamedImportBindings> {
    let mut finder = RenamedImportBindingFinder {
        model,
        module_move,
        renamed: RenamedImportBindings::default(),
        supported: true,
    };
    AnyNodeRef::from(module).visit_source_order(&mut finder);
    finder.supported.then_some(finder.renamed)
}

struct RenamedImportBindingFinder<'a, 'db> {
    model: &'a SemanticModel<'db>,
    module_move: &'a ModuleMove,
    renamed: RenamedImportBindings,
    supported: bool,
}

impl<'ast> SourceOrderVisitor<'ast> for RenamedImportBindingFinder<'_, '_> {
    fn enter_node(&mut self, node: AnyNodeRef<'ast>) -> TraversalSignal {
        match node {
            AnyNodeRef::StmtImport(import) => {
                for alias in &import.names {
                    let Some(module) = self.model.resolve_module(Some(alias.name.as_str()), 0)
                    else {
                        continue;
                    };
                    let old_name = module.name(self.model.db());
                    if self.has_unsupported_name(module) {
                        self.supported = false;
                        return TraversalSignal::Skip;
                    }
                    if let Some(new_name) = self.module_move.rewrite(old_name) {
                        if let Some(asname) = &alias.asname {
                            self.record_stable(alias, asname.as_str());
                        } else {
                            self.record(
                                alias,
                                old_name.first_component(),
                                new_name.first_component(),
                                ImportBindingKind::Import,
                            );
                        }
                    }
                }
                TraversalSignal::Skip
            }
            AnyNodeRef::StmtImportFrom(import) => {
                let Ok(old_parent) =
                    ModuleName::from_import_statement(self.model.db(), self.model.file(), import)
                else {
                    return TraversalSignal::Skip;
                };
                if let Some(module) =
                    resolve_module(self.model.db(), self.model.file(), &old_parent)
                    && self.has_unsupported_name(module)
                {
                    self.supported = false;
                    return TraversalSignal::Skip;
                }
                for alias in &import.names {
                    let inferred = alias.inferred_type(self.model);
                    if !matches!(inferred, Some(Type::ModuleLiteral(_)))
                        && is_direct_submodule_import(&old_parent, alias, &self.module_move.old)
                    {
                        self.supported = false;
                        return TraversalSignal::Skip;
                    }
                    if let Some(Type::ModuleLiteral(module)) = inferred
                        && self.has_unsupported_name(module.module(self.model.db()))
                    {
                        self.supported = false;
                        return TraversalSignal::Skip;
                    }
                    if let Some(new_name) = moved_import_from_submodule(
                        self.model,
                        self.module_move,
                        &old_parent,
                        alias,
                    ) {
                        if let Some(asname) = &alias.asname {
                            self.record_stable(alias, asname.as_str());
                        } else {
                            self.record(
                                alias,
                                alias.name.as_str(),
                                new_name.last_component(),
                                ImportBindingKind::ImportFrom,
                            );
                        }
                    }
                }
                TraversalSignal::Skip
            }
            _ => TraversalSignal::Traverse,
        }
    }
}

impl RenamedImportBindingFinder<'_, '_> {
    fn has_unsupported_name(&self, module: Module<'_>) -> bool {
        self.module_move.contains_module(self.model.db(), module)
            && self
                .module_move
                .rewrite(module.name(self.model.db()))
                .is_none()
    }

    fn record(&mut self, alias: &ast::Alias, old: &str, new: &str, kind: ImportBindingKind) {
        let index = semantic_index(self.model.db(), self.model.file());
        let scope = index
            .expect_single_definition(alias)
            .file_scope(self.model.db());
        if !self.renamed.insert(scope, old, new, kind) {
            self.supported = false;
        }
    }

    fn record_stable(&mut self, alias: &ast::Alias, name: &str) {
        let index = semantic_index(self.model.db(), self.model.file());
        let scope = index
            .expect_single_definition(alias)
            .file_scope(self.model.db());
        if !self.renamed.insert_stable(scope, name) {
            self.supported = false;
        }
    }
}

fn import_from_module_range(tokens: &Tokens, import: &ast::StmtImportFrom) -> Option<TextRange> {
    let mut after_from = false;
    let mut first = None;
    let mut last = None;

    for token in tokens.in_range(import.range) {
        match token.kind() {
            TokenKind::From => after_from = true,
            TokenKind::Import if after_from => break,
            TokenKind::Dot | TokenKind::Ellipsis | TokenKind::Name if after_from => {
                first.get_or_insert(token.start());
                last = Some(token.end());
            }
            _ => {}
        }
    }

    Some(TextRange::new(first?, last?))
}

fn render_import_from_module(
    import: &ast::StmtImportFrom,
    new_name: &ModuleName,
    importing_module: Option<&ImportingModule>,
) -> String {
    if import.level == 0 {
        return new_name.as_str().to_string();
    }

    let Some(importing_module) = importing_module else {
        return new_name.as_str().to_string();
    };
    let level = if importing_module.is_package {
        import.level.saturating_sub(1)
    } else {
        import.level
    };
    let Some(new_base) = importing_module
        .name_after_move
        .ancestors()
        .nth(level as usize)
    else {
        return new_name.as_str().to_string();
    };

    let relative = if new_name == &new_base {
        Some(String::new())
    } else {
        new_name
            .relative_to(&new_base)
            .map(|relative| relative.as_str().to_string())
    };
    let Some(relative) = relative else {
        return new_name.as_str().to_string();
    };

    let mut rendered = ".".repeat(import.level as usize);
    rendered.push_str(&relative);
    rendered
}

#[cfg(test)]
mod tests {
    use super::*;
    use ruff_db::Db as _;
    use ruff_db::files::system_path_to_file;
    use ruff_db::source::source_text;
    use ruff_db::system::{DbWithTestSystem, DbWithWritableSystem, SystemPathBuf};
    use ruff_python_ast::PythonVersion;
    use ty_module_resolver::SearchPathSettings;
    use ty_project::{ProjectMetadata, TestDb};
    use ty_python_core::platform::PythonPlatform;
    use ty_python_core::program::{FallibleStrategy, Program, ProgramSettings};
    use ty_python_semantic::PythonVersionWithSource;

    #[test]
    fn rename_simple_import_across_scopes() {
        assert_rename(
            &[
                ("old_module.py", "x = 1\ndef hello(): ...\n"),
                (
                    "consumer.py",
                    "import old_module\nprint(old_module.x)\nold_module.hello()\ndef f():\n    return old_module.x\nclass C:\n    value = old_module.x\ndef unrelated():\n    new_module = 1\n    return new_module\n",
                ),
            ],
            "old_module.py",
            "new_module.py",
            "consumer.py",
            "import new_module\nprint(new_module.x)\nnew_module.hello()\ndef f():\n    return new_module.x\nclass C:\n    value = new_module.x\ndef unrelated():\n    new_module = 1\n    return new_module\n",
        );
    }

    #[test]
    fn rename_from_import_with_formatting() {
        assert_rename(
            &[
                ("old_module.py", "x = 1\n"),
                ("consumer.py", "from old_module import x\n"),
            ],
            "old_module.py",
            "new_module.py",
            "consumer.py",
            "from new_module import x\n",
        );
        assert_rename(
            &[
                ("pkg/__init__.py", ""),
                ("pkg/old_sub.py", "x = 1\n"),
                ("consumer.py", "from pkg . old_sub import x\n"),
            ],
            "pkg/old_sub.py",
            "pkg/new_sub.py",
            "consumer.py",
            "from pkg.new_sub import x\n",
        );
    }

    #[test]
    fn rename_relative_import() {
        assert_rename(
            &[
                (
                    "pkg/__init__.py",
                    "from .ner_model_port import NERModelPort as NERModelPort\n",
                ),
                ("pkg/ner_model_port.py", "class NERModelPort: ...\n"),
            ],
            "pkg/ner_model_port.py",
            "pkg/ner_model.py",
            "pkg/__init__.py",
            "from .ner_model import NERModelPort as NERModelPort\n",
        );
    }

    #[test]
    fn rename_from_import_with_repeated_components_uses_new_local_binding() {
        assert_rename(
            &[
                ("/foo/__init__.py", ""),
                ("/foo/foo.py", "x = 1\n"),
                ("/consumer.py", "from foo import foo\nprint(foo.x)\n"),
            ],
            "/foo/foo.py",
            "/foo/bar.py",
            "/consumer.py",
            "from foo import bar\nprint(bar.x)\n",
        );
    }

    #[test]
    fn renamed_bindings_are_scoped_to_their_imports() {
        assert_rename(
            &[
                ("/foo/__init__.py", ""),
                ("/foo/foo.py", "x = 1\n"),
                ("/bar/__init__.py", ""),
                (
                    "/consumer.py",
                    concat!(
                        "def qualified():\n",
                        "    import foo.foo\n",
                        "    return foo.foo.x\n",
                        "import foo.foo as stable\n",
                        "def local():\n",
                        "    from foo import foo\n",
                        "    return foo.x, stable.x\n",
                    ),
                ),
            ],
            "/foo/foo.py",
            "/bar/foo.py",
            "/consumer.py",
            concat!(
                "def qualified():\n",
                "    import bar.foo\n",
                "    return bar.foo.x\n",
                "import bar.foo as stable\n",
                "def local():\n",
                "    from bar import foo\n",
                "    return foo.x, stable.x\n",
            ),
        );
    }

    #[test]
    fn ambiguous_same_scope_import_bindings_are_out_of_scope() {
        for consumer in [
            "import foo.foo\nfrom foo import foo\nprint(foo.x)\n",
            "from foo import foo\nimport foo.foo\nprint(foo.x)\n",
        ] {
            assert_unsupported(
                &[
                    ("/foo/__init__.py", ""),
                    ("/foo/foo.py", "x = 1\n"),
                    ("/bar/__init__.py", ""),
                    ("/consumer.py", consumer),
                ],
                "/foo/foo.py",
                "/bar/foo.py",
            );
        }

        assert_unsupported(
            &[
                ("/foo/__init__.py", ""),
                ("/foo/foo.py", "x = 1\n"),
                (
                    "/consumer.py",
                    "from foo import foo\ndef foo(): ...\ndel foo\n",
                ),
            ],
            "/foo/foo.py",
            "/foo/bar.py",
        );
    }

    #[test]
    fn rename_dotted_import() {
        assert_rename(
            &[
                ("pkg/__init__.py", ""),
                ("pkg/old_sub.py", "x = 1\n"),
                ("pkg/other.py", "y = 1\n"),
                (
                    "consumer.py",
                    "import pkg.old_sub\nimport pkg.other\nprint(pkg.old_sub.x, pkg.other.y)\n",
                ),
            ],
            "pkg/old_sub.py",
            "pkg/new_sub.py",
            "consumer.py",
            "import pkg.new_sub\nimport pkg.other\nprint(pkg.new_sub.x, pkg.other.y)\n",
        );
    }

    #[test]
    fn rename_cross_directory() {
        assert_rename(
            &[
                ("/old_package/__init__.py", ""),
                ("/old_package/old_module.py", "x = 1\n"),
                ("/new_package/__init__.py", ""),
                (
                    "/consumer.py",
                    "import old_package.old_module\nprint(old_package.old_module.x)\n",
                ),
            ],
            "/old_package/old_module.py",
            "/new_package/new_module.py",
            "/consumer.py",
            "import new_package.new_module\nprint(new_package.new_module.x)\n",
        );
    }

    #[test]
    fn cross_package_access_through_parent_alias_is_out_of_scope() {
        assert_unsupported(
            &[
                ("/old_package/__init__.py", ""),
                ("/old_package/old_module.py", "x = 1\n"),
                ("/new_package/__init__.py", ""),
                (
                    "/consumer.py",
                    "import old_package\nimport old_package.old_module as moved\nprint(old_package.old_module.x, moved.x)\n",
                ),
            ],
            "/old_package/old_module.py",
            "/new_package/new_module.py",
        );
    }

    #[test]
    fn rename_cross_directory_standalone_import() {
        assert_rename(
            &[
                ("/old_package/__init__.py", ""),
                ("/old_package/old_module.py", "x = 1\n"),
                ("/new_package/__init__.py", ""),
                (
                    "/consumer.py",
                    "from old_package import old_module\nprint(old_module.x)\n",
                ),
            ],
            "/old_package/old_module.py",
            "/new_package/new_module.py",
            "/consumer.py",
            "from new_package import new_module\nprint(new_module.x)\n",
        );
    }

    #[test]
    fn rename_cross_directory_rewrites_relative_import_in_moved_file() {
        assert_rename(
            &[
                ("/old_package/__init__.py", ""),
                ("/old_package/helper.py", "x = 1\n"),
                ("/old_package/moved.py", "from . import helper\n"),
                ("/new_package/__init__.py", ""),
            ],
            "/old_package/moved.py",
            "/new_package/moved.py",
            "/old_package/moved.py",
            "from old_package import helper\n",
        );
    }

    #[test]
    fn rename_cross_directory_import_with_sibling_is_conservative() {
        assert_unsupported(
            &[
                ("/old_package/__init__.py", ""),
                ("/old_package/old_module.py", ""),
                ("/old_package/other.py", ""),
                ("/new_package/__init__.py", ""),
                (
                    "/consumer.py",
                    "from old_package import old_module, other\n",
                ),
            ],
            "/old_package/old_module.py",
            "/new_package/new_module.py",
        );
    }

    #[test]
    fn rename_top_level_module_into_package() {
        assert_rename(
            &[
                ("/old.py", "x = 1\n"),
                ("/pkg/__init__.py", ""),
                ("/consumer.py", "import old\nprint(old.x)\n"),
            ],
            "/old.py",
            "/pkg/new.py",
            "/consumer.py",
            "import pkg.new\nprint(pkg.new.x)\n",
        );
    }

    #[test]
    fn parent_import_to_top_level_is_out_of_scope() {
        assert_unsupported(
            &[
                ("/pkg/__init__.py", ""),
                ("/pkg/old.py", "x = 1\n"),
                (
                    "/consumer.py",
                    "from pkg import (\n    old,  # keep this comment\n)\nprint(old.x)\n",
                ),
            ],
            "/pkg/old.py",
            "/new.py",
        );
    }

    #[test]
    fn rename_updates_references_in_excluded_anchor_file() {
        let mut db = create_test_db(&[
            ("/old_module.py", "import old_module\n"),
            ("/consumer.py", ""),
        ]);
        let project = db.project();
        project.set_included_paths(&mut db, vec!["/consumer.py".into()]);
        let old_module = system_path_to_file(&db, "/old_module.py").unwrap();
        assert!(!project.files(&db).contains(&old_module));

        let edits = will_rename_file(
            &db,
            SystemPath::new("/old_module.py"),
            SystemPath::new("/new_module.py"),
        );

        let result = apply_edits(&db, &edits, old_module);
        assert_eq!(result, "import new_module\n");
    }

    #[test]
    fn unsupported_module_paths_are_out_of_scope() {
        // Moving a package initializer changes the package itself.
        assert_unsupported(
            &[
                ("pkg/__init__.py", "x = 1\n"),
                ("consumer.py", "import pkg\n"),
            ],
            "pkg/__init__.py",
            "pkg/new.py",
        );
        assert_unsupported(
            &[
                ("old_module.py", "x = 1\n"),
                ("consumer.py", "import old_module\nprint(old_module.x)\n"),
            ],
            "old_module.py",
            "_abc.py",
        );
        assert_unsupported(
            &[
                ("old_module.py", "x = 1\n"),
                ("consumer.py", "import old_module\n"),
            ],
            "old_module.py",
            "new_module.txt",
        );
        // Python normalizes identifiers, but the replacement must preserve its spelling.
        assert_unsupported(
            &[
                ("old_module.py", "x = 1\n"),
                ("consumer.py", "import old_module\n"),
            ],
            "old_module.py",
            "\u{212a}.py",
        );
        assert_unsupported(
            &[
                ("old_module.py", "x = 1\n"),
                ("consumer.py", "import old_module\n"),
            ],
            "old_module.py",
            "__debug__.py",
        );
    }

    #[test]
    fn rename_shadowed_module_not_rewritten() {
        assert_rename(
            &[
                ("pkg/__init__.py", ""),
                ("pkg/foo.py", "x = 1\n"),
                (
                    "consumer.py",
                    "from pkg import foo\n\ndef f(pkg):\n    return pkg.foo\n",
                ),
            ],
            "pkg/foo.py",
            "pkg/bar.py",
            "consumer.py",
            "from pkg import bar\n\ndef f(pkg):\n    return pkg.foo\n",
        );
    }

    #[test]
    fn mixed_package_roots_are_out_of_scope() {
        assert_unsupported(
            &[
                ("/pkg/__init__.py", ""),
                ("/pkg/old.py", "x = 1\n"),
                ("/other_pkg/__init__.py", ""),
                ("/other_pkg/old.py", "x = 2\n"),
                (
                    "/consumer.py",
                    "def f(flag: bool):\n    import pkg.old\n    import other_pkg\n    if flag:\n        pkg = other_pkg\n    return pkg.old.x\n",
                ),
            ],
            "/pkg/old.py",
            "/pkg/new.py",
        );
    }

    #[test]
    fn module_reexports_and_ambiguous_submodule_imports_are_out_of_scope() {
        assert_unsupported(
            &[
                ("old_module.py", "x = 1\n"),
                ("pkg/__init__.py", "import old_module as old_module\n"),
                ("consumer.py", "import pkg\nprint(pkg.old_module.x)\n"),
            ],
            "old_module.py",
            "new_module.py",
        );
        assert_unsupported(
            &[
                ("/pkg/__init__.py", "from . import old\n"),
                ("/pkg/old.py", "x = 1\n"),
                ("/consumer.py", "from pkg import *\nprint(old.x)\n"),
            ],
            "/pkg/old.py",
            "/pkg/new.py",
        );
    }

    #[test]
    fn rename_pyi_file_and_paired_batch() {
        assert_rename(
            &[
                ("old_module.pyi", "x: int\n"),
                ("consumer.py", "import old_module\nprint(old_module.x)\n"),
            ],
            "old_module.pyi",
            "new_module.pyi",
            "consumer.py",
            "import new_module\nprint(new_module.x)\n",
        );

        let db = create_test_db(&[
            ("old_module.py", "x = 1\n"),
            ("old_module.pyi", "x: int\n"),
            ("consumer.py", "import old_module\nprint(old_module.x)\n"),
        ]);

        let edits = will_rename_paths(
            &db,
            &[
                PathRename::file("old_module.py".into(), "new_module.py".into()),
                PathRename::file("old_module.pyi".into(), "new_module.pyi".into()),
            ],
        )
        .expect("coordinated source and stub move to be supported");

        let consumer = system_path_to_file(&db, "consumer.py").unwrap();
        assert_eq!(edits.iter().filter(|edit| edit.file == consumer).count(), 2);
        let result = apply_edits(&db, &edits, consumer);
        assert_eq!(result, "import new_module\nprint(new_module.x)\n");
    }

    #[test]
    fn unrelated_file_and_directory_batches_are_out_of_scope() {
        let db = create_test_db(&[
            ("pkg/__init__.py", ""),
            ("pkg/a.py", ""),
            ("pkg/b.py", ""),
            ("x/__init__.py", ""),
            ("y/__init__.py", ""),
            ("consumer.py", "from pkg import a, b\n"),
        ]);

        let edits = will_rename_paths(
            &db,
            &[
                PathRename::file("pkg/a.py".into(), "x/a.py".into()),
                PathRename::file("pkg/b.py".into(), "y/b.py".into()),
            ],
        );

        assert!(edits.is_err());

        let db = create_test_db(&[
            ("/old_pkg/__init__.py", "x = 1\n"),
            ("/consumer.py", "from old_pkg import x\n"),
        ]);
        let edits = will_rename_paths(
            &db,
            &[PathRename::file(
                SystemPath::new("/old_pkg").to_path_buf(),
                SystemPath::new("/new_pkg").to_path_buf(),
            )],
        );
        assert!(edits.is_err());
    }

    #[test]
    fn paired_source_and_stub_must_move_together() {
        let db = create_test_db(&[
            ("old_module.py", "x = 1\n"),
            ("old_module.pyi", "x: int\n"),
            ("consumer.py", "import old_module\nprint(old_module.x)\n"),
        ]);

        let edits = will_rename_paths(
            &db,
            &[
                PathRename::file("old_module.py".into(), "first.py".into()),
                PathRename::file("old_module.pyi".into(), "second.pyi".into()),
            ],
        );

        assert!(edits.is_err());
        assert_unsupported(
            &[
                ("old_module.py", "x = 1\n"),
                ("old_module.pyi", "x: int\n"),
                ("consumer.py", "import old_module\n"),
            ],
            "old_module.pyi",
            "new_module.pyi",
        );

        let mut db = create_test_db(&[
            ("/stubs/old_module.pyi", "x: int\n"),
            ("/runtime/old_module.py", "x = 1\n"),
            ("/project/consumer.py", "import old_module\n"),
        ]);
        configure_search_paths_with_src_roots(
            &mut db,
            vec!["/project".into()],
            vec!["/stubs".into(), "/runtime".into()],
        );

        assert_unsupported_in_db(&db, "/stubs/old_module.pyi", "/stubs/new_module.pyi");
    }

    #[test]
    fn optional_import_is_unsupported_instead_of_introducing_alias() {
        assert_unsupported(
            &[
                ("old_module.py", "x = 1\n"),
                (
                    "consumer.py",
                    "try:\n    import old_module\nexcept ImportError:\n    old_module = None\nprint(old_module)\n",
                ),
            ],
            "old_module.py",
            "new_module.py",
        );
    }

    #[test]
    fn binding_collision_is_unsupported_instead_of_introducing_alias() {
        for consumer in [
            "import old_module\nnew_module = 1\nprint(old_module.x, new_module)\n",
            "import old_module\ndef f(new_module):\n    return old_module.x\n",
            "import old_module\ndef f():\n    import sys as new_module\n    return old_module.x\n",
        ] {
            assert_unsupported(
                &[("old_module.py", "x = 1\n"), ("consumer.py", consumer)],
                "old_module.py",
                "new_module.py",
            );
        }
    }

    #[test]
    fn builtin_collision_is_unsupported_instead_of_introducing_alias() {
        assert_unsupported(
            &[
                ("old_module.py", "x = 1\n"),
                (
                    "consumer.py",
                    "import old_module\nprint(list(), old_module.x)\n",
                ),
            ],
            "old_module.py",
            "list.py",
        );
    }

    #[test]
    fn global_declaration_is_unsupported() {
        assert_unsupported(
            &[
                ("old_module.py", "x = 1\n"),
                (
                    "consumer.py",
                    "import old_module\n\ndef f():\n    global old_module\n    return old_module.x\n",
                ),
            ],
            "old_module.py",
            "new_module.py",
        );
    }

    #[test]
    fn rename_del_target() {
        assert_rename(
            &[
                ("old_module.py", "x = 1\n"),
                ("consumer.py", "import old_module\ndel old_module\n"),
            ],
            "old_module.py",
            "new_module.py",
            "consumer.py",
            "import new_module\ndel new_module\n",
        );
    }

    #[test]
    fn unsupported_consumer_aborts_entire_workspace_edit() {
        assert_unsupported(
            &[
                ("pkg/__init__.py", ""),
                ("pkg/old.py", "x = 1\n"),
                ("safe.py", "import pkg.old\nprint(pkg.old.x)\n"),
                ("unsafe.py", "import pkg.old\npkg.old = None\n"),
            ],
            "pkg/old.py",
            "pkg/new.py",
        );
        assert_unsupported(
            &[
                ("pkg/__init__.py", ""),
                ("pkg/old.py", "x = 1\n"),
                (
                    "consumer.py",
                    "import pkg.old\npkg.new = object()\nprint(pkg.old.x)\n",
                ),
            ],
            "pkg/old.py",
            "pkg/new.py",
        );
    }

    #[test]
    fn unreadable_candidate_aborts_entire_workspace_edit() {
        let db = create_test_db(&[
            ("old_module.py", "x = 1\n"),
            ("consumer.py", "import old_module\nprint(old_module.x)\n"),
            ("unreadable.py", ""),
        ]);
        db.test_system()
            .memory_file_system()
            .write_file("unreadable.py", b"\xff")
            .unwrap();

        assert_unsupported_in_db(&db, "old_module.py", "new_module.py");
    }

    #[test]
    fn independent_old_package_use_is_unsupported_instead_of_adding_import() {
        assert_unsupported(
            &[
                ("/old_package/__init__.py", "value = 1\n"),
                ("/old_package/old_module.py", "x = 1\n"),
                ("/new_package/__init__.py", ""),
                (
                    "/consumer.py",
                    "import old_package.old_module\nprint(old_package.value, old_package.old_module.x)\n",
                ),
            ],
            "/old_package/old_module.py",
            "/new_package/new_module.py",
        );
    }

    #[test]
    fn compatible_destination_package_binding_is_reused() {
        assert_rename(
            &[
                ("/old_pkg/__init__.py", ""),
                ("/old_pkg/moved.py", "value = 1\n"),
                ("/new_pkg/__init__.py", ""),
                ("/new_pkg/other.py", "value = 2\n"),
                (
                    "/consumer.py",
                    "import new_pkg.other\nimport old_pkg.moved\n",
                ),
            ],
            "/old_pkg/moved.py",
            "/new_pkg/new.py",
            "/consumer.py",
            "import new_pkg.other\nimport new_pkg.new\n",
        );
    }

    #[test]
    fn cross_directory_move_uses_destination_search_path() {
        let mut db = create_test_db(&[
            ("/high/old.py", "x = 1\n"),
            ("/low/helper.py", ""),
            ("/project/consumer.py", "import old\nprint(old.x)\n"),
        ]);
        configure_search_paths_with_src_roots(
            &mut db,
            vec!["/project".into()],
            vec!["/high".into(), "/low".into()],
        );

        assert_rename_in_db(
            &db,
            "/high/old.py",
            "/low/new.py",
            "/project/consumer.py",
            "import new\nprint(new.x)\n",
        );
        assert_unsupported_in_db(&db, "/high/old.py", "/low/old.py");
    }

    #[test]
    fn multiply_importable_source_is_out_of_scope() {
        let mut db = create_test_db(&[
            ("/pkg/old.py", "x = 1\n"),
            ("/consumer.py", "import old\nprint(old.x)\n"),
        ]);
        configure_search_paths(&mut db, vec!["/pkg".into()]);

        assert_unsupported_in_db(&db, "/pkg/old.py", "/pkg/new.py");
    }

    #[test]
    fn multiply_importable_destination_is_out_of_scope() {
        let mut db = create_test_db(&[
            ("/old.py", "x = 1\n"),
            ("/pkg/helper.py", ""),
            ("/consumer.py", "import old\nprint(old.x)\n"),
        ]);
        configure_search_paths(&mut db, vec!["/pkg".into()]);

        assert_unsupported_in_db(&db, "/old.py", "/pkg/new.py");
    }

    #[test]
    fn destination_shadowing_is_out_of_scope() {
        assert_unsupported(
            &[("/old.py", ""), ("/pkg.py", "")],
            "/old.py",
            "/pkg/new.py",
        );

        let mut db = create_test_db(&[("/old.py", ""), ("/extra/new.py", "")]);
        configure_search_paths(&mut db, vec!["/extra".into()]);
        assert_unsupported_in_db(&db, "/old.py", "/new.py");
    }

    #[test]
    fn destination_package_member_collision_is_out_of_scope() {
        assert_unsupported(
            &[
                ("/pkg/__init__.py", "new = 1\n"),
                ("/pkg/old.py", "x = 1\n"),
                (
                    "/consumer.py",
                    "import pkg.old\nprint(pkg.old.x, pkg.new)\n",
                ),
            ],
            "/pkg/old.py",
            "/pkg/new.py",
        );
    }

    #[test]
    fn stdlib_search_paths_are_out_of_scope() {
        let mut db = create_test_db(&[
            ("/src/old.pyi", "x: int\n"),
            ("/src/consumer.py", "import old\nprint(old.x)\n"),
            ("/src/typeshed/stdlib/VERSIONS", "new: 3.8-\n"),
        ]);
        let mut settings = SearchPathSettings::new(vec!["/src".into()]);
        settings.custom_typeshed = Some("/src/typeshed".into());
        configure_search_path_settings(&mut db, &settings);

        assert_unsupported_in_db(&db, "/src/old.pyi", "/src/typeshed/stdlib/new.pyi");
    }

    fn will_rename_file(
        db: &dyn Db,
        old_path: &SystemPath,
        new_path: &SystemPath,
    ) -> Vec<FileRenameEdit> {
        try_will_rename_file(db, old_path, new_path).expect("module move to be supported")
    }

    fn try_will_rename_file(
        db: &dyn Db,
        old_path: &SystemPath,
        new_path: &SystemPath,
    ) -> Result<Vec<FileRenameEdit>, UnsupportedFileRename> {
        let rename = PathRename::file(old_path.to_path_buf(), new_path.to_path_buf());
        will_rename_paths(db, &[rename])
    }

    fn assert_unsupported(files: &[(&str, &str)], old_path: &str, new_path: &str) {
        let db = create_test_db(files);
        assert_unsupported_in_db(&db, old_path, new_path);
    }

    fn assert_unsupported_in_db(db: &dyn Db, old_path: &str, new_path: &str) {
        assert_eq!(
            try_will_rename_file(db, SystemPath::new(old_path), SystemPath::new(new_path)),
            Err(UnsupportedFileRename)
        );
    }

    fn assert_rename(
        files: &[(&str, &str)],
        old_path: &str,
        new_path: &str,
        target: &str,
        expected: &str,
    ) {
        let db = create_test_db(files);
        assert_rename_in_db(&db, old_path, new_path, target, expected);
    }

    fn assert_rename_in_db(
        db: &dyn Db,
        old_path: &str,
        new_path: &str,
        target: &str,
        expected: &str,
    ) {
        let edits = will_rename_file(db, SystemPath::new(old_path), SystemPath::new(new_path));
        let target = system_path_to_file(db, target).unwrap();
        assert_eq!(apply_edits(db, &edits, target), expected);
    }

    fn create_test_db(files: &[(&str, &str)]) -> TestDb {
        let mut db = TestDb::new(ProjectMetadata::new("test".into(), "/".into()));

        db.init_program_with_python_version(PythonVersion::latest_ty())
            .unwrap();

        for &(path, contents) in files {
            db.write_file(path, contents)
                .expect("write to memory file system to be successful");
        }

        db
    }

    fn configure_search_paths(db: &mut TestDb, extra_paths: Vec<SystemPathBuf>) {
        let root = db.project().root(db).to_path_buf();
        configure_search_paths_with_src_roots(db, vec![root], extra_paths);
    }

    fn configure_search_paths_with_src_roots(
        db: &mut TestDb,
        src_roots: Vec<SystemPathBuf>,
        extra_paths: Vec<SystemPathBuf>,
    ) {
        let mut settings = SearchPathSettings::new(src_roots);
        settings.extra_paths = extra_paths;
        configure_search_path_settings(db, &settings);
    }

    fn configure_search_path_settings(db: &mut TestDb, settings: &SearchPathSettings) {
        let search_paths = settings
            .to_search_paths(db.system(), db.vendored(), &FallibleStrategy)
            .expect("valid search paths");
        Program::init_or_update(
            db,
            ProgramSettings {
                python_version: PythonVersionWithSource::default(),
                python_platform: PythonPlatform::default(),
                search_paths,
            },
        );
    }

    fn apply_edits(db: &dyn Db, edits: &[FileRenameEdit], file: File) -> String {
        let mut sorted_edits: Vec<_> = edits.iter().filter(|e| e.file == file).collect();
        sorted_edits.sort_by_key(|b| std::cmp::Reverse(b.range.start()));

        let mut result = source_text(db, file).as_str().to_owned();
        for edit in sorted_edits {
            let start = usize::from(edit.range.start());
            let end = usize::from(edit.range.end());
            result.replace_range(start..end, &edit.new_text);
        }
        result
    }
}
