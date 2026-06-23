use std::collections::HashMap;

use lsp_types::{RenameFilesParams, TextEdit, Uri, WillRenameFilesRequest, WorkspaceEdit};
use ruff_db::files::File;
use ruff_db::system::SystemPathBuf;
use ty_ide::{PathRename, will_rename_paths_in_files};
use ty_project::{Db as _, ProjectDatabase};

use crate::document::ToRangeExt;
use crate::server::api::traits::{
    BackgroundRequestHandler, RequestHandler, RetriableRequestHandler,
};
use crate::session::SessionSnapshot;
use crate::session::client::Client;

pub(crate) struct WillRenameFilesHandler;

impl RequestHandler for WillRenameFilesHandler {
    type RequestType = WillRenameFilesRequest;
}

impl BackgroundRequestHandler for WillRenameFilesHandler {
    fn run(
        snapshot: &SessionSnapshot,
        client: &Client,
        params: RenameFilesParams,
    ) -> crate::server::Result<Option<WorkspaceEdit>> {
        let encoding = snapshot.position_encoding();
        let mut all_changes: HashMap<Uri, Vec<TextEdit>> = HashMap::new();
        let mut renames = Vec::new();
        let mut project_index = None;

        for file_rename in &params.files {
            let (Some(old_path), Some(new_path)) = (
                file_uri_to_path(&file_rename.old_uri),
                file_uri_to_path(&file_rename.new_uri),
            ) else {
                return Ok(None);
            };

            if !matches!(old_path.extension(), Some("py" | "pyi")) {
                return Ok(None);
            }
            if old_path.extension() != new_path.extension() {
                return Ok(unsupported_move(client));
            }
            let Some(rename_project_index) = snapshot.project_index_for_path(&old_path) else {
                return Ok(None);
            };
            if snapshot
                .enclosing_project_index_for_path(&new_path)
                .is_some_and(|index| index != rename_project_index)
            {
                return Ok(unsupported_move(client));
            }
            if project_index
                .replace(rename_project_index)
                .is_some_and(|project_index| project_index != rename_project_index)
            {
                return Ok(unsupported_move(client));
            }
            renames.push(PathRename::file(old_path, new_path));
        }

        // File moves are evaluated in the project that owns the old path. Consumers in other
        // workspaces are intentionally left unchanged, even when they can import through an extra
        // search path; coordinating edits across independently configured projects is out of scope.
        let Some(project_index) = project_index else {
            return Ok(None);
        };
        let Some(db) = snapshot.projects().get(project_index) else {
            return Ok(None);
        };
        let Some(workspace_settings) = snapshot.workspace_settings(project_index) else {
            return Ok(None);
        };
        if workspace_settings.is_language_services_disabled() {
            return Ok(None);
        }

        let project = db.project();
        let indexed_files = project.files(db);
        let open_files = project.open_files(db);
        let files = (&indexed_files)
            .into_iter()
            .chain(open_files.iter().copied())
            .filter(|file| file_is_in_rename_scope(snapshot, db, project_index, *file));

        let Ok(edits) = will_rename_paths_in_files(db, &renames, files) else {
            return Ok(unsupported_move(client));
        };
        for edit in edits {
            let (file, range, new_text) = edit.into_parts();
            if !file_is_in_rename_scope(snapshot, db, project_index, file) {
                continue;
            }
            let Some(range) = range.to_lsp_range(db, file, encoding) else {
                return Ok(unsupported_move(client));
            };
            let Some(location) = range.into_location() else {
                return Ok(unsupported_move(client));
            };

            all_changes.entry(location.uri).or_default().push(TextEdit {
                range: location.range,
                new_text,
            });
        }

        if all_changes.values_mut().any(|edits| {
            edits.sort_by_key(|edit| (edit.range.start, edit.range.end));
            edits.dedup();
            edits.windows(2).any(|edits| {
                edits[0].range.start == edits[1].range.start
                    || edits[0].range.end > edits[1].range.start
            })
        }) {
            return Ok(unsupported_move(client));
        }

        if all_changes.is_empty() {
            Ok(None)
        } else {
            Ok(Some(WorkspaceEdit {
                changes: Some(all_changes),
                ..Default::default()
            }))
        }
    }
}

impl RetriableRequestHandler for WillRenameFilesHandler {
    const RETRY_ON_CANCELLATION: bool = true;
}

fn file_uri_to_path(uri: &str) -> Option<SystemPathBuf> {
    let uri = Uri::parse(uri).ok()?;
    SystemPathBuf::from_path_buf(uri.to_file_path().ok()?).ok()
}

fn file_is_in_rename_scope(
    snapshot: &SessionSnapshot,
    db: &ProjectDatabase,
    project_index: usize,
    file: File,
) -> bool {
    file.path(db).as_system_path().is_none_or(|path| {
        snapshot
            .enclosing_project_index_for_path(path)
            .is_none_or(|index| index == project_index)
    })
}

fn unsupported_move(client: &Client) -> Option<WorkspaceEdit> {
    client.show_warning_message(
        "ty could not safely update imports and references for this file move. \
         No automated code changes were applied.",
    );
    None
}
