use crate::notebook::NotebookBuilder;
use crate::{TestServer, TestServerBuilder};
use lsp_types::{
    DidOpenTextDocumentNotification, DidOpenTextDocumentParams, FileRename, LanguageKind,
    MessageType, Position, Range, ShowMessageNotification, TextDocumentItem, TextEdit, Uri,
    WorkspaceEdit,
};
use ruff_db::system::SystemPath;
use std::collections::HashMap;
use std::time::Duration;

#[test]
fn simple_rename() -> anyhow::Result<()> {
    let mut server = TestServerBuilder::new()?
        .with_file("old_module.py", "")?
        .with_file("consumer.py", "")?
        .build()
        .wait_until_workspaces_are_initialized();

    server.open_text_document("old_module.py", "x = 1\n", 1);
    server.open_text_document("consumer.py", "import old_module\nprint(old_module.x)\n", 1);

    let mut changes = rename_changes(&mut server, "old_module.py", "new_module.py");
    assert_module_edits(
        &changes
            .remove(&server.file_uri("consumer.py"))
            .expect("changes to target the consumer"),
    );
    assert!(changes.is_empty());

    Ok(())
}

#[test]
fn notebook_cell() -> anyhow::Result<()> {
    let mut server = TestServerBuilder::new()?
        .with_file("old_module.py", "x = 1\n")?
        .build()
        .wait_until_workspaces_are_initialized();

    let mut notebook = NotebookBuilder::virtual_file("consumer.ipynb");
    let cell_uri = notebook.add_python_cell("import old_module\nprint(old_module.x)\n");
    notebook.open(&mut server);
    server.collect_publish_diagnostic_notifications(1);

    let mut changes = rename_changes(&mut server, "old_module.py", "new_module.py");
    assert_module_edits(
        &changes
            .remove(&cell_uri)
            .expect("changes to target the notebook cell"),
    );
    assert!(changes.is_empty());

    Ok(())
}

#[test]
fn untitled_document() -> anyhow::Result<()> {
    let mut server = TestServerBuilder::new()?
        .with_file("old_module.py", "x = 1\n")?
        .build()
        .wait_until_workspaces_are_initialized();

    let file_uri = server.file_uri("consumer.py");
    let virtual_uri = Uri::parse(&format!("untitled://{}", file_uri.path())).unwrap();
    server.send_notification::<DidOpenTextDocumentNotification>(DidOpenTextDocumentParams {
        text_document: TextDocumentItem {
            uri: virtual_uri.clone(),
            language_id: LanguageKind::Python,
            version: 1,
            text: "import old_module\nprint(old_module.x)\n".to_string(),
        },
    });

    let mut changes = rename_changes(&mut server, "old_module.py", "new_module.py");
    let edits = changes
        .remove(&virtual_uri)
        .expect("changes to target the untitled document");
    assert!(changes.is_empty());

    assert_module_edits(&edits);

    Ok(())
}

#[test]
fn unsupported_foreign_consumer_does_not_cancel_owned_edits() -> anyhow::Result<()> {
    let workspace_a = SystemPath::new("repo/a");
    let workspace_b = SystemPath::new("repo/b");
    let mut server = TestServerBuilder::new()?
        .with_file("repo/pyproject.toml", "[tool.ty]\n")?
        .with_workspace(workspace_a, None)?
        .with_file("repo/a/foo/__init__.py", "")?
        .with_file("repo/a/foo/foo.py", "x = 1\n")?
        .with_file("repo/a/foo/other.py", "")?
        .with_file("repo/a/bar/__init__.py", "")?
        .with_file(
            "repo/a/consumer.py",
            "from a.foo import foo\nprint(foo.x)\n",
        )?
        .with_workspace(workspace_b, None)?
        .with_file(
            "repo/b/consumer.py",
            "from a.foo import foo, other\nprint(foo.x)\n",
        )?
        .build()
        .wait_until_workspaces_are_initialized();

    let mut changes = rename_changes(&mut server, "repo/a/foo/foo.py", "repo/a/bar/new.py");
    let edits = changes
        .remove(&server.file_uri("repo/a/consumer.py"))
        .expect("changes to target the owning workspace");

    assert_eq!(
        edits
            .iter()
            .map(|edit| edit.new_text.as_str())
            .collect::<Vec<_>>(),
        ["a.bar", "new", "new"]
    );
    assert!(changes.is_empty());

    Ok(())
}

#[test]
fn unsupported_move_warns_without_consumers() -> anyhow::Result<()> {
    let mut server = TestServerBuilder::new()?
        .with_file("old_module.py", "x = 1\n")?
        .with_file("old_module.pyi", "x: int\n")?
        .build()
        .wait_until_workspaces_are_initialized();

    let edits = request_rename(&mut server, "old_module.pyi", "new_module.pyi");

    assert!(edits.is_none());
    let warning = server.await_notification::<ShowMessageNotification>();
    assert_eq!(warning.kind, MessageType::Warning);
    assert_eq!(
        warning.message,
        "ty could not safely update imports and references for this file move. \
         No automated code changes were applied."
    );

    Ok(())
}

#[test]
fn safe_move_without_consumers_is_silent() -> anyhow::Result<()> {
    let mut server = TestServerBuilder::new()?
        .with_file("old_module.py", "x = 1\n")?
        .build()
        .wait_until_workspaces_are_initialized();

    let edits = request_rename(&mut server, "old_module.py", "new_module.py");

    assert!(edits.is_none());
    assert!(
        server
            .try_await_notification::<ShowMessageNotification>(Some(Duration::from_millis(100)))
            .is_err()
    );

    Ok(())
}

fn assert_module_edits(edits: &[TextEdit]) {
    assert_eq!(
        edits,
        [
            TextEdit::new(
                Range::new(Position::new(0, 7), Position::new(0, 17)),
                "new_module".to_string(),
            ),
            TextEdit::new(
                Range::new(Position::new(1, 6), Position::new(1, 16)),
                "new_module".to_string(),
            ),
        ]
    );
}

fn request_rename(server: &mut TestServer, old: &str, new: &str) -> Option<WorkspaceEdit> {
    server.will_rename_files(vec![FileRename {
        old_uri: server.file_uri(old).to_string(),
        new_uri: server.file_uri(new).to_string(),
    }])
}

fn rename_changes(server: &mut TestServer, old: &str, new: &str) -> HashMap<Uri, Vec<TextEdit>> {
    request_rename(server, old, new)
        .and_then(|edit| edit.changes)
        .expect("rename to produce workspace changes")
}
