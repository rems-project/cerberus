// Monaco editor configuration

require.config({ paths: { 'vs': 'node_modules/monaco-editor/dev/vs' }});
require(['vs/editor/editor.main'], () => {
  var editorC = monaco.editor.create(document.getElementById('editor-c'));
  var modelC = monaco.editor.createModel (
    cerberus.buffer().toString(), 'c'
  );
  modelC.onDidChangeContent((e) => {
    // TODO: this is very ugly, i don't know what to do!!!
    var content = cerberus.buffer();
    content.c = editorC.getValue();
    content.l = content.c.length;
    cerberus.update(content);
  });
  editorC.setModel(modelC);

  var editorCore = monaco.editor.create(document.getElementById('editor-core'));
  editorCore.setModel(monaco.editor.createModel('', 'fsharp'));
  //cerberus.output ((s) => { editorCore.setValue (s); });

  var log = monaco.editor.create(document.getElementById('log'));
  log.setModel(monaco.editor.createModel('', 'c'));
  cerberus.log ((s) => { log.setValue (log.getValue() + s); });
});

