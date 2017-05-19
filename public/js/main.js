'use_strict';

// Globals
var source_number = 1;
var pane_number = 1

function Pane () {
  this.editor = null;
  this.tab = null;
  this.values = {};
}

function create_editor (elem) {
  var div = $(elem).find('.editor')[0];
  elem.pane.editor = CodeMirror (div, {
    mode: 'text/x-csrc',
    styleActiveLine: true,
    lineNumbers: true,
    matchBrackets: true,
    tabSize: 2,
    smartIndent: true
  });
  elem.pane.editor.on('change', () => {
    elem.pane.values[elem.pane.tab] = elem.pane.editor.getValue();
  });
}

function clear_tab_selection (pane) {
  $(pane).find('.tablinks').removeClass('active');
}

function change_tab (e, $tab, tabname) {
  e.pane.tab = tabname;
  refresh_pane(e.pane);
  clear_tab_selection (e);
  $tab.addClass('active');
}

function create_tab (e, name, value) {
  if (!name) {
    name = 'Source #' + source_number;
    source_number++;
  }

  if (Object.keys(e.pane.values).length === 0) {
    $(e).find('.editor').show();
  }
  clear_tab_selection(e);

  e.pane.tab = name;
  e.pane.values[name] = value ? value : '';


  var $new_tab = $('#tablink-template').clone().contents();
  $new_tab.find('.title').text(name);
  $new_tab.find('.title').on('click', () => {
    change_tab (e, $new_tab, name);
  });
  $new_tab.find('.close').on('click', () => {
    if (e.pane.tab === name) {
      if (Object.keys(e.pane.values).length === 1) {
        $(e).find('.editor').hide();
      } else {
        var prev_tab = $new_tab.prev()[0];
        var prev_tab_name = $(prev_tab).find('.title')[0].textContent;
        change_tab(e, $(prev_tab), prev_tab_name);
      }
    }
    delete e.pane.values[name];
    $new_tab.remove();
  });
  $(e).find('.tabadder').before($new_tab);
  refresh_pane(e.pane);
}


function refresh_pane(pane) {
  pane.editor.setValue(pane.values[pane.tab]);
  pane.editor.refresh();
}

function create_panes_from_template(e) {
  $('#pane-template').clone().contents().appendTo(e);
  e.pane = new Pane();
  create_editor(e);
  create_tab(e, null, 'int main() {return 0;}');
}

function init_panes() {
  var ps = $('.pane').toArray();
  var w = window.innerWidth/ps.length + 'px';
  for (i = 0; i < ps.length - 1; i++) {
    ps[i].style.width = w;
  }
  ps[ps.length-1].style.flex = '1 1 auto';
}

function resize_panes() {
  var ps = $('.pane').toArray();
  var n = ps.length;
  var factor = window.innerWidth / window.prevWidth;
  for (i = 0; i < n - 1; i++) {
    var w = parseFloat(ps[i].style.width.slice(0, -2));
    ps[i].style.width = (w * factor)+'px';
  }
  ps[n-1].style.flex = '1 1 auto';
  window.prevWidth = window.innerWidth;
}

// HTML Event handlers

function new_tab (evt) {
  create_tab(evt.srcElement.parentNode);
}

// Resize events

var startX, paneWidth, paneSep;
window.prevWidth = window.innerWidth;

function init_resize(evt) {
  paneSep = evt.srcElement;
  paneSep.className += ' resize';
  startX = evt.clientX;
  $('div').each((i, e) => {
    e.style.pointerEvents = 'none';
  });
  var pane = $(paneSep).prev()[0];
  paneWidth = parseFloat(pane.style.width.slice(0, -2));
  document.documentElement.addEventListener('mousemove', do_resize, false);
  document.documentElement.addEventListener('mouseup', stop_resize, false);
}

function do_resize(evt) {
  var delta = evt.clientX - startX;
  var pane = $(paneSep).prev()[0];
  pane.style.width = (paneWidth+delta)+'px';
  console.log (evt.clientX - startX);
}

function stop_resize(evt) {
  paneSep.className = paneSep.className.replace(' resize', '');
  $('div').each((i, e) => {
    e.style.pointerEvents = '';
  });
  document.documentElement.removeEventListener('mousemove', do_resize, false);
  document.documentElement.removeEventListener('mouseup', stop_resize, false);
}

window.onresize = ((evt) => {
  resize_panes();
});

// Initializations

function setup() {
  $('.pane').each((i,e) => {
    create_panes_from_template (e);
  });

  init_panes();

  $('.pane-separator').each((i, e) => {
    e.addEventListener('mousedown', init_resize, false);
  });
}

setup();
