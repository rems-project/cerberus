'use_strict';

// Globals
var source_counter = 1;

// Types
function Pane (div) {
  this.editor = CodeMirror ($(div).find('.editor')[0], {
    mode: 'text/x-csrc',
    styleActiveLine: true,
    lineNumbers: true,
    matchBrackets: true,
    tabSize: 2,
    smartIndent: true
  });

  this.tab = null;    // Current tab
  this.values = {};   // Values/Buffer being edited
  this.div = div;     // Pointer to UI

  // Add event listeners
  $(this.div).find('.tabadder').on('click', () => this.create_tab ());

  this.number_of_tabs = function () {
    return Object.keys(this.values).length;
  }

  this.set_value = function (value) {
    this.values[this.tab] = value;
    this.refresh();
  }

  this.save_editor_value = function () {
    this.values[this.tab] = this.editor.getValue();
  }

  this.create_tab = function (name, value) {
    if (!name) {
      name = 'Source #' + source_counter;
      source_counter++;
    }
    this.tab = name;
    this.values[name] = value ? value : '';

    if (this.number_of_tabs() === 1) {
      $(this.div).find('.editor').show();
    }
    this.clear_tab_selection();

    var $tab = $('#tablink-template').clone().contents();
    $tab.find('.title').text(name);
    $tab.find('.title').on('click', () => {
      this.change_tab($tab);
    });
    $tab.find('.close').on('click', () => {
      if (this.tab === name) {
        if (this.number_of_tabs() === 1)
          $(this.div).find('.editor').hide();
        else
          this.change_tab($tab.prev())
      }
      delete this.values[name];
      $tab.remove();
    });
    $(this.div).find('.tabadder').before($tab);
    this.refresh();
  }

  this.clear_tab_selection = function () {
    $(this.div).find('.tablinks').removeClass('active');
  }

  this.change_tab = function ($tab) {
    this.save_editor_value();
    this.tab = $tab.find('.title')[0].textContent;
    this.clear_tab_selection();
    $tab.addClass('active');
    this.refresh();
  }

  this.refresh = function () {
    this.editor.setValue(this.values[this.tab]);
    this.editor.refresh();
  }
}

function UI() {
  this.panes = []
  window.prevWidth = window.innerWidth;

  this.setup = function () {
    var w = window.innerWidth/this.panes.length + 'px';
    for (i = 0; i < this.panes.length; i++) {
      this.panes[i].div.style.width = w;
    }
    $('.pane-separator').each((i, e) => {
      e.addEventListener('mousedown', this.init_resize, false);
    });
  }

  this.refresh = function () {
    var factor = window.innerWidth / window.prevWidth;
    for (i = 0; i < this.panes.length; i++) {
      var w = parseFloat(this.panes[i].div.style.width.slice(0, -2));
      this.pannes[i].div.style.width = (w * factor)+'px';
    }
    window.prevWidth = window.innerWidth;
  }

  // Resizing panes
  this.resize = {
    x: 0,
    sep: null,
    pane: null,
    paneWidth: null,
    lastPane: null,
    lastPaneWidth: null
  }

  this.init_resize = (evt) => {
    this.resize.x = evt.clientX;
    this.resize.sep = evt.srcElement;
    this.resize.pane = $(this.resize.sep).prev()[0];
    this.resize.paneWidth = parseFloat(this.resize.pane.style.width.slice(0, -2));
    this.resize.lastPane = $(this.resize.sep).siblings().last()[0];
    this.resize.lastPaneWidth =
      parseFloat(this.resize.lastPane.style.width.slice(0, -2));
    $(this.resize.sep).addClass('resize');
    $('div').each((i, e) => {
      e.style.pointerEvents = 'none';
    });
    document.documentElement.addEventListener('mousemove',this.do_resize,false);
    document.documentElement.addEventListener('mouseup',this.stop_resize,false);
  }

  this.do_resize = (evt) => {
    var delta = evt.clientX - this.resize.x;
    this.resize.pane.style.width = (this.resize.paneWidth+delta)+'px';
    this.resize.lastPane.style.width = (this.resize.lastPaneWidth-delta)+'px';
  }

  this.stop_resize = (evt) => {
    $(this.resize.sep).removeClass('resize');
    $('div').each((i, e) => {
      e.style.pointerEvents = '';
    });
    document.documentElement.removeEventListener('mousemove',this.do_resize,false);
    document.documentElement.removeEventListener('mouseup',this.stop_resize,false);
  }


}

// TODO: at the moment I run any file on the left side and put in the right side
// buffer
function run(evt) {
  var panes = $('.pane');
  var source = cerberus.buffer();
  panes[0].pane.save_editor_value();
  source.c = panes[0].pane.values[panes[0].pane.tab];
  source.l = source.c.length;
  $('body').addClass('wait');
  cerberus.update(source);
  $('body').removeClass('wait');
  var result = cerberus.run();
  panes[1].pane.values[panes[1].pane.tab] = result.toString();
  panes[1].pane.refresh();
}

function create_pane_from_template(div) {
  $('#pane-template').clone().contents().appendTo(div);
  var pane = new Pane(div);
  pane.create_tab();
  div.pane = pane; // TODO: ugly: for run
  return pane;
}

function setup() {
  var ui = new UI();
  $('.pane').each((i,e) => {
    ui.panes.push(create_pane_from_template (e));
  });
  ui.setup();

  // Wait buffile to be downloaded
  $(document).ready(() => {
    ui.panes[0].set_value (cerberus.buffer().toString());
  });
}

setup();
