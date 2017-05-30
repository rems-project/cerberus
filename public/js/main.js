'use_strict';

// Globals
var source_counter = 1;

function Tab (title, value) {
  this.select = () => {
    this.tablink.addClass('active');
    this.content.show();
  }

  this.clearSelection = () => {
    this.tablink.removeClass('active');
    this.content.hide();
  }

  this.isSelected = () => {
    this.tablink.hasClass('active');
  }

  this.refresh = () => {
  }

  this.parent = null;

  this.title = title;

  if (!this.title) {
    this.title = 'Source #' + source_counter;
    source_counter++;
  }

  this.tablink = $('#tablink-template').clone().contents();

  this.tabtitle = this.tablink.find('.title');
  this.tabtitle.text(this.title);

  this.tabclose = this.tablink.find('.close');

  this.content = $(document.createElement('div'));

  this.tabtitle.on('click', () => {
    if (this.parent)
      this.parent.setActiveTab(this);
  });

  this.tabclose.on('click', () => {
    if (this.parent)
      this.parent.removeTab(this);
  });

}

function TabEditor (title, value) {
  Tab.call(this, title, value);

  this.editor = CodeMirror (this.content[0], {
    mode: 'text/x-csrc',
    styleActiveLine: true,
    lineNumbers: true,
    matchBrackets: true,
    tabSize: 2,
    smartIndent: true
  });

  this.content.addClass('editor');

  this.refresh = () => {
    this.editor.refresh();
  }
}

// Types
function Pane (div) {
  this.firstTab = () => {
    return this.tabs[0];
  }

  this.prevTab = (tab) => {
    for (var i = 1; i < this.tabs.length; i++)
      if (this.tabs[i] === tab)
        return this.tabs[i-1];
    return null;
  }

  this.addTab = (tab) => {
    this.tabs.push(tab);
    this.tabadder.before(tab.tablink);
    this.content.append(tab.content);
    tab.parent = this;
    tab.refresh();
  }

  this.removeTab = (tab) => {
    if (tab === this.activeTab) {
      var prev = this.prevTab(tab);
      if (prev)
        this.setActiveTab(prev);
      else if (this.tabs.length > 0)
        this.setActiveTab(this.firstTab());
    }

    tab.tablink.remove();
    tab.content.remove();

    for(var i = 0; i < this.tabs.length; i++) {
      if (this.tabs[i] === tab) {
        this.tabs.splice(i, 1);
      }
    }

    if (this.tabs.length == 0)
      this.parent.removePane(this);
  }

  this.setActiveTab = (tab) => {
    if (this.activeTab)
      this.activeTab.clearSelection();
    tab.select();
    this.activeTab = tab;
  }

  this.refresh = () => {
    this.activeTab.refresh();
  }

  this.tabs = [];

  // UI
  this.parent = null;
  if (div) {
    this.div = $(div);
  } else {
    this.div = $('#pane-template').clone().contents();
  }
  this.tabadder = this.div.find('.tabadder');
  this.content = this.div.find('.content');

  this.activeTab = new TabEditor();
  this.addTab(this.activeTab);

  // Event listeners
  this.tabadder.on('click', () => {
    var tab = new TabEditor();
    this.addTab(tab);
    this.setActiveTab(tab);
  });


}

function UI() {
  this.setup = () => {
    var w = window.innerWidth/this.panes.length + 'px';
    for (i = 0; i < this.panes.length; i++) {
      this.panes[i].div.width(w);
    }
    $('.pane-separator').each((i, e) => {
      e.addEventListener('mousedown', this.init_resize, false);
    });
  }

  this.wait = () => {
    $('body').addClass('wait');
  }

  this.done = () => {
    $('body').removeClass('wait');
  }

  this.addPane = (pane) => {
    if (this.panes.length > 0) {
      $('<div class="pane-separator"></div>').appendTo(this.div);
    }
    this.panes.push(pane);
    this.div.append(pane.div);
    pane.parent = this;
    pane.refresh();
  }

  this.secondaryPane = () => {
  }

  this.removePane = (pane) => {
    if (this.panes.length == 1) {
      pane.div.remove();
      return;
    }
    var sep = null;
    if (this.panes[0] === pane)
      sep = pane.div.next('.pane-separator');
    else
      sep = pane.div.prev('.pane-separator');
    sep.remove();
    pane.div.remove();

    for (var i = 0; i < this.panes.length; i++) {
      if (this.panes[i] === pane) {
        this.panes.splice(i, 1);
      }
    }
    this.setup();
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

  this.refresh = () => {
    var factor = window.innerWidth / window.prevWidth;
    for (i = 0; i < this.panes.length; i++) {
      var w = parseFloat(this.panes[i].div[0].style.width.slice(0, -2));
      this.panes[i].div[0].style.width = (w * factor)+'px';
    }
    window.prevWidth = window.innerWidth;
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

  this.panes = []
  window.prevWidth = window.innerWidth;

  this.div = $('#panes');
  this.activePane = new Pane();
  this.addPane(this.activePane);

  this.setup();

  $('#run').on('click', () => {
    this.wait();
    var source = this.activePane.activeTab.editor.getValue();
    var result = cerberus.run(source);
    this.activePane.activeTab.editor.setValue(result.toString());
    this.activePane.activeTab.editor.setOption('mode', 'text/x-core');
    this.done();
  });

  $('#new_pane').on('click', () => {
    this.addPane(new Pane());
    this.setup();
  });

  $('#new_tab').on('click', () => {
    let tab = new TabEditor();
    this.activePane.addTab(tab);
    this.activePane.setActiveTab(tab);
  });
}

var ui = new UI();

// Wait buffer.c to be downloaded
$(window).ready(() => {
  ui.setup();
  ui.activePane.activeTab.editor.setValue(cerberus.buffer().toString());
});
