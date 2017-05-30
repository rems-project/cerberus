'use_strict'

// Globals
let source_counter = 1

class Tab {
  constructor(title, value) {
    this.parent = null

    this.title = title

    if (!this.title) {
      this.title = 'Source #' + source_counter
      source_counter++
    }

    this.tablink = $('#tablink-template').clone().contents()

    this.tabtitle = this.tablink.find('.title')
    this.tabtitle.text(this.title)

    this.tabclose = this.tablink.find('.close')

    this.content = $(document.createElement('div'))
    this.content.addClass('tab-content')

    this.tabtitle.on('click', () => {
      if (this.parent)
        this.parent.setActiveTab(this)
    })

    this.tabclose.on('click', () => {
      if (this.parent)
        this.parent.removeTab(this)
    })
  }

  setTitle (title) {
    this.title = title
    this.tabtitle.text(title)
  }

  select () {
    this.tablink.addClass('active')
    this.content.show()
  }

  clearSelection () {
    this.tablink.removeClass('active')
    this.content.hide()
  }

  isSelected () {
    this.tablink.hasClass('active')
  }

  refresh () {
  }

}

class TabEditor extends Tab {
  constructor(title, value) {
    super(title, value)
    this.editor = CodeMirror (this.content[0], {
      mode: 'text/x-csrc',
      styleActiveLine: true,
      lineNumbers: true,
      matchBrackets: true,
      tabSize: 2,
      smartIndent: true
    })

    this.content.addClass('editor')
  }

  colorLines(i, e, color) {
    for (let k = i; k < e; k++) {
      this.editor.removeLineClass(k, 'gutter')
      this.editor.addLineClass(k, 'gutter', color)
    }
  }

  refresh () {
    this.editor.refresh()
  }
}

// Types
class Pane {
  constructor (div) {
    this.tabs = []

    // UI
    this.parent = null
    if (div) {
      this.div = $(div)
    } else {
      this.div = $('#pane-template').clone().contents()
    }
    this.tabadder = this.div.find('.tabadder')
    this.content = this.div.find('.content')
    this.activeTab = null

    // Event listeners
    this.tabadder.on('click', () => {
      let tab = new TabEditor()
      this.addTab(tab)
      this.setActiveTab(tab)
      if (this.parent)
        this.parent.activePane = this
    })

    this.content.on('click', () => {
      if (this.parent)
        this.parent.activePane = this
    })
  }

  get firstTab () {
    return this.tabs[0]
  }

  prevTab (tab) {
    for (let i = 1; i < this.tabs.length; i++)
      if (this.tabs[i] === tab)
        return this.tabs[i-1]
    return null
  }

  addTab (tab) {
    this.tabs.push(tab)
    this.tabadder.before(tab.tablink)
    this.content.append(tab.content)
    tab.parent = this
    if (!this.activeTab)
      this.activeTab = tab
    tab.refresh()
  }

  removeTab (tab) {
    if (tab === this.activeTab) {
      let prev = this.prevTab(tab)
      if (prev)
        this.setActiveTab(prev)
      else if (this.tabs.length > 0)
        this.setActiveTab(this.firstTab)
    }

    tab.tablink.remove()
    tab.content.remove()

    for(let i = 0; i < this.tabs.length; i++) {
      if (this.tabs[i] === tab) {
        this.tabs.splice(i, 1)
      }
    }

    if (this.tabs.length == 0)
      this.parent.removePane(this)
  }

  setActiveTab (tab) {
    if (this.activeTab)
      this.activeTab.clearSelection()
    tab.select()
    this.activeTab = tab
  }

  refresh () {
    if (this.activeTab)
      this.activeTab.refresh()
  }
}

class UI {

  pickColor(i) {
    switch (i % 6) {
      case 0:
        return 'color0'
      case 1:
        return 'color1'
      case 2:
        return 'color2'
      case 3:
        return 'color3'
      case 4:
        return 'color4'
      case 5:
        return 'color5'
    }
  }

  decorateLines (ctab, coretab, locs, i) {
    let head = fst (locs)
    let tail = snd (locs)

    let color = this.pickColor(i);

    let cpos = (fst(head)).toString().match(/\d+/g)
    ctab.editor.markText(
      {line: parseInt(cpos[0])-1, ch: parseInt(cpos[1])-1},
      {line: parseInt(cpos[2])-1, ch: parseInt(cpos[3])-1},
      {className: color}
    )

    let corepos = snd(head)
    coretab.colorLines (fst(corepos), snd(corepos), color)

    if (tail == 0) return;
    this.decorateLines(ctab, coretab, tail, i+1)
  }

  constructor () {
    this.panes = []
    window.prevWidth = window.innerWidth
    this.div = $('#panes')
    this.activePane = null

    // Resizing panes event
    this.resize = {
      x: 0,
      sep: null,
      pane: null,
      paneWidth: null,
      lastPane: null,
      lastPaneWidth: null
    }

    $('#run').on('click', () => {
      this.wait()
      let source = this.activePane.activeTab.editor.getValue()
      let result = cerberus.run(source)
      let corePane = this.secondaryPane
      let tab = new TabEditor(this.activePane.activeTab.title + ' [core]')
      tab.editor.setValue(snd(result).toString())
      tab.editor.setOption('mode', 'text/x-core')

      let locs = fst(result)
      this.decorateLines(this.activePane.activeTab, tab, locs, 0);

      corePane.addTab(tab)
      corePane.setActiveTab(tab)
      this.done()
    })

    $('#new_pane').on('click', () => {
      let pane = new Pane()
      pane.addTab(new TabEditor())
      this.addPane(pane)
      this.setup()
    })

    $('#new_tab').on('click', () => {
      let tab = new TabEditor()
      this.activePane.addTab(tab)
      this.activePane.setActiveTab(tab)
    })

    $('#help').on('click', () => {
      let tab = new Tab('Help')
      tab.content.append($('#help-template').clone().contents())
      this.activePane.addTab(tab)
      this.activePane.setActiveTab(tab)
    })
  }

  setup () {
    let w = window.innerWidth/this.panes.length + 'px'
    for (let i = 0; i < this.panes.length; i++) {
      this.panes[i].div.width(w)
    }
    $('.pane-separator').on('mousedown', e => this.init_resize(e))
  }

  wait () {
    $('body').addClass('wait')
  }

  done () {
    $('body').removeClass('wait')
  }

  addPane (pane) {
    if (this.panes.length > 0) {
      $('<div class="pane-separator"></div>').appendTo(this.div)
    }
    this.panes.push(pane)
    this.div.append(pane.div)
    pane.parent = this
    pane.refresh()
  }

  get secondaryPane () {
    if (this.panes.length < 2 || !this.activePane) {
      let pane = new Pane()
      this.addPane(pane)
      this.setup()
      return pane
    }
    for (let i = 1; i < this.panes.length - 1; i++) {
      if (this.panes[i-1] == this.activePane)
        return this.panes[i]
    }
    return this.panes[this.panes.length - 1]
  }

  removePane (pane) {
    if (this.panes.length == 1) {
      pane.div.remove()
      this.setup()
      return
    }
    let sep = null
    if (this.panes[0] === pane)
      sep = pane.div.next('.pane-separator')
    else
      sep = pane.div.prev('.pane-separator')
    sep.remove()
    pane.div.remove()

    for (let i = 0; i < this.panes.lengtha; i++) {
      if (this.panes[i] === pane) {
        this.panes.splice(i, 1)
      }
    }
    this.setup()
  }

  refresh () {
    let factor = window.innerWidth / window.prevWidth
    for (i = 0; i < this.panes.length; i++) {
      let w = parseFloat(this.panes[i].div[0].style.width.slice(0, -2))
      this.panes[i].div[0].style.width = (w * factor)+'px'
    }
    window.prevWidth = window.innerWidth
  }

  init_resize (evt) {
    this.resize.x = evt.clientX
    this.resize.sep = evt.currentTarget
    this.resize.pane = $(this.resize.sep).prev()[0]
    this.resize.paneWidth = parseFloat(this.resize.pane.style.width.slice(0, -2))
    this.resize.lastPane = $(this.resize.sep).siblings().last()[0]
    this.resize.lastPaneWidth =
      parseFloat(this.resize.lastPane.style.width.slice(0, -2))
    $(this.resize.sep).addClass('resize')
    $('div').each((i, e) => e.style.pointerEvents = 'none')
    $(document.documentElement).on('mousemove', e => this.do_resize(e));
    $(document.documentElement).on('mouseup', e => this.stop_resize(e));
  }

  do_resize (evt) {
    let delta = evt.clientX - this.resize.x
    this.resize.pane.style.width = (this.resize.paneWidth+delta)+'px'
    this.resize.lastPane.style.width = (this.resize.lastPaneWidth-delta)+'px'
  }

  stop_resize (evt) {
    $(this.resize.sep).removeClass('resize')
    $('div').each((i, e) => e.style.pointerEvents = '')
    $(document.documentElement).off('mousemove');
    $(document.documentElement).off('mouseup');
  }

}

// ML pair
function fst(array) {
  if (array.length != 3 || array[0] != 0) {
    alert ("Not a pair: " + array);
    return;
  }
  return array[1];
}

function snd(array) {
  if (array.length != 3 || array[0] != 0) {
    alert ("Not a pair: " + array);
    return;
  }
  return array[2];
}

const ui = new UI()

// Wait buffer.c to be downloaded
function onLoadCerberus() {
  $(window).ready(() => {
    ui.activePane = new Pane()
    ui.addPane(ui.activePane)
    ui.activePane.addTab(new TabEditor())
    ui.activePane.activeTab.setTitle('hello.c')
    ui.activePane.activeTab.editor.setValue(cerberus.buffer().toString())
    ui.setup()
  })
}
