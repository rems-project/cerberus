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

    this.tablink.on('click', () => {
      if (this.parent)
        this.parent.setActiveTab(this)
      this.refresh()
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

    this._coreTab = null
    this._execTab = null
    this._consoleTab = null

    this.editor = CodeMirror (this.content[0], {
      mode: 'text/x-csrc',
      styleActiveLine: true,
      lineNumbers: true,
      matchBrackets: true,
      tabSize: 2,
      smartIndent: true
    })

    this.editor.addOverlay({
      token: (stream) => {
        const rx_word = "\" "
        let ch = stream.peek()
        let word = ""

        if (rx_word.includes(ch) || ch === '\uE000' || ch === '\uE001') {
          stream.next()
          return null
        }

        while ((ch = stream.peek()) && !rx_word.includes(ch)){
          word += ch
          stream.next()
        }

        let re = /{-#.+#-}/
        if (re.test(word))
          return "std"
      }
    }, { opaque: true }
    )

    this.editor.getWrapperElement().addEventListener('mousedown', (e) => {
      if ($(e.target).hasClass('cm-std')) {
        if (this.parent) {
          let tab = new TabEditor()
          this.parent.addTab(tab)
          this.parent.setActiveTab(tab)
          tab.editor.setValue(e.target.textContent)
        }
      }
    })

    this.content.addClass('editor')
  }

  get coreTab() {
    if (!this._coreTab) {
      let corePane = this.parent.parent.secondaryPane
      this._coreTab = new TabEditor(this.title + ' [core]')
      corePane.addTab(this._coreTab)
      corePane.setActiveTab(this._coreTab)
    }
    return this._coreTab;
  }

  get execTab() {
    if (!this._execTab) {
      let corePane = this.parent.parent.secondaryPane
      this._execTab = new TabEditor(this.title + ' [exec]')
      corePane.addTab(this._execTab)
      corePane.setActiveTab(this._execTab)
    }
    return this._execTab;
  }

  get consoleTab() {
    if (!this._consoleTab) {
      let corePane = this.parent.parent.secondaryPane
      this._consoleTab = new TabEditor(this.title + ' [console]')
      corePane.addTab(this._consoleTab)
      corePane.setActiveTab(this._consoleTab)
    }
    return this._consoleTab;
  }

  colorLines(i, e, color) {
    //if (e - i == 0) e++ //HACK
    for (let k = i; k <= e; k++) {
      this.editor.removeLineClass(k, 'background')
      this.editor.addLineClass(k, 'background', color)
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
      this.run (false)
    })

    $('#random').on('click', () => {
      this.run (false)
    })

    $('#exhaustive').on('click', () => {
      this.run (true)
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

  run (exhaustive) {
    this.wait()

    let sourceTab = this.activePane.activeTab
    let coreTab = sourceTab.coreTab
    let execTab = sourceTab.execTab

    let source = sourceTab.editor.getValue()
    let result = cerberus.run(source, exhaustive)
    let parsedResult = null

    if (result[0] === 0) {
      parsedResult = parseCerberusResult(result[1][1].toString())
      parsedResult.batch = result[1][2][1].toString()
    } else {
      parsedResult = {
        success: false,
        locations: [],
        core: "",
        console: result[1].toString(),
        batch: ""
      }
    }

    coreTab.editor.setValue(parsedResult.core)
    coreTab.editor.setOption('mode', 'text/x-core')

    for (let i = 0; i < parsedResult.locations.length; i++) {
      let loc = parsedResult.locations[i]
      let color = generateColor()
      sourceTab.editor.markText (
        loc.c.begin, loc.c.end,
        {className: color}
      )
      coreTab.colorLines (loc.core.begin.line, loc.core.end.line, color)
    }

    execTab.editor.setValue(parsedResult.batch)

    if (!parsedResult.success) {
      let consoleTab = sourceTab.consoleTab
      consoleTab.editor.setValue (
        consoleTab.editor.getValue()+parsedResult.console
      )
    }

    this.done()
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

function generateColor() {
  function basicColor (mix) {
    return Math.floor((Math.floor(Math.random()*256)+mix)/2)
  }
  let r = basicColor(255)
  let g = basicColor(255)
  let b = basicColor(255)
  let className = 'color'+r+g+b
  style.innerHTML +=
    '.' + className +' { background-color: rgba('+r+','+g+','+b+',1); }\n'
  return className
}

function parseCerberusResult(res) {
  function countLines(str) {
    return str.split(/\r\n|\r|\n/).length - 1
  }

  let bits = res.split(/{-#(\d*:\d*-\d*:\d*:|E...)#-}/g)
  let core = ""
  let locs = [], stkLoc = [], stkLine0 = []
  let l0 = 0, l = 0
  for (let i = 0; i < bits.length; i++) {
    if (bits[i] == 'ELOC') {
      // finish last location
      let cloc = stkLoc.pop().toString().match(/\d+/g)
      locs.push({
        c: {
          begin: {line: cloc[0]-1, ch: cloc[1]-1},
          end: {line: cloc[2]-1, ch: cloc[3]-1}
        },
        core: {
          begin: {line: l0, ch: 0},
          end: {line: l, ch: 0}
        }
      })
      l0 = stkLine0.pop()
      continue;
    }
    if (/\d*:\d*-\d*:\d*:/g.test(bits[i])) {
      stkLine0.push(l0)
      stkLoc.push(bits[i])
      l0 = l
      continue;
    }
    // a bit of core source
    core += bits[i]
    l += countLines(bits[i])
  }

  locs.sort((a, b) => {
    return (a.core.end.line - a.core.begin.line)
      < (b.core.end.line - b.core.begin.line) ? 1:-1
  })

  return {
    success: true,
    locations: locs,
    core: core
  }
}

let style = document.createElement('style')
style.type = 'text/css'
document.head.appendChild(style)
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
