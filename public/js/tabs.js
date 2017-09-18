'use_strict'

// Globals

/* Generic Tab */
class Tab {
  constructor(title) {
    this.parent = null

    this.title = title
    this.alive = true

    if (!this.title && ui) {
      this.title = 'Source #' + ui.sourceCounter
      ui.sourceCounter++
    }

    this.tablink = $('#tab-template').clone().contents()

    this.tabtitle = this.tablink.find('.title')
    this.tabtitle.text(this.title)

    this.tabclose = this.tablink.find('.close')

    this.content = $(document.createElement('div'))
    this.content.addClass('tab-content')

    this.addEventListener()
  }

  addEventListener() {
    this.tablink.on('click', () => {
      this.setActive()
    })

    this.tabclose.on('click', () => {
      if (this.parent)
        this.parent.removeTab(this)
    })

    this.tablink.on('dragstart', (evt) => {
      if (ui)
        ui.draggedTab = this
      $('body').addClass('grabbing')
    })

    this.tablink.on('dragend', (evt) => {
      $('body').removeClass('grabbing')
    })
  }

  setTitle (title) {
    this.title = title
    this.tabtitle.text(title)
  }

  setActive() {
    if (this.parent) {
      this.parent.clearSelection()
      this.parent.setActiveTab(this)
    }
    this.tablink.addClass('active')
    this.content.show()
    this.refresh()
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

/* Tab with SVG graph */
class TabGraph extends Tab {
  constructor(title, srcTab) {
    super(title)

    this.srcTab = srcTab
    this.graph = $('#graph-template').clone().contents()
    this.graph.appendTo(this.content);

    this.svg_container = this.graph.find('.svg_container')
    this.svg = null

    this.graph.find('#minus').on('click', () => {
      this.svg.panzoom('zoom', true)
    })

    this.graph.find('#reset').on('click', () => {
      this.svg.panzoom('resetZoom')
      this.svg.panzoom('resetPan')
    })

    this.graph.find('#plus').on('click', () => {
      this.svg.panzoom('zoom');
    })

  }

  setValue(data) {
    // Remove previous one
    if (this.svg)
      this.svg.remove()

    // Add to the container
    this.dot = json_to_dot(data)
    this.svg_container.append(Viz(this.dot))
    this.svg = this.graph.find('svg')
    this.svg.panzoom()

    // Set active
    this.setActive()
    this.refresh()
  }
}

/* Tab with CodeMirror editor */
class TabEditor extends Tab {
  constructor(title, source) {
    super(title)
    this.editor = CodeMirror (this.content[0], {
      styleActiveLine: true,
      lineNumbers: true,
      matchBrackets: true,
      tabSize: 2,
      smartIndent: true
    })
    this.content.addClass('editor')
    this.dirty = false
    this.editor.on('change', () => this.dirty = true)
    if (source)
      this.editor.setValue(source)
  }

  getValue() {
    return this.editor.getValue()
  }

  setValue(value) {
    this.editor.setValue(value)
    this.setActive()
    this.refresh()
  }

  appendValue(value) {
    this.setValue(this.getValue()+value)
  }

  colorLines(i, e, color) {
    for (let k = i; k <= e; k++) {
      this.editor.removeLineClass(k, 'background')
      this.editor.addLineClass(k, 'background', color)
    }
  }

  refresh () {
    this.editor.refresh()
  }
}

/* ReadOnly Editor */
class TabReadOnly extends TabEditor {
  constructor (title) {
    super(title)
    this.editor.setOption ('readOnly', true)
  }
}

/* Tab C source */
class TabSource extends TabEditor {
  constructor(title, source) {
    super(title, source)
    this.editor.setOption('mode', 'text/x-csrc')
    this.editor.on('cursorActivity', (doc) => this.activity(doc))
    this._coreTab = null
    this._execTab = null
    this._consoleTab = null
    this._graphTab = null
    this.locations = null
    this._selection = false
  }

  activity(doc) {
    let from = doc.getCursor('from')
    let to = doc.getCursor('to')

    // If core tab is not alive anymore
    // we should stop coloring
    if (this._coreTab && !this._coreTab.alive)
      this.dirty = true

    if (from === to) {
      if (!this._selection) return // nothing to do
      this.clear()
      if (!this.dirty) this.highlight()
      this._selection = false
      return
    }

    if (!this._selection) {
      this.clear()
      if (this._coreTab && this._coreTab.alive)
        this.coreTab.clear()
    }

    if (!this.dirty) {
      let loc = this.getLocationFromSelection(from, to)
      if (loc) {
        this.editor.markText (loc.c.begin, loc.c.end, {className: loc.color})
        this.coreTab.colorLines (loc.core.begin.line, loc.core.end.line, loc.color)
      }
    }
    this._selection = true
  }

  get coreTab() {
    if (this._coreTab && this._coreTab.alive)
      return this._coreTab
    if (!ui) return null;
    this._coreTab = new TabCore(this.title + ' [core]', this)
    ui.secondaryPane.addTab(this._coreTab)
    this._coreTab.setActive()
    return this._coreTab;
  }

  get execTab() {
    if (this._execTab && this._execTab.alive)
      return this._execTab
    if (!ui) return null;
    this._execTab = new TabReadOnly(this.title + ' [exec]')
    this._execTab.srcTab = this
    ui.secondaryPane.addTab(this._execTab)
    this._execTab.setActive()
    return this._execTab;
  }

  get consoleTab() {
    if (this._consoleTab && this._consoleTab.alive)
      return this._consoleTab
    if (!ui) return null;
    this._consoleTab = new TabReadOnly(this.title + ' [console]')
    this._consoleTab.srcTab = this
    ui.secondaryPane.addTab(this._consoleTab)
    this._consoleTab.setActive()
    return this._consoleTab;
  }

  get graphTab() {
    if (this._graphTab && this._graphTab.alive)
      return this._graphTab
    if (!ui) return null;
    this._graphTab = new TabGraph(this.title + ' [graph]', this)
    ui.secondaryPane.addTab(this._graphTab)
    this._graphTab.setActive()
    return this._graphTab;
  }

  getLocationFromSelection(from, to) {
    for (let i = this.locations.length - 1; i >= 0; i--) {
      let loc = this.locations[i]
      if ((loc.c.begin.line < from.line ||
          (loc.c.begin.line == from.line && loc.c.begin.ch <= from.ch))
        && (loc.c.end.line > to.line ||
          (loc.c.end.line == to.line && loc.c.end.ch >= to.ch)))
        return loc
    }
    return null
  }

  clear() {
    let marks = this.editor.getAllMarks()
    for (let i = 0; i < marks.length; i++)
      marks[i].clear()
    if (this._coreTab && this._coreTab.active)
      this.coreTab.clear()
  }

  highlight() {
    if (!this.locations) return
    for (let i = 0; i < this.locations.length; i++) {
      let loc = this.locations[i]
      this.editor.markText (
        loc.c.begin, loc.c.end,
        {className: loc.color}
      )
      this.coreTab.colorLines (loc.core.begin.line, loc.core.end.line, loc.color)
    }

  }
}

/* Tab Core */
class TabCore extends TabReadOnly {
  constructor (title, srcTab) {
    super(title)

    this.srcTab = srcTab
    this._selection = false

    this.tooltip = $(document.createElement('div'))
    this.tooltip.addClass('tooltip')
    this.tooltip.appendTo(this.content)
    this.tooltipVisible = false

    this.editor.setOption('mode', 'text/x-core')
    this.editor.on('cursorActivity', (doc) => this.activity(doc))

    this.locations = null

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

        let re = /{-#.+[#,]/
        if (re.test(word))
          return "std"
      }
    }, { opaque: true }
    )

    this.editor.getWrapperElement().addEventListener('mousedown', (e) => {
      if ($(e.target).hasClass('cm-std')) {
        if (this.parent) {
          let content = getSTDSection(e.target.textContent)
          let tab = new Tab(content.title)
          this.parent.addTab(tab)
          tab.content.append(content.data)
          tab.setActive()
        }
      }
    })

    this.editor.getWrapperElement().addEventListener ('mouseover', (e) => {
      // If tooltip is still visible, remove it
      if (this.tooltipVisible) {
        this.tooltip.removeClass('tooltip-visible')
        this.tooltipVisible = false
      }

      if ($(e.target).hasClass('cm-std')) {
        let content = getSTDSentence(e.target.textContent)
        this.tooltip.addClass('tooltip-visible')
        this.tooltip.css({left: e.pageX, top: e.pageY})
        this.tooltip.text(content)
        this.tooltipVisible = true
        return
      }

      let pos = this.editor.coordsChar({left: e.pageX,top: e.pageY})
      let token = this.editor.getTokenAt(pos)
      if (token.type == 'keyword') {
        let msg = null
        switch (token.string) {
          case 'strong':
            msg = 'strong sequencing dictates memory action order'
            break
          case 'weak':
            msg = 'weak sequencing does not dictate memory action order'
            break
          case 'pure':
            msg = 'a pure expression does not have any side effect.'
            break
          default:
            return;
        }
        if (!msg)
          return
        this.tooltip.addClass('tooltip-visible')
        this.tooltip.css({left: e.pageX, top: e.pageY})
        this.tooltip.text(msg)
        this.tooltipVisible = true
        return
      }
    })
  }

  activity(doc) {
    // If source tab is not alive or has been changed, don't do anything
    //if (!this.srcTab.alive || this.srcTab.dirty)
    //  return

    let from = doc.getCursor('from')
    let to = doc.getCursor('to')

    if (from === to) {
      if (!this._selection) return // nothing to do
      this.clear()
      this.highlight()
      this._selection = false
      return
    }

    if (!this._selection) {
      this.srcTab.clear()
      this.clear()
    }

    let loc = this.getLocationFromSelection(from, to)
    if (loc) {
      this.srcTab.editor.markText (loc.c.begin, loc.c.end, {className: loc.color})
      this.colorLines (loc.core.begin.line, loc.core.end.line, loc.color)
    }

    this._selection = true
  }

  getLocationFromSelection(from, to) {
    for (let i = this.locations.length - 1; i >= 0; i--) {
      let loc = this.locations[i]
      if (loc.core.begin.line <= from.line && loc.core.end.line >= to.line)
        return loc
    }
    return null
  }

  clear() {
    this.editor.eachLine((line) => {
      this.editor.removeLineClass(line, 'background')
    })
  }

  highlight() {
    if (!this.locations) return
    for (let i = 0; i < this.locations.length; i++) {
      let loc = this.locations[i]
      this.srcTab.editor.markText (
        loc.c.begin, loc.c.end,
        {className: loc.color}
      )
      this.colorLines (loc.core.begin.line, loc.core.end.line, loc.color)
    }
  }
}
