'use_strict'

// Globals

/* Generic Tab */
class Tab {
  constructor(title) {
    this.parent = null

    this.dom         = $('#tab-template').clone().contents()
    this.dom.content = $('<div class="tab-content"></div>')

    this.setTitle(title)
    this.addEventListener()
  }

  addEventListener() {
    this.dom.on('click', () => {
      this.setActive()
    })

    this.dom.children('.close').on('click', () => {
      if (this.parent)
        this.parent.remove(this)
    })

    this.dom.on('dragstart', (evt) => {
      if (ui) ui.currentView.draggedTab = this
      $('body').addClass('grabbing')
    })

    this.dom.on('dragend', (evt) => {
      $('body').removeClass('grabbing')
    })
  }

  setTitle (title) {
    this.title = title
    this.dom.children('.title').text(title)
  }

  setActive() {
    if (this.parent) {
      this.parent.clearSelection()
      this.parent.setActiveTab(this)
    }
    this.dom.addClass('active')
    this.dom.content.show()
    this.refresh()
  }

  clearSelection () {
    this.dom.removeClass('active')
    this.dom.content.hide()
  }

  isSelected () {
    this.dom.hasClass('active')
  }

  refresh () {
    // Overwritten
  }

}

/* Tab with SVG graph */
class TabGraph extends Tab {
  constructor(title) {
    super(title)

    this.dom.graph = $('#graph-template').clone().contents()
    this.dom.content.append(this.dom.graph)
    this.svg = null

    this.dom.graph.children('#minus').on('click', () => {
      this.svg.panzoom('zoom', true)
    })

    this.dom.graph.children('#reset').on('click', () => {
      this.svg.panzoom('resetZoom')
      this.svg.panzoom('resetPan')
    })

    this.dom.graph.children('#plus').on('click', () => {
      this.svg.panzoom('zoom');
    })
  }

  setValue(data) {
    // Remove previous one
    if (this.svg)
      this.svg.remove()

    // Add to the container
    this.dot = json_to_dot(data)
    this.dom.graph.children('.svg').append(Viz(this.dot))
    this.svg = this.dom.graph.find('svg')
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
    this.dom.content.addClass('editor')

    this.editor = CodeMirror (this.dom.content[0], {
      styleActiveLine: true,
      lineNumbers: true,
      matchBrackets: true,
      tabSize: 2,
      smartIndent: true,
      lineWrapping: true
    })

    this.editor.on('blur', (doc) => {
      if (!this.dirty) ui.currentView.highlight()
      this.skipCursorEvent = true
    })

    // CodeMirror overwrites 'click' events
    this.editor.on('mousedown', () => {
      if (!this.dirty) ui.currentView.highlight()
      this.skipCursorEvent = true
    })

    this.editor.on('dblclick', (doc) => {
      this.skipCursorEvent = false
      this.markSelection(doc)
    })

    this.editor.on('viewportChange', (doc) => {
      console.log('view port change')
    })

    this.editor.on('refresh', (doc) => {
      console.log('refresh')
    })

    this.editor.on('update', (doc) => {
      console.log('update')
    })



    if (source) this.editor.setValue(source)

    this.dirty = false
    this.skipCursorEvent = true
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

  clear() {
    this.editor.eachLine((line) => {
      this.editor.removeLineClass(line, 'background')
    })
  }

  markText (begin, end, cls) {
    this.editor.markText(begin, end, cls)
  }

  markSelection(doc) {
    // Just got focus or a click event
    if (this.skipCursorEvent) {
      this.skipCursorEvent = false
      return;
    }
    // If not dirty, then mark selection
    if (!this.dirty) {
      let from = doc.getCursor('from')
      let to   = doc.getCursor('to')
      ui.currentView.markSelection(this.getLocation(from, to))
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
    this.editor.on('cursorActivity', (doc) => this.markSelection(doc))

    this.editor.on('change', () => {
      if (ui.currentView)
        ui.currentView.clear()
      this.dirty = true
    })

  }

  getLocation(from, to) {
    let locations = ui.currentView.locations;
    for (let i = locations.length - 1; i >= 0; i--) {
      let loc = locations[i]
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
  }
}

/* Tab Core */
class TabCore extends TabReadOnly {
  constructor (title) {
    super(title)

    this.tooltip = $(document.createElement('div'))
    this.tooltip.addClass('tooltip')
    this.tooltip.appendTo(this.content)
    this.tooltipVisible = false

    this.editor.setOption('mode', 'text/x-core')
    this.editor.on('cursorActivity', (doc) => this.markSelection(doc))

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
    }, { opaque: true, priority: 1000 }
    )

    this.editor.getWrapperElement().addEventListener('mousedown', (e) => {
      let edom = $(e.target);
      if (edom.hasClass('cm-std')) {
        if (edom.hasClass('tooltip')) {
          edom.removeClass('tooltip')
          edom.siblings('.tooltip-text').remove()
        } else {
          edom.addClass('tooltip')
          let content = getSTDSection(e.target.textContent)
          edom.after($('<span class="tooltip-text"></span>').append(content.data))
        }
      }
    })
  }

  getLocation(from, to) {
    let locations = ui.currentView.locations
    for (let i =locations.length - 1; i >= 0; i--) {
      let loc = locations[i]
      if (loc.core.begin.line <= from.line && loc.core.end.line >= to.line)
        return loc
    }
    return null
  }

}
