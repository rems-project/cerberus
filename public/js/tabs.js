'use_strict'

// Globals
let sourceCounter = 1
let draggedTab = null // this is sad

class Tab {
  constructor(title) {
    this.parent = null

    this.title = title

    if (!this.title) {
      this.title = 'Source #' + sourceCounter
      sourceCounter++
    }

    this.tablink = $('#tablink-template').clone().contents()

    this.tabtitle = this.tablink.find('.title')
    this.tabtitle.text(this.title)

    this.tabclose = this.tablink.find('.close')

    this.content = $(document.createElement('div'))
    this.content.addClass('tab-content')

    this.dragDiv = null

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
      draggedTab = this
      $('body').addClass('grabbing')
      // TODO: build a hover div
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
      this.parent.activeTab = this
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

class TabEditor extends Tab {
  constructor(title) {
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

class TabReadOnly extends TabEditor {
  constructor (title) {
    super(title)
    this.editor.setOption ('readOnly', true)
  }
}

class TabGraph extends Tab {
  constructor(title, dot) {
    super(title)

    this.graph = $('#graph-template').clone().contents()
    this.graph.appendTo(this.content);

    this.graph.find('#centre').on('click', () => {
      this.svg.panzoom('resetPan')
    })

    this.graph.find('#minus').on('click', () => {
      this.svg.panzoom('zoom', true)
    })

    this.graph.find('#reset').on('click', () => {
      this.svg.panzoom('resetZoom')
    })

    this.graph.find('#plus').on('click', () => {
      this.svg.panzoom('zoom');
    })
  }

  json_to_dot(data) {
    function aux (i, d) {
      switch (d.label) {
        case "active":
          return {
            index: i+1,
            nodes: [parseInt(i) + '[label="' + d.arena + '"]'],
            edges: []
          }
        case "killed":
          return {
            index: i+1,
            nodes: [parseInt(i) + '[label="killed"]'],
            edges: []
          }
        case "nd":
          let nd = {
            index: i,
            nodes: [],
            edges: []
          }
          for (let j = 0; j < d.children.length; j++) {
            let c = aux(nd.index+1, d.children[j])
            nd.nodes = nd.nodes.concat(c.nodes)
            nd.edges = nd.edges.concat(c.edges)
            nd.edges.push(parseInt(i) + " -> " + parseInt(nd.index+1))
            nd.index = c.index
          }
          nd.nodes.push(parseInt(i) + '[label="nd"]')
          return nd
        case "guard":
          let c = aux(i+1, d.child)
          c.nodes.push(parseInt(i) + '[label="guard"]')
          c.nodes.push(parseInt(i) + " -> " + parseInt(i+1))
          return c
        case "branch":
          let c1 = aux(i+1, d.child1)
          let c2 = aux(c1.index+1, d.child2)
          let ns = c2.nodes.concat(c1.nodes)
          let es = c2.edges.concat(c1.edges)
          ns.push(parseInt(i) + '[label="branch"]')
          es.push(parseInt(i) + " -> " + parseInt(i+1))
          es.push(parseInt(i) + " -> " + parseInt(c1.index+1))
          return {
            index: c2.index,
            nodes: ns,
            edges: es
          }
      }
      alert ('json_to_dot: fatal error')
    }
    let x = aux(1, data)
    let dot = "digraph G {node[shape=box];"
    for (let i = 0; i < x.nodes.length; i++)
      dot += x.nodes[i] + ";"
    for (let i = 0; i < x.edges.length; i++)
      dot += x.edges[i] + ";"
    return dot + "}"
  }

  setGraph(data) {
    this.graph.find('.svg_container').append(Viz(this.json_to_dot(data)))
    this.svg = this.graph.find('svg')
    this.svg.panzoom()
  }
}

class TabSource extends TabEditor {
  constructor(title ) {
    super(title)
    this.editor.setOption('mode', 'text/x-csrc')
    this.editor.on('cursorActivity', (doc) => this.activity(doc))
    this._coreTab = null
    this._execTab = null
    this._consoleTab = null
    this._graphTab = null
    this.data = null
    this._selection = false
  }

  activity(doc) {
    let from = doc.getCursor('from')
    let to = doc.getCursor('to')

    if (from === to) {
      if (!this._selection) return // nothing to do
      this.clear()
      if (!this.dirty) this.highlight()
      this._selection = false
      return
    }

    if (!this._selection) {
      this.clear()
    }

    if (!this.dirty) {
      let loc = this.getLocationFromSelection(from, to)
      if (loc) {
        this.editor.markText (loc.c.begin, loc.c.end, {className: loc.color})
        this.coreTab.colorLines (loc.core.begin.line, loc.core.end.line, loc.color)
      }
    }
    this._selection = true
    console.log('selection')
  }

  get coreTab() {
    if (!this._coreTab) {
      let corePane = this.parent.parent.secondaryPane
      this._coreTab = new TabCore(this.title + ' [core]')
      corePane.addTab(this._coreTab)
      this._coreTab.setActive()
    }
    return this._coreTab;
  }

  get execTab() {
    if (!this._execTab) {
      let corePane = this.parent.parent.secondaryPane
      this._execTab = new TabReadOnly(this.title + ' [exec]')
      corePane.addTab(this._execTab)
      this._execTab.setActive()
    }
    return this._execTab;
  }

  get consoleTab() {
    if (!this._consoleTab) {
      let corePane = this.parent.parent.secondaryPane
      this._consoleTab = new TabReadOnly(this.title + ' [console]')
      corePane.addTab(this._consoleTab)
      this._consoleTab.setActive()
    }
    return this._consoleTab;
  }

  get graphTab() {
    if (!this._graphTab) {
      let corePane = this.parent.parent.secondaryPane
      this._graphTab = new TabGraph(this.title + ' [graph]')
      corePane.addTab(this._graphTab)
      this._graphTab.setActive()
    }
    return this._graphTab;
  }

  getLocationFromSelection(from, to) {
    for (let i = this.data.locations.length - 1; i >= 0; i--) {
      let loc = this.data.locations[i]
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
    if (this._coreTab)
      this.coreTab.clear()
  }

  highlight() {
    if (!this.data) return
    for (let i = 0; i < this.data.locations.length; i++) {
      let loc = this.data.locations[i]
      this.editor.markText (
        loc.c.begin, loc.c.end,
        {className: loc.color}
      )
      this.coreTab.colorLines (loc.core.begin.line, loc.core.end.line, loc.color)
    }

  }
}


class TabCore extends TabReadOnly {
  constructor (title) {
    super(title)

    this.tooltip = $(document.createElement('div'))
    this.tooltip.addClass('tooltip')
    this.tooltip.appendTo(this.content)
    this.tooltipVisible = false

    this.editor.setOption('mode', 'text/x-core')

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
      let pos = this.editor.coordsChar({left: e.pageX,top: e.pageY})
      let token = this.editor.getTokenAt(pos)

      // If tooltip is still visible, remove it
      if (this.tooltipVisible) {
        this.tooltip.removeClass('tooltip-visible')
        this.tooltipVisible = false
      }

      // Show tooltip for keywords
      if (token.type === 'keyword') {
        switch (token.string) {
          default:
            return;
          case 'strong':
          case 'weak':
          case 'pure':
            break;
        }
        this.tooltip.addClass('tooltip-visible')
        this.tooltip.css({left: e.pageX, top: e.pageY})
        this.tooltip.text(token.string)
        this.tooltipVisible = true
      }
    })
  }


  clear() {
    this.editor.eachLine((line) => {
      this.editor.removeLineClass(line, 'background')
    })
  }

}
