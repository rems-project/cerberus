'use_strict'

/* Generic Tab */
class Tab {
  constructor(title) {
    this.dom = $('<div class="tab-content"></div>')
    this.setTitle(title)
  }

  setTitle (title) {
    this.title = title
    this.dom.children('.title').text(title)
  }

  // Dummy methods to be overwritten
  refresh () {}
  mark (loc) {}
  clear ()   {}
  update (s)  {}
  highlight(s) {}

}

class TabInteractive extends Tab {
  constructor(title) {
    super(title)

    this.dom.addClass('graph')
    this.dom.attr('align', 'right')

    let restart = $('<button id="restart">restart</button>')
    this.dom.append(restart)

    this.hide_tau = false
    let hide_tau_btn = $('<button>hide tau steps</button>')
    this.dom.append(hide_tau_btn)

    let container = $('<div align="center" class="svg"></div>')
    this.dom.append(container)

    // Setup Graph Network
    let options = {
      nodes: {
        shape: 'box',
        shapeProperties: {
          borderRadius: 6
        },
        fixed: true
      },
      edges: {
        arrows: {to: true}
      },
      groups: {
        leaf: {
          color: 'rgb(0, 255, 140)'
        }
      },
      layout: {
        hierarchical: {
          enabled: true,
          levelSeparation: 70,
          nodeSpacing: 200
        }
      },
      interaction: {
        dragNodes: false,
        navigationButtons: true
      }
    }
    let graph = {nodes: this.nodes, edges: this.edges }
    this.network = new vis.Network(container[0], graph, options);

    restart.on('click', () => {
      ui.state.steps.edges.clear()
      ui.state.steps.nodes.clear()
      ui.state.steps.hide_tau.edges.clear()
      ui.state.steps.hide_tau.nodes.clear()
      ui.state.interactive = null
      ui.request('Step', (data) => {
        ui.currentView.mergeState(data)
        ui.currentView.startInteractive()
        this.network.fit()
      })
    })

    hide_tau_btn.on('click', () => {
      this.hide_tau = !this.hide_tau
      if (this.hide_tau)
        hide_tau_btn.text('show tau steps')
      else
        hide_tau_btn.text('hide tau steps')
      this.network.setData({nodes: this.nodes, edges: this.edges})
    })

    this.network.on('click', (arg) => {
      // if one node is selected
      if (arg && arg.nodes && arg.nodes.length == 1) {
        let active = this.nodes.get(arg.nodes[0])
        if (active) {
          if (active.group && active.group == 'leaf') {
            // do a step
            ui.state.interactive = {
              state: active.state,
              active: active.id
            }
            ui.request('Step', (data) => {
              this.attachTree(active.id, data.interactive.steps)
            })
          } else if (active.loc) {
            // show mem and select locations
            let loc = ui.source.getLocation(active.loc.begin, active.loc.end)
            ui.clear()
            ui.mark(loc)
          } else {
            // just clear and highlight everything
            ui.clear()
            ui.highlight()
          }
        }
      }
    })
  }

  get nodes() {
    return this.hide_tau ? ui.state.steps.hide_tau.nodes
                         : ui.state.steps.nodes
  }

  get edges() {
    return this.hide_tau ? ui.state.steps.hide_tau.edges
                         : ui.state.steps.edges
  }

  attachTree(pointId, tree) {
    // Get trees
    let nodes = ui.state.steps.nodes
    let edges = ui.state.steps.edges
    let no_tau_nodes = ui.state.steps.hide_tau.nodes
    let no_tau_edges = ui.state.steps.hide_tau.edges
    // TODO: this is bad!
    let is_tau = (nId) => {
      let n = nodes.get(nId)
      if (n && n.label.includes("tau"))
        return !n.label.includes("End")
      return false
    }
    let getParent = (nId) => {
      let es = edges.get()
      for (let i = 0; i < es.length; i++) {
        if (es[i].to == nId)
          return es[i].from
      }
      return null
    }
    let getNoTauParent = (nId) => {
      let fromId = getParent(nId)
      if (fromId && is_tau(fromId))
        return getNoTauParent(fromId)
      return fromId
    }
    // Update current point
    let point = nodes.get(pointId)
    delete point.group
    delete point.state
    nodes.remove(pointId)
    no_tau_nodes.remove(pointId)
    nodes.add(point)
    no_tau_nodes.add(point)
    // Add nodes and edges of the new tree
    tree.nodes.forEach(function (n) {
      nodes.add(n)
      if (!is_tau(n.id))
        no_tau_nodes.add(n)
    })
    tree.edges.forEach(function (e) { edges.add(e) })
    tree.edges.forEach(function (e) {
      if (!is_tau(e.to))
        no_tau_edges.add({from: getNoTauParent(e.to), to: e.to})
    })
    // Focus
    this.network.focus(tree.nodes[0].id)
  }

  highlight() {
    this.network.unselectAll()
  }
}

class TabMemory extends Tab {
  constructor(title) {
    super(title)

    /*
    this.dom.content = $('#interactive-template').clone().contents()
    this.dom.append(this.dom.content)

    // Setup Graph Network
    let options = {
      nodes: {
        shape: 'box',
        shapeProperties: {
          borderRadius: 6
        }
      },
      edges: {
        arrows: {to: true}
      }
    }
    this.nodes = new vis.DataSet([])
    this.edges = new vis.DataSet([])
    let graph = {nodes: this.nodes, edges: this.edges }
    let container = this.dom.content.children('.svg')[0]
    this.network = new vis.Network(container, graph, options);

    */
  }

  getAllocationValue(state, alloc) {
    let map = state.mem.bytemap
    if (map[alloc.base]) {
      let val = ''
      let base = parseInt(alloc.base)
      let size = parseInt(alloc.size)
      for (let i = base; i < base + size; i++) {
        val = map[i][1] + parseInt(val, 16).toString()
      }
      return val
    }
    return 'undef'
  }

  update (state) {
    /*
    let nodes = []
    for (let i = 0, alloc = state.mem.allocations[i];
          alloc;
          i++, alloc = state.mem.allocations[i] ) {
      let label = i+': ' + this.getAllocationValue(state, alloc)
      nodes.push({id: i, label: label})
    }
    let graph = {nodes: nodes, edges: []}
    this.network.setData(graph)
    */
  }
}

/* Tab with CodeMirror editor */
class TabEditor extends Tab {
  constructor(title, source) {
    super(title)
    this.dom.addClass('editor')

    this.editor = CodeMirror (this.dom[0], {
      styleActiveLine: true,
      lineNumbers: true,
      matchBrackets: true,
      tabSize: 2,
      smartIndent: true,
      lineWrapping: true
    })

    this.editor.on('blur', (doc) => {
      ui.highlight()
      this.skipCursorEvent = true
    })

    // CodeMirror overwrites 'click' events
    this.editor.on('mousedown', () => {
      ui.highlight()
      this.skipCursorEvent = true
    })

    this.editor.on('dblclick', (doc) => {
      this.skipCursorEvent = false
      this.markSelection(doc)
    })

    this.editor.on('viewportChange', (doc) => {
      //console.log('view port change')
    })

    this.editor.on('refresh', (doc) => {
      //console.log('refresh')
    })

    this.editor.on('update', (doc) => {
      //console.log('update')
    })

    if (source) this.editor.setValue(source)
    this.skipCursorEvent = true
  }

  getValue() {
    return this.editor.getValue()
  }

  setValue(value) {
    this.editor.setValue(value)
    this.refresh()
  }

  appendValue(value) {
    this.setValue(this.getValue()+value)
  }

  colorLines(i, e, color) {
    for (let k = i; k <= e; k++) {
      this.editor.removeLineClass(k, 'background')
      this.editor.addLineClass(k, 'background', 'color'+color)
    }
  }

  clear() {
    this.editor.eachLine((line) => {
      this.editor.removeLineClass(line, 'background')
    })
  }

  markSelection(doc) {
    // Just got focus or a click event
    if (this.skipCursorEvent) {
      this.skipCursorEvent = false
      return;
    }
    if (!ui.settings.colour_cursor) return;
    let from = doc.getCursor('from')
    let to   = doc.getCursor('to')
    ui.mark(this.getLocation(from, to))
  }

  refresh () {
    this.editor.refresh()
  }

  showTooltip(content) {
    function elt(tagname, cls /*, ... elts*/) {
      let e = document.createElement(tagname);
      if (cls) e.className = cls;
      for (let i = 2; i < arguments.length; ++i) {
        let elt = arguments[i];
        if (typeof elt == "string") elt = document.createTextNode(elt);
        e.appendChild(elt);
      }
      return e;
    }
    function makeTooltip(x, y, content) {
      let node = elt("div", "tooltip", content);
      node.style.left = x + "px";
      node.style.top = y + "px";
      document.body.appendChild(node);
      // Shifting X
      let minWidth = 300
      if (node.clientWidth < minWidth) {
        let dx = minWidth - node.clientWidth
        node.style.left = (x - dx - 10) + "px"
      }
      // Shifting Y
      let minHeight = 200
      let maxY = y + node.clientHeight
      if (document.body.clientHeight < maxY) {
        let maxHeight = document.body.clientHeight - y
        if (maxHeight < minHeight) {
          let dy = minHeight - maxHeight
          node.style.top = (y - dy - 10) + "px"
          maxHeight = minHeight
        }
        node.style.maxHeight = maxHeight + "px"
      }

      return node;
    }

    function clear() {
      if (tip.parentNode) fadeOut(tip)
      this.tooltip = null
      clearActivity()
    }

    let where = this.editor.cursorCoords()
    let tip = makeTooltip(where.right + 1, where.bottom, content)
    let mouseOnTip = false
    let cmIsBlur = false

    CodeMirror.on(tip, "mousemove", () => {
      console.log('on move');
      mouseOnTip = true;
    })

    CodeMirror.on(tip, "mousedown", (e) => {
      let x0 = e.clientX
      let y0 = e.clientY
      let pos = $(tip).position()
      function moveTip(e) {
        let dx = e.clientX - x0
        let dy = e.clientY - y0
        tip.style.cursor = 'move'
        tip.style.left = (dx + pos.left) + "px";
        tip.style.top = (dy + pos.top) + "px";
      }
      function stop(e) {
        tip.style.cursor = 'auto'
        $(document).off('mousemove')
        $(document).off('mouseup')
      }
      tip.style.cursor = 'move'
      $(document).on('mousemove', e => moveTip(e));
      $(document).on('mouseup', e => stop(e));
    })

    function onEditorActivity(cm, f) {
      cm.on("cursorActivity", f)
      cm.on("scroll", f)
      cm.on("blur", () => {
        console.log('blur');
        cmIsBlur = true
        if (!mouseOnTip) f()
      })
      cm.on("setDoc", f)
      return function() {
        cm.off("cursorActivity", f)
        cm.off("scroll", f)
        cm.off("blur", f)
        cm.off("setDoc", f)
      }
    }

    let clearActivity = onEditorActivity(this.editor, () => {
      if (tip.parentNode) fadeOut(tip)
      this.tooltip = null
      clearActivity()
    })

    CodeMirror.on(tip, "mouseout", (e) => {
      if (!CodeMirror.contains(tip, e.relatedTarget || e.toElement)) {
        console.log('outside');
        mouseOnTip = false;
      }
      if (cmIsBlur) this.editor.focus()

    })

    this.tooltip = tip
  }
}

/* ReadOnly Editor */
class TabReadOnly extends TabEditor {
  constructor (title, source) {
    super(title, source)
    this.editor.setOption ('readOnly', true)
  }
}

class TabExecution extends TabReadOnly {
  constructor () {
    super('Execution')
  }
  update (s) {
    this.setValue(s.result) // TODO: change to execution result
  }
}

class TabConsole extends TabReadOnly {
  constructor () {
    super('Console')
  }
  update (s) {
    this.setValue(s.console)
  }
}

/* Tab C source */
class TabSource extends TabEditor {
  constructor(title, source) {
    super(title, source)
    this.isClosable = false
    this.editor.setOption('mode', 'text/x-csrc')
    this.editor.on('cursorActivity', (doc) => this.markSelection(doc))

    this.editor.on('change', () => {
      ui.currentView.dirty = true;
      //ui.currentView.clear()
    })
  }

  getLocation(from, to) {
    let locations = ui.currentView.state.locs;
    for (let i = 0; i < locations.length; i++) {
      let loc = locations[i]
      if ((loc.c.begin.line < from.line ||
          (loc.c.begin.line == from.line && loc.c.begin.ch <= from.ch))
        && (loc.c.end.line > to.line ||
          (loc.c.end.line == to.line && loc.c.end.ch >= to.ch)))
        return loc
    }
    return null
  }

  mark(loc) {
    this.editor.markText (loc.c.begin, loc.c.end, {className: getColor(loc.color)})
  }

  highlight(s) {
    for (let i = 0; i < s.locs.length; i++)
      this.mark(s.locs[i])
  }

  clear() {
    let marks = this.editor.getAllMarks()
    for (let i = 0; i < marks.length; i++)
      marks[i].clear()
  }
}

/* Tab Cabs */
class TabCabs extends TabReadOnly {
  constructor() {
    super('Cabs')
    this.editor.setOption('mode', 'text/x-ast-dump')
    this.editor.setOption('placeholder', '<Cabs elaboration failed...>')
  }

  update(s) {
    this.setValue(s.ast.cabs)
  }
}

/* Tab Cabs */
class TabAil extends TabReadOnly {
  constructor() {
    super('Ail')
    this.editor.setOption('mode', 'text/x-ast-dump')
    this.editor.setOption('placeholder', '<Ail elaboration failed...>')

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

        let re = /\[\d(\.\d)*(#\d)?\]/
        if (re.test(word))
          return "std"
      }
    }, { opaque: true, priority: 1000 }
    )

    this.editor.getWrapperElement().addEventListener('mousedown', (e) => {
      let edom = $(e.target);
      if (edom.hasClass('cm-std')) {
        if (this.tooltip && e.target.tooltipVisible) {
          fadeOut(this.tooltip)
          e.target.tooltipVisible = false
        } else {
          this.showTooltip(getSTDSection(e.target.textContent).data[0]);
          e.target.tooltipVisible = true;
        }
      }
    })

  }

  update(s) {
    this.setValue(s.ast.ail)
  }
}

/* Tab Core */
class TabCore extends TabReadOnly {
  constructor () {
    super('Core')

    this.editor.setOption('mode', 'text/x-core')
    this.editor.setOption('placeholder', '<Core elaboration failed...>')
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

        let re = /{-#\d(\.\d)*(#\d)?/
        if (re.test(word))
          return "std"
      }
    }, { opaque: true, priority: 1000 }
    )

    this.editor.getWrapperElement().addEventListener('mousedown', (e) => {
      let edom = $(e.target);
      if (edom.hasClass('cm-std')) {
        if (this.tooltip && e.target.tooltipVisible) {
          fadeOut(this.tooltip)
          e.target.tooltipVisible = false
        } else {
          this.showTooltip(getSTDSection(e.target.textContent).data[0]);
          e.target.tooltipVisible = true;
        }
      }
    })

  }

  getLocation(from, to) {
    let locations = ui.currentView.state.locs
    for (let i = 0; i < locations.length; i ++) {
      let loc = locations[i]
      if (loc.core.begin.line <= from.line && loc.core.end.line >= to.line)
        return loc
    }
    return null
  }

  mark(loc) {
    this.colorLines (loc.core.begin.line, loc.core.end.line, loc.color)
  }

  highlight(s) {
    for (let i = s.locs.length - 1; i >= 0; i--)
      this.mark(s.locs[i])
  }

  update(s) {
    this.setValue(s.pp.core)
  }

}

class TabAsm extends TabReadOnly {
  constructor(cc) {
    super(cc.name)

    this.editor.setOption('placeholder', '<Compilation failed...>')
    this.editor.setOption('mode', {name: "gas", architecture: "x86"})

    let toolbar   = $(document.createElement("div"))

    this.dropdownActive = $('<a href="#" class="dropbtn dropdown-toggle">'
                          + cc.name + '</a>')
    this.dropdown = $('<div class="dropdown"></div>')
    this.dropdown.append(this.dropdownActive)
    this.dropdown.append(this.createDropdownContent(this))

    this.options  = $('<input type="text" placeholder="Compiler options...">')

    this.options.on('blur', () => {
      this.compile(cc)
    })
    this.options.on('keypress', (e) => {
      if (e.which == 13) // Enter
        this.compile(cc)
    })

    toolbar.append(this.dropdown)
    toolbar.append(this.options)

    this.dom.addClass('tab-compiler')
    this.dom.prepend(toolbar)

    this.compile(cc)

    //this.thanks = $(document.createElement("div"))

    //let close = $(document.createElement("a"))
    //close.attr("title", "Remove me!")
    //close.addClass("remove-panel")
    //close.text("✖")
    //CodeMirror.on(close, "click", () => this.thanks.remove())

    //let label = $(document.createElement("span"))
    //label.text("I'm panel n°" + "blah")

    //this.thanks.append(close)
    //this.thanks.append(label)
    //this.editor.addPanel(this.thanks[0], {position: "bottom", stable: true});

    this.editor.on('cursorActivity', (doc) => this.markSelection(doc))

    this.cc = cc;
    this.lines = {}
    this.locations = {}
  }

  createDropdownContent()
  {
    let dropdown = $('<div class="dropdown-content"></div>')
    for (let i = 0; i < compilers.length; i++) {
      let cc  = compilers[i]
      let opt = $('<a href="#">' + cc.name + '</a>')
      opt.on('click', () => {
        this.compile(cc)
        this.dropdownActive.text(cc.name)
        this.setTitle(cc.name)
      })
      dropdown.append(opt)
    }
    return dropdown
  }

  update() {
    this.compile(this.cc)
  }

  updateLocations() {
    this.locations = {}
    let locs = ui.currentView.state.locs;
    for (let i = locs.length - 1; i >= 0; i--) {
      let l = locs[i].c.begin.line+1;
      if (this.locations[l] || !this.lines[l])
        continue;
      this.locations[l] = {
        begin: Math.min(...this.lines[l]),
        end: Math.max(...this.lines[l]),
        color: locs[i].color,
        source: locs[i]
      }
    }
  }


  getLocation(from, to) {
    for (let i = 0; i < this.locations.length; i++) {
      if (this.locations[i].begin <= from.line && this.locations[i].end >= to.line)
        return this.locations[i].source
    }
    return null
  }

  mark(loc) {
    let l = this.locations[loc.c.begin.line+1]
    if (l) this.colorLines (l.begin, l.end, l.color)
  }

  highlight(s) {
    for (let i = s.locs.length - 1; i >= 0; i--)
      this.mark(s.locs[i])
  }

  compile (cc) {
    ui.wait()
    $.ajax({
      headers: {Accept: 'application/json'},
      contentType: "application/json; charset=utf-8",
      url: 'https://gcc.godbolt.org/api/compiler/'+cc.id+'/compile',
      type: 'POST',
      data: JSON.stringify ({
        source: ui.currentView.getValue(),
        compiler: cc.id,
        options: {
          userOptions: this.options.val(),
          compilerOptions: {},
          filters: {
            binary: false,
            execute: false,
            labels: true,
            directives: true,
            commentOnly: true,
            trim: false,
            intel: true,
            demangle: true
          }
        }
      }),
      success: (data, status, query) => {
        console.log(data)
        let value = ''
        for (let i = 0; i < data.asm.length; i ++) {
          let asm = data.asm[i]
          value += asm.text + '\n'
          if (asm.source && asm.source.line) {
            if (!this.lines[asm.source.line])
              this.lines[asm.source.line] = []
            this.lines[asm.source.line].push(i)
          }
        }
        this.setValue(value)
        this.updateLocations()
        this.highlight()
        ui.done()
      }
    })
  }

}

/* Concrete Tabs Factory */
const Tabs = {
  TabSource,
  TabCabs,
  TabAil,
  TabCore,
  TabExecution,
  TabInteractive,
  TabMemory,
  TabConsole
}

function createTab(title) {
  return new Tabs['Tab'+title]()
}

function instanceOf(tab, title) {
  return tab instanceof Tabs['Tab'+title]
}
