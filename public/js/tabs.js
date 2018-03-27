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
  updateMemory (s) {}
  highlight(s) {}
  fit() {}

}

class TabHelp extends Tab {
  constructor() {
    super('Help')
    this.dom.addClass('help')
    $.ajax({
      url: 'help.html',
      type: 'GET',
      success: (data) => this.dom.append(data)
    })
  }
}

class TabInteractive extends Tab {
  constructor(title) {
    super(title)

    let toolbar = $('<div class="toolbar"></div>')
    toolbar.attr('align', 'right')

    this.step = $('<div class="btn inline">step</div>')
    toolbar.append(this.step)

    let restart = $('<div class="btn inline">restart</div>')
    toolbar.append(restart)

    let hide_tau_btn = $('<div class="btn inline">show tau steps</button>')
    toolbar.append(hide_tau_btn)
    this.hide_tau = true

    let container = $('<div align="center" class="graph"></div>')

    this.dom.append(toolbar)
    this.dom.append(container)

    // Setup Graph Network
    let options = {
      nodes: {
        shape: 'dot',
        size: 10,
        shapeProperties: {
          borderRadius: 2
        },
        color: {
          border: '#5f5f5f',
          background: '#5f5f5f',
          highlight: {
            border: '#7f7f7f',
            background: '#7f7f7f'
          }
        },
        font: {
          align: 'left'
          //color: '#f1f1f1'
        },
        fixed: true
      },
      edges: {
        arrows: {to: true},
        font: {
          background: '#ffffff',
          color: '#5f5f5f',
        },
      },
      groups: {
        leaf: {
          color: {
            background: '#044777',
            border: '#044777'
          }
        }
      },
      layout: {
        hierarchical: {
          enabled: true,
          levelSeparation: 90,
          nodeSpacing: 200
        }
      },
      interaction: {
        navigationButtons: true,
        //keyboard: true,
        selectable: true,
        selectConnectedEdges: false
      }
    }
    let graph = {nodes: this.nodes, edges: this.edges }
    this.network = new vis.Network(container[0], graph, options);

    this.step.on('click', () => {
      let selection = this.network.getSelection()
      if (selection.nodes && selection.nodes.length > 0) {
        this.doStep(this.nodes.get(selection.nodes[0]))
      }
      // If initial step
      let ns = this.nodes.get()
      if (ns.length == 1)
        this.doStep(ns[0])
    })

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
          this.step.disable(true)
          if (active.group && active.group == 'leaf') {
            // do a step
            this.doStep(active)
          } else if (active.loc) {
            // show mem and select locations
            ui.clear()
            ui.mark(ui.source.getLocation(active.loc.begin, active.loc.end))
            if (active.mem)
              ui.updateMemory(active.mem)
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

  doStep(active) {
    if (active) {
      // do a step
      ui.state.interactive = {
        state: active.state,
        active: active.id
      }
      ui.request('Step', (data) => {
        this.attachTree(active.id, data.interactive.steps)
      })
    } else {
      console.log('error: node '+active+' unknown')
    }
  }

  nodeLabel(str) {
    if (str == 'Step_eval(first operand of a Create)')
      return 'Eval first operand of create'
    if (str == 'Step_eval(Esseq)')
      return 'Eval strong sequencing'
    if (str == 'Step_eval(Ewseq)')
      return 'Eval weak sequencing'
    if (str == 'Step_eval(Epure)')
      return 'Eval pure expression'
    if (str == 'Step_tau(End)')
      return 'Non deterministic choice'
    return str
  }

  attachTree(pointId, tree) {
    // Update tree nodes
    tree.nodes.map((n) => n.label = this.nodeLabel(n.label))
    // Get trees
    let leafNodeId = null
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
    tree.nodes.map(function (n) {
      nodes.add(n)
      if (!is_tau(n.id)) no_tau_nodes.add(n)
      if (n.state) leafNodeId = n.id
    })
    tree.edges.map(function (e) { edges.add(e) })
    tree.edges.map(function (e) {
      if (!is_tau(e.to))
        no_tau_edges.add({from: getNoTauParent(e.to), to: e.to})
    })
    // If found a leaf
    if (leafNodeId) {
      // Focus
      this.network.focus(leafNodeId)
      // Select last leaf node
      this.network.selectNodes([leafNodeId])
      this.step.disable(false)
    } else {
      this.network.focus(tree.nodes[0])
    }
  }

  fit() {
    this.network.setData({nodes: this.nodes, edges: this.edges})
    this.network.fit()
    this.network.redraw()
  }

  highlight() {
    this.network.unselectAll()
  }

}

class TabMemory extends Tab {
  constructor(title) {
    super(title)

    let container = $('<div align="center" class="graph"></div>')
    this.dom.append(container)

    // Setup Graph Network
    let options = {
      nodes: {
        shape: 'box',
        shapeProperties: {
          borderRadius: 3
        }
      },
      edges: {
        arrows: {to: true},
        smooth: {
          forceDirection: "none"
        }
      },
      interaction: {
        navigationButtons: true
      },
      physics: {
        barnesHut: {
          springLength: 200
        }
      }
    }
    let graph = {nodes: ui.state.mem.nodes, edges: ui.state.mem.edges }
    this.network = new vis.Network(container[0], graph, options);
  }

  updateMemory (state) {
    this.network.setData(state.mem)
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
      ui.currentView.state.dirty = true;
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
    this.setValue(s.pp.ail)
  }
}

class TabAil_AST extends TabAil {
  constructor() {
    super()
    this.setTitle('Ail (AST)')
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
    if (cc == null) cc = defaultCompiler // Global variable

    super(cc.name)

    this.editor.setOption('placeholder', '<Compilation failed...>')
    this.editor.setOption('mode', {name: "gas", architecture: "x86"})

    let toolbar   = $('<div class="toolbar flex"></div>')

    this.dropdown = $('<div class="btn dropdown">'+cc.name+'</div>')
    this.dropdown.append(this.createDropdownContent(this))

    this.options  = $('<input type="text" placeholder="Compiler options..." style="flex-grow: 1;">')

    this.options.on('blur', () => {
      this.compile(cc)
    })
    this.options.on('keypress', (e) => {
      if (e.which == 13) // Enter
        this.compile(cc)
    })

    toolbar.append(this.dropdown)
    toolbar.append(this.options)

    this.dom.prepend(toolbar)

    this.compile(cc)

    this.editor.on('cursorActivity', (doc) => this.markSelection(doc))

    this.cc = cc;
    this.locations = {}
  }

  createDropdownContent()
  {
    let dropdown = $('<div class="dropdown-content"></div>')
    for (let i = 0; i < compilers.length; i++) {
      let cc  = compilers[i]
      let opt = $('<div class="btn">' + cc.name + '</div>')
      opt.on('click', () => {
        this.compile(cc)
        this.dropdown.text(cc.name)
        this.setTitle(cc.name)
      })
      dropdown.append(opt)
    }
    return dropdown
  }

  update() {
    this.compile(this.cc)
  }

  updateLocations(lines) {
    this.locations = {}
    let locs = ui.currentView.state.locs;
    for (let i = locs.length - 1; i >= 0; i--) {
      let l0 = locs[i].c.begin.line+1;
      if (this.locations[0] || !lines[l0]) continue;
      let ln = locs[i].c.end.line+1;
      if (this.locations[ln] || !lines[ln]) continue;
      this.locations[l0] = {
        begin: Math.min(...lines[l0]),
        end:   Math.max(...lines[ln]),
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
        source: ui.source.getValue(),
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
        let lines = {}
        for (let i = 0; i < data.asm.length; i ++) {
          let asm = data.asm[i]
          if (asm.text)
            value += asm.text + '\n'
          if (asm.source && asm.source.line) {
            if (!lines[asm.source.line]) lines[asm.source.line] = []
            lines[asm.source.line].push(i)
          }
        }
        this.setValue(value)
        this.updateLocations(lines)
        this.highlight(ui.state)
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
  TabAil_AST,
  TabExecution,
  TabInteractive,
  TabMemory,
  TabConsole,
  TabHelp,
  TabAsm
}

function createTab(title) {
  return new Tabs['Tab'+title]()
}

function instanceOf(tab, title) {
  return tab instanceof Tabs['Tab'+title]
}
