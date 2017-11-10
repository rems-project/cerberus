'use_strict'

/* Generic Tab */
class Tab {
  constructor(title) {
    this.parent = null

    this.dom         = $('#tab-template').clone().contents()
    this.dom.content = $('<div class="tab-content"></div>')

    this.setTitle(title)
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

  // Dummy methods to be overwriten
  refresh () {}
  mark (loc) {}
  clear ()   {}
  update ()  {}
  highlight() {}

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
      ui.currentView.highlight()
      this.skipCursorEvent = true
    })

    // CodeMirror overwrites 'click' events
    this.editor.on('mousedown', () => {
      ui.currentView.highlight()
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
    this.setActive()
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
    if (!ui.colour_cursor) return;
    let from = doc.getCursor('from')
    let to   = doc.getCursor('to')
    ui.currentView.markSelection(this.getLocation(from, to))
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
      ui.currentView.dirty = true;
      //ui.currentView.clear()
    })
    // No close button
    this.dom.children('.close').hide()
  }

  getLocation(from, to) {
    let locations = ui.currentView.data.locs;
    for (let i = 0; i < locations.length; i++) {
      let loc = locations[i]
      if ((loc.c.begin.line < from.line ||
          (loc.c.begin.line == from.line && loc.c.begin.ch <= from.ch))
        && (loc.c.end.line > to.line ||
          (loc.c.end.line == to.line && loc.c.end.ch > to.ch)))
        return loc
    }
    return null
  }

  mark(loc) {
    this.editor.markText (loc.c.begin, loc.c.end, {className: getColor(loc.color)})
  }

  highlight() {
    let locations = ui.currentView.data.locs;
    for (let i = 0; i < locations.length; i++) {
      this.mark(locations[i])
    }
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

  update() {
    this.setValue(ui.currentView.data.cabs)
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

  update() {
    this.setValue(ui.currentView.data.ail)
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
    let locations = ui.currentView.data.locs
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

  highlight() {
    let locations = ui.currentView.data.locs;
    for (let i = locations.length - 1; i >= 0; i--) {
      this.mark(locations[i])
    }
  }

  update() {
    this.setValue(ui.currentView.data.core)
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

    toolbar.append(this.dropdown)
    toolbar.append(this.options)

    this.dom.content.addClass('tab-compiler')
    this.dom.content.prepend(toolbar)

    this.compile(cc)

    this.thanks = $(document.createElement("div"))

    let close = $(document.createElement("a"))
    close.attr("title", "Remove me!")
    close.addClass("remove-panel")
    close.text("✖")
    CodeMirror.on(close, "click", () => this.thanks.remove())

    let label = $(document.createElement("span"))
    label.text("I'm panel n°" + "blah")

    this.thanks.append(close)
    this.thanks.append(label)
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
    let locs = ui.currentView.data.locs;
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

  highlight() {
    let locs = ui.currentView.data.locs;
    for (let i = locs.length - 1; i >= 0; i--) {
      this.mark(locs[i])
    }
  }

  compile (cc) {
    ui.wait()
    $.ajax({
      headers: {Accept: 'application/json'},
      url: 'https://gcc.godbolt.org/api/compiler/'+cc.id+'/compile',
      type: 'POST',
      data: ui.currentView.getValue(),
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
        if (ui.colour) this.highlight()
        ui.done()
      }
    })
  }

}
