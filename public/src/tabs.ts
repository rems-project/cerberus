import $ from 'jquery'
import _ from 'lodash'
import CodeMirror from 'codemirror'
import { Node, Edge, Graph } from './graph';
import Util from './util'
import Common from './common'
import UI from './ui'
import Viz from './js/viz.js'

namespace Tabs {

/* Generic  */
export abstract class Tab {
  title: string | undefined
  dom: JQuery<HTMLElement>
  ee: Common.EventEmitter

  constructor(title: string, ee: Common.EventEmitter) {
    this.dom = $('<div class="tab-content"></div>')
    this.ee = ee
    this.setTitle(title)
  }

  setTitle (title: string): void {
    this.title = title
    this.dom.children('.title').text(title)
  }

  /** Called when size or visibility of HTML changes */
  refresh () {}

  /** Update value (receives current state) */
  update(s: Readonly<Common.State>) {}

  /** Update initial value (receives current state) */
  initial(s: Readonly<Common.State>) { this.update(s) }
  
  /** Implemented by GoldenLayout when tab content is attached to it */
  setActive () {}
}

export class Help extends Tab {
  constructor(ee: Common.EventEmitter) {
    super('Help', ee)
    this.dom.addClass('page')
    $.ajax({
      url: 'help.html',
      type: 'GET',
      success: (data) => this.dom.append(data)
    })
  }
}

export class Preferences extends Tab {
  constructor (ee: Common.EventEmitter) {
    super('Prefernces', ee)
    this.dom.addClass('page') // maybe change this
    $.ajax({
      url: 'preferences.html',
      type: 'GET',
      success: (data) => this.dom.append(data)
    })
  }
}

export class Interactive extends Tab {
  constructor(ee: Common.EventEmitter) {
    super('Interactive', ee)

    const toolbar = $('<div class="toolbar adjust-height"></div>')

    const stepBtn = $('<div class="btn inline">Step</div>')
    const restartBtn = $('<div class="btn inline">Restart</div>')

    const optionsBtn = $('<div class="btn dropdown"><span>Options</span></div>')
    const dropdown_options = $('<div class="dropdown-content"></div>')

    const hide_tauCBox = $('<input type="checkbox">')
    const hide_tauBtn = $('<div class="btn">Suppress tau transitions</div>')
    hide_tauBtn.prepend(hide_tauCBox)
    const skip_tauCBox = $('<input type="checkbox">')
    const skip_tauBtn = $('<div class="btn">Skip tau transitions</div>')
    skip_tauBtn.prepend(skip_tauCBox)
    const eager_memCBox = $('<input type="checkbox">')
    const eager_memBtn = $('<div class="btn">Skip to the next memory action</div>')
    eager_memBtn.prepend(eager_memCBox)

    dropdown_options.attr('align', 'left')
    dropdown_options.append(hide_tauBtn)
    dropdown_options.append(skip_tauBtn)
    dropdown_options.append(eager_memBtn)
    optionsBtn.append(dropdown_options)

    toolbar.append(optionsBtn)
    toolbar.append(restartBtn)
    toolbar.append(stepBtn)

    const controls = $('<div class="toolbar"></div>')
    const zoomIn = $('<div class="btn inline" type="button">Zoom In</div>')
    const reset = $('<div class="btn inline" type="button">Reset</div>')
    const range = $('<input class="range" type="range" step="0.05" min="0.1" max="2">')
    const zoomOut = $('<div class="btn inline" type="button">Zoom Out</div>')
    controls.append(zoomIn)
    controls.append(zoomOut)
    controls.append(range)
    controls.append(reset)

    const container = $('<div align="center" class="graph"></div>')
    this.dom.append(controls)
    this.dom.append(toolbar)
    this.dom.append(container)

    const updateFlags = (state: Readonly<Common.State>) => {
      hide_tauCBox.prop('checked', state.hide_tau)
      skip_tauCBox.prop('checked', state.skip_tau)
      eager_memCBox.prop('checked', state.eager_mem)
    }
    const toggle = (flag: string) => {
      ee.once((state: Common.State) => {
        state[flag] = !state[flag]
        // if we don't skip tau we should show the transitions
        state.hide_tau = state.skip_tau && state.hide_tau
        updateFlags(state)
        ee.emit('updateDOT')
      })
    }

    hide_tauBtn.on('click', () => toggle('hide_tau'))
    skip_tauBtn.on('click', () => toggle('skip_tau'))
    eager_memBtn.on('click', () => toggle('eager_mem'))
    ee.once((state: Common.State) => updateFlags(state))

    stepBtn.on('click', () => {
      ee.once((state: Readonly<Common.State>) => {
        const active = _.find(state.graph.nodes, n => n.selected)
        if (active)
          ee.emit('step', active.id)
        else
          alert('No selected node.')
      })
    })
    restartBtn.on('click', () => ee.emit('resetInteractive'))

    const updateGraph = (state: Readonly<Common.State>) => {
      container.empty()
      container.append(Viz(state.dotExecGraph))
      const svg = container.find('svg')
      svg.addClass('panzoom')
      // @ts-ignore
      svg.panzoom({
        $zoomIn: zoomIn,
        $zoomOut: zoomOut,
        $zoomRange: range,
        $reset: reset,
        increment: 0.1,
        minScale: 0.1,
        maxScale: 2
      })
      // Check if needs to span down
      const svgHeight = svg.height()
      const containerHeight = container.height()
      if (svgHeight && containerHeight) {
        const delta = containerHeight / 2 - svgHeight
        if (delta < 0) {
          // @ts-ignore
          svg.panzoom('pan', 0, delta, '{ relative: true }')
        }
      }
      // Zoom using the mouse
      container.off() // remove all previous events
      container.on('mousewheel.focal', (e) => {
        e.preventDefault()
        // @ts-ignore
        let delta = e.delta || e.originalEvent.wheelDelta
        // @ts-ignore
        let zoomOut = delta ? delta < 0 : e.originalEvent.deltaY > 0
        // @ts-ignore
        svg.panzoom('zoom', zoomOut, { increment: 0.01, animate: false, focal: e })
      })
    }

    ee.on('highlight', this, this.highlight)
    ee.on('updateGraph', this, (s: Common.State) => updateGraph(s))
  }
  
  highlight() {
    //this.network.unselectAll()
  }

  refresh() {
    //this.network.redraw()
  }

}

class Memory extends Tab {
  constructor(ee: Common.EventEmitter) {
    super('Memory', ee)

    const container = $('<div align="center" class="graph"></div>')
    const controls = $('<div class="toolbar"></div>')
    const zoomIn = $('<div class="btn inline" type="button">Zoom In</div>')
    const reset = $('<div class="btn inline" type="button">Reset</div>')
    const range = $('<input class="range" type="range" step="0.05" min="0.1" max="2">')
    const zoomOut = $('<div class="btn inline" type="button">Zoom Out</div>')
    controls.append(zoomIn)
    controls.append(zoomOut)
    controls.append(range)
    controls.append(reset)
    this.dom.append(controls)
    this.dom.append(container)

    // Initial zoom and position
    let scale0 = 1
    let x0 = 0, y0 = 0

    ee.on('updateMemory', this, (s:Common.State) => {
      container.empty()
      container.append(Viz(s.dotMem))
      const svg = container.find('svg')
      svg.addClass('panzoom')
      // @ts-ignore
      svg.panzoom({
        $zoomIn: zoomIn,
        $zoomOut: zoomOut,
        $zoomRange: range,
        $reset: reset,
        increment: 0.1,
        minScale: 0.1,
        maxScale: 2
      })
      svg.on('panzoomzoom', (elem, panzoom, scale) => {
        scale0 = scale
      })
      svg.on('panzoompan', (elem, panzoom, x, y) => {
        x0 = x
        y0 = y
      })
      svg.on('panzoomreset', () => {
        scale0 = 1
        x0 = y0 = 0
      })
      // @ts-ignore
      svg.panzoom('pan', x0, y0)
      // @ts-ignore
      svg.panzoom('zoom', scale0)
    })
  }
  
}

/*  with CodeMirror editor */
export abstract class Editor extends Tab {
  protected editor: CodeMirror.Editor
  protected tooltip?: HTMLElement
  private skipCursorEvent: boolean

  constructor(title: string, source: string, ee: Common.EventEmitter) {
    super(title, ee)
    this.dom.addClass('editor')

    const config = <CodeMirror.EditorConfiguration> {
      styleActiveLine: true,
      lineNumbers: true,
      matchBrackets: true,
      tabSize: 2,
      smartIndent: true,
      lineWrapping: true
    }

    this.editor = CodeMirror (this.dom[0], config)

    this.editor.on('blur', (doc) => {
      this.ee.emit('highlight')
      this.skipCursorEvent = true
    })

    // CodeMirror overwrites 'click' events
    this.editor.on('mousedown', () => {
      this.ee.emit('highlight')
      this.skipCursorEvent = true
    })

    this.editor.on('dblclick', (ed) => {
      this.skipCursorEvent = false
      this.markSelection(ed.getDoc())
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
    ee.on('clear', this, this.clear)
  }

  getValue() {
    return this.editor.getValue()
  }

  setValue(value: string) {
    this.editor.setValue(value)
    this.refresh()
  }

  appendValue(value: string) {
    this.setValue(this.getValue()+value)
  }

  colorLines(i: number, e: number, color: string | number) {
    for (let k = i; k <= e; k++) {
      this.editor.removeLineClass(k, 'background')
      this.editor.addLineClass(k, 'background', 'color'+color)
    }
  }

  clear() {
    this.editor.getDoc().eachLine((line: CodeMirror.LineHandle) => {
      this.editor.removeLineClass(line, 'background')
    })
  }

  getLocation(from: Common.Point, to: Common.Point) {
    // TO BE OVERWRITTEN
    return undefined
  }

  markSelection(doc: CodeMirror.Doc) {
    // Just got focus or a click event
    if (this.skipCursorEvent) {
      this.skipCursorEvent = false
      return;
    }
    const from = doc.getCursor('from')
    const to   = doc.getCursor('to')
    const loc  = this.getLocation(from, to)
    if (loc) {
      this.ee.emit('clear')
      this.ee.emit('mark', loc)
    }
  }

  refresh () {
    this.editor.refresh()
  }

  showTooltip(content: HTMLElement) {
    function elt(tagname: string, cls: string, ...args: any []) {
      let e = document.createElement(tagname);
      if (cls) e.className = cls;
      for (let i = 0; i < args.length; ++i) {
        let elt = args[i];
        if (typeof elt == "string") elt = document.createTextNode(elt);
        e.appendChild(elt);
      }
      return e;
    }
    function makeTooltip(x: number, y: number, content: HTMLElement) {
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

    let where = this.editor.cursorCoords(true)
    //@ts-ignore WARN: CodeMirror.d.ts is missing .right
    let tip = makeTooltip(where.right + 1, where.bottom, content)
    let cmIsBlur = false

    CodeMirror.on(tip, "mousemove", () => {
      console.log('on move');
    })

    CodeMirror.on(tip, "mousedown", (e: MouseEvent) => {
      let x0 = e.clientX
      let y0 = e.clientY
      let pos = $(tip).position()
      function moveTip(e: MouseEvent): void {
        let dx = e.clientX - x0
        let dy = e.clientY - y0
        tip.style.cursor = 'move'
        tip.style.left = (dx + pos.left) + "px";
        tip.style.top = (dy + pos.top) + "px";
      }
      function stop(e: MouseEvent): void {
        tip.style.cursor = 'auto'
        $(document).off('mousemove')
        $(document).off('mouseup')
      }
      tip.style.cursor = 'move'
      $(document).on('mousemove', (e: any) => moveTip(e));
      $(document).on('mouseup', (e: any) => stop(e));
    })

    function onEditorActivity(cm: CodeMirror.Editor, f: (_: CodeMirror.Editor) => void) {
      cm.on("cursorActivity", f)
      cm.on("scroll", f)
      cm.on("blur", () => {
        console.log('blur');
        cmIsBlur = true
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
      if (tip.parentNode) Util.fadeOut(tip)
      this.tooltip = undefined
      clearActivity()
    })

    CodeMirror.on(tip, "mouseout", (e: MouseEvent) => {
      if (cmIsBlur) this.editor.focus()
    })

    this.tooltip = tip
  }
}

/* ReadOnly Editor */
export abstract class ReadOnly extends Editor {
  constructor (title: string, source: string, ee: Common.EventEmitter) {
    super(title, source, ee)
    this.editor.setOption ('readOnly', true)
  }
}

export class Implementation extends ReadOnly {
  constructor (ee: Common.EventEmitter) {
    super('Implementation Defined', '', ee)
    this.editor.setOption('placeholder', '<Download failed...>')
    this.editor.setOption('mode', {name: "ocaml"})
    $.ajax({
      url: 'assets/ocaml_implementation.ml',
      type: 'GET',
      success: (data) => this.setValue(data)
    })
  }
}

export class Execution extends ReadOnly {
  constructor (ee: Common.EventEmitter) {
    super('Execution', '', ee)
    ee.on('update', this, this.update)
    ee.on('updateExecution', this, this.update)
  }

  update (s: Common.State) : void {
    if (s.result == '') {
      this.setValue('')
      return
    }
    const values = s.result.split(/\nEND EXEC\[\d*\]\nBEGIN EXEC\[\d*\]\n/g)
      .map((s: string) => s.replace(/BEGIN EXEC\[\d*\]\n/, "").replace(/\nEND EXEC\[\d*\]/, ''))
      .sort()
    let result = ""
    let current : string | undefined = undefined
    let cnt = 0
    for (let i = 0; i < values.length; i++) {
      if (values[i] != current) {
        if (cnt > 0) {
          result += "BEGIN EXEC["+(i-cnt)+"-"+(i-1)+"]\n"
          result += current
          result += "\nEND EXEC["+(i-cnt)+"-"+(i-1)+"]\n"
        }
        current = values[i]
        cnt = 1;
      } else {
        cnt++
      }
    }
    if (cnt > 0) {
      let i = values.length
      result += "BEGIN EXEC["+(i-cnt)+"-"+(i-1)+"]\n"
      result += current
      result += "\nEND EXEC["+(i-cnt)+"-"+(i-1)+"]\n"
      cnt = 1;
    } 
    this.setValue(result)
  }
}

class Console extends ReadOnly {
  constructor (ee: Common.EventEmitter) {
    super('Console', '', ee)
    ee.on('update', this, this.update)
    ee.on('updateExecution', this, this.update) // in case of failures
  }

  update(s:Common.State) {
    const vs = s.console.split(':')
    if (vs.length > 2) {
      this.ee.emit('markError', parseInt(vs[1]))
      this.setValue(s.title() + ':' + _.join(_.drop(vs, 1), ':'))
    } else {
      this.setValue(s.console)
    }
  }
}

/*  C source */
export class Source extends Editor {
  constructor(title: string, source: string, ee: Common.EventEmitter) {
    super(title, source, ee)
    this.editor.setOption('gutters', ['error'])
    this.editor.setOption('mode', 'text/x-csrc')
    this.editor.on('cursorActivity', (ed) => this.markSelection(ed.getDoc()))

    this.editor.on('change', () => {
      ee.emit('dirty')
      ee.emit('clear')
    })
    ee.on('highlight', this, this.highlight)
    ee.on('mark', this, this.mark)
    ee.on('markError', this, this.markError)
    ee.on('markInteractive', this, this.markInteractive)
    ee.on('clear', this, this.clear)
  }

  getLocation(from: Common.Point, to: Common.Point) {
    return this.ee.once((s: Readonly<Common.State>) => {
      let locations = s.locs;
      for (let i = 0; i < locations.length; i++) {
        let loc = locations[i]
        if ((loc.c.begin.line < from.line ||
            (loc.c.begin.line == from.line && loc.c.begin.ch <= from.ch))
          && (loc.c.end.line > to.line ||
            (loc.c.end.line == to.line && loc.c.end.ch >= to.ch)))
          return loc
      }
      return null
    })
  }

  mark(loc: Common.Locations) {
    let options: CodeMirror.TextMarkerOptions = {
      className: Util.getColor(loc.color)
    }
    this.editor.getDoc().markText(loc.c.begin, loc.c.end, options)
  }

  markInteractive(loc: any, state: Readonly<Common.State>) {
    if (loc.c) {
      this.editor.getDoc().markText(loc.c.begin, loc.c.end, { className: Util.getColorByLocC(state, loc.c) })
    }
  }

  markError(l: number) {
    this.editor.setGutterMarker(l-1, 'error', $('<div class="syntax-error">✖</div>')[0])
  }

  highlight(s: Common.State) {
    for (let i = 0; i < s.locs.length; i++)
      this.mark(s.locs[i])
  }

  clear() {
    this.editor.clearGutter('error')
    let marks = this.editor.getDoc().getAllMarks()
    for (let i = 0; i < marks.length; i++)
      marks[i].clear()
  }
}

/*  Cabs */
class Cabs extends ReadOnly {
  constructor(ee: Common.EventEmitter) {
    super('Cabs', '', ee)
    this.editor.setOption('mode', 'text/x-ast-dump')
    this.editor.setOption('placeholder', '<Cabs elaboration failed...>')
    ee.on('update', this, this.update)
  }
  update(s:Common.State) {
    this.setValue(s.ast.cabs)
  }
}

/*  Ail */
class Ail extends ReadOnly {
  constructor(ee: Common.EventEmitter) {
    super('Ail', '', ee)
    this.editor.setOption('mode', 'text/x-ast-dump')
    this.editor.setOption('placeholder', '<Ail elaboration failed...>')

    this.editor.addOverlay({
      token: (stream: CodeMirror.StringStream) => {
        const rx_word: string = "\" "
        let ch = stream.peek()
        let word = ""
        if (_.includes(rx_word, ch) || ch === '\uE000' || ch === '\uE001') {
          stream.next()
          return undefined
        }
        while ((ch = stream.peek()) && !_.includes(rx_word, ch)){
          word += ch
          stream.next()
        }
        let re = /(\[|;)\d(\.\d)*(#\d)?(\]?)/
        if (re.test(word))
          return "std"
        return undefined
      }
    }, { opaque: true, priority: 1000 }
    )

    this.editor.getWrapperElement().addEventListener('mousedown', (e: MouseEvent) => {
      if (!e.target) return
      const unsafeTarget = e.target as any
      if ($(e.target).hasClass('cm-std')) {
        if (this.tooltip && unsafeTarget.tooltipVisible) {
          Util.fadeOut(this.tooltip)
          unsafeTarget.tooltipVisible = false
        } else {
          const stdSection = UI.getSTDSection(unsafeTarget.textContent)
          if (stdSection) {
            this.showTooltip(stdSection.data[0])
            unsafeTarget.tooltipVisible = true;
          }
        }
      }
    })

    ee.on('update', this, this.update)
  }

  update(s:Common.State) {
    this.setValue(s.pp.ail)
  }
}

class Ail_AST extends Ail {
  constructor(ee:Common.EventEmitter) {
    super(ee)
    this.setTitle('Ail (AST)')
    ee.on('update', this, this.update)
  }

  update(s:Common.State) {
    this.setValue(s.ast.ail)
  }
}

/*  Core */
export class Core extends ReadOnly {
  constructor (ee: Common.EventEmitter) {
    super('Core', '', ee)

    this.editor.setOption('mode', 'text/x-core')
    this.editor.setOption('placeholder', '<Core elaboration failed...>')
    this.editor.on('cursorActivity', (ed) => this.markSelection(ed.getDoc()))

    this.editor.addOverlay({
      token: (stream: CodeMirror.StringStream) => {
        const rx_word = "\" "
        let ch = stream.peek()
        let word = ""
        if (_.includes(rx_word, ch) || ch === '\uE000' || ch === '\uE001') {
          stream.next()
          return undefined 
        }
        while ((ch = stream.peek()) && !_.includes(rx_word, ch)){
          word += ch
          stream.next()
        }
        let re = /{-#\d(\.\d)*(#\d)?/
        if (re.test(word))
          return "std"
        return undefined
      }
    }, { opaque: true, priority: 1000 }
    )

    this.editor.getWrapperElement().addEventListener('mousedown', (e: MouseEvent) => {
      if (!e.target) return
      const unsafeTarget = e.target as any
      if ($(e.target).hasClass('cm-std')) {
        if (this.tooltip && unsafeTarget.tooltipVisible) {
          Util.fadeOut(this.tooltip)
          unsafeTarget.tooltipVisible = false
        } else {
          const stdSection = UI.getSTDSection(unsafeTarget.textContent)
          if (stdSection) {
            this.showTooltip(stdSection.data[0])
            unsafeTarget.tooltipVisible = true;
          }
        }
      }
    })

    this.setValue('Waiting for core...')

    ee.on('update', this, this.update)
    ee.on('highlight', this, this.highlight)
    ee.on('mark', this, this.mark)
    ee.on('markInteractive', this, this.markInteractive)
  }

  initial(s: Readonly<Common.State>) {
    if (s.pp.core == '')
      this.setValue("-- Waiting for core...")
    else
      this.setValue(s.pp.core)
  }

  update(s: Common.State) {
    this.setValue(s.pp.core)
  }

  getLocation(from: Common.Point, to: Common.Point) {
    return this.ee.once((s: Common.State) => {
      let locations = s.locs
      for (let i = 0; i < locations.length; i ++) {
        let loc = locations[i]
        if (loc.core.begin.line <= from.line && loc.core.end.line >= to.line)
          return loc
      }
      return null
    })
  }

  mark(loc: Common.Locations) {
    this.colorLines (loc.core.begin.line, loc.core.end.line, loc.color)
  }

  markInteractive(loc: any, state: Readonly<Common.State>) {
    if (loc.core && state.ranges) {
      const range = state.ranges[loc.core]
      if (loc.c && range)
        this.editor.getDoc().markText(range.begin, range.end, { className: Util.getColorByLocC(state, loc.c) })
    }
  }

  highlight(s: Common.State) {
    for (let i = s.locs.length - 1; i >= 0; i--)
      this.mark(s.locs[i])
  }

  clear() {
    let marks = this.editor.getDoc().getAllMarks()
    for (let i = 0; i < marks.length; i++)
      marks[i].clear()
    this.editor.getDoc().eachLine((line: CodeMirror.LineHandle) => {
      this.editor.removeLineClass(line, 'background')
    })
  }
}

class Asm extends ReadOnly {
  private current: JQuery<HTMLElement>
  private options: JQuery<HTMLElement>
  private cc: Common.Compiler
  private source?: Readonly<string>
  locations: any // TODO

  constructor(ee: Common.EventEmitter, cc?: any) {
    if (cc == null) cc = UI.defaultCompiler // Global variable

    super(cc.name, '', ee)

    this.editor.setOption('placeholder', '<Compilation failed...>')
    this.editor.setOption('mode', {name: "gas", architecture: "x86"})

    let toolbar   = $('<div class="toolbar flex"></div>')

    this.current = $('<span>'+cc.name+'</span>')
    const dropdown = $('<div class="btn dropdown"></div>')
    dropdown.append(this.current)
    dropdown.append(this.createDropdownContent())

    this.options  = $('<input type="text" placeholder="Compiler options..." style="flex-grow: 1;">')
    this.options.on('blur', () => {
      this.compile()
    })
    this.options.on('keypress', (e) => {
      if (e.which == 13) // Enter
        this.compile()
    })

    toolbar.append(dropdown)
    toolbar.append(this.options)

    this.dom.prepend(toolbar)

    this.editor.on('cursorActivity', (ed) => this.markSelection(ed.getDoc()))

    this.cc = cc;
    this.locations = {}

    ee.on('update', this, this.update)
    ee.on('highlight', this, this.highlight)
    ee.on('mark', this, this.mark)
  }

  update(s: Common.State) {
    this.source = s.source()
    this.compile()
  }

  compile() {
    Util.Cursor.wait()
    $.ajax({
      headers: {Accept: 'application/json'},
      contentType: "application/json; charset=utf-8",
      url: 'https://gcc.godbolt.org/api/compiler/'+this.cc.id+'/compile',
      type: 'POST',
      data: JSON.stringify ({
        source: this.source,
        compiler: this.cc.id,
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
        let value = ''
        let lines: any = {}
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
        if (UI.getSettings().colour)
          this.ee.once((s: Readonly<Common.State>) => this.highlight(s))
        Util.Cursor.done()
      },
    }).fail(() => {
        this.setValue('')
        Util.Cursor.done()
    })
  }

  createDropdownContent() {
    const dropdown = $('<div class="dropdown-content"></div>')
    const compilers = UI.compilers
    if (!compilers) return dropdown
    for (let i = 0; i < compilers.length; i++) {
      const cc  = compilers[i]
      const opt = $('<div class="btn">' + cc.name + '</div>')
      opt.on('click', () => {
        this.cc = cc
        this.current.text(cc.name)
        this.compile()
      })
      dropdown.append(opt)
    }
    return dropdown
  }

  updateLocations(lines: any) {
    this.ee.once((s: Readonly<Common.State>) => {
      this.locations = {}
      let locs = s.locs;
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
    })
  }

  getLocation(from: Common.Point, to: Common.Point) {
    for (let i = 0; i < this.locations.length; i++) {
      if (this.locations[i].begin <= from.line && this.locations[i].end >= to.line)
        return this.locations[i].source
    }
    return null
  }

  mark(loc: Common.Locations) {
    let l = this.locations[loc.c.begin.line+1]
    if (l) this.colorLines (l.begin, l.end, l.color)
  }

  highlight(s: Common.State) {
    for (let i = s.locs.length - 1; i >= 0; i--)
      this.mark(s.locs[i])
  }
}

/* Concrete Tabs Factory */
const Tabs: any = {
  Source, Cabs, Ail, Core, Ail_AST,
  Execution, Console, Asm,
  Interactive, Memory,
  Preferences, Implementation, Help
}

export function create(title: string, ee: Common.EventEmitter): Tab {
  return new Tabs[title](ee)
}

export function instanceOf(tab: Tab, title: string) {
  return tab instanceof Tabs[title]
}

}

export default Tabs