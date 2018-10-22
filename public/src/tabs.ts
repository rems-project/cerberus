import $ from 'jquery'
import _ from 'lodash'
import CodeMirror from 'codemirror'
import GoldenLayout from "golden-layout"
import * as util from './util'
import { State, EventEmitter, Compiler } from './common'
import { Point, Locations } from './location'
import UI from './ui' 

namespace Tabs {

/* Generic  */
export abstract class Tab {
  title: string | undefined
  dom: JQuery<HTMLElement>
  ee: EventEmitter

  constructor(title: string, ee: EventEmitter) {
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
  update(s: Readonly<State>) {}

  /** Update initial value (receives current state) */
  initial(s: Readonly<State>) { this.update(s) }
  
  /** Implemented by GoldenLayout when tab content is attached to it */
  setActive () {}
}

export class Help extends Tab {
  constructor(ee: EventEmitter) {
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
  constructor (ee: EventEmitter) {
    super('Prefernces', ee)
    this.dom.addClass('page') // maybe change this
    $.ajax({
      url: 'preferences.html',
      type: 'GET',
      success: (data) => this.dom.append(data)
    })
  }
}

class SvgGraph extends Tab {
  panzoomOptions: any
  container: JQuery<HTMLElement>
  svg: JQuery<HTMLElement>
  
  constructor(name: string, ee: EventEmitter) {
    super (name, ee)
    const controls = $('<div class="toolbar"></div>')
    const zoomIn = $('<div class="menu-item btn inline">Zoom In</div>')
    const zoomOut = $('<div class="menu-item btn inline">Zoom Out</div>')
    const range = $('<input class="menu-item range" type="range" step="0.05" min="0.1" max="2">')
    const reset = $('<div class="menu-item reset btn inline">Reset</div>')
    controls.append(zoomIn)
    controls.append(zoomOut)
    controls.append(range)
    controls.append(reset)
    this.container = $('<div align="center" class="graph"></div>')
    this.dom.append(controls)
    this.dom.append(this.container)
    this.panzoomOptions = {
      $zoomIn: zoomIn,
      $zoomOut: zoomOut,
      $zoomRange: range,
      $reset: reset,
      increment: 0.1,
      minScale: 0.1,
      maxScale: 2
    }
    this.svg = $('<span>No data...</span>')
  }

  setSVG(data: string) {
    this.container.empty()
    // @ts-ignore: Viz.js is loaded later
    this.container.append(Viz(data))
    this.svg = this.container.find('svg')
    this.svg.addClass('panzoom')
    // @ts-ignore
    this.svg.panzoom(this.panzoomOptions)
    // Zoom using the mouse
    this.container.off() // remove all previous events
    this.container.on('mousewheel.focal', (e: any) => {
      e.preventDefault()
      let delta = e.delta || e.originalEvent.wheelDelta
      let zoomOut = delta ? delta < 0 : e.originalEvent.deltaY > 0
      // @ts-ignore
      this.svg.panzoom('zoom', zoomOut, { increment: 0.01, animate: false, focal: e })
    })
  }
}


export class Interactive extends SvgGraph {
  constructor(ee: EventEmitter) {
    super('Interactive', ee)
    ee.on('updateExecutionGraph', this, (s: State) => this.updateGraph(s))
  }

  private updateGraph (state: Readonly<State>) {
    this.setSVG(state.dotExecGraph)
    // Check if needs to span down
    const svgHeight = this.svg.height()
    const containerHeight = this.container.height()
    if (svgHeight && containerHeight) {
      const delta = containerHeight / 2 - svgHeight
      if (delta < 0) {
        // @ts-ignore
        this.svg.panzoom('pan', 0, delta, '{ relative: true }')
      }
    }
  }

  initial(s: Readonly<State>) {
    // The timeout guarantees that the tab is attached to the DOM.
    // The update is called in the next event loop cycle.
    setTimeout (() => this.updateGraph(s), 0)
  }
}

class Memory extends SvgGraph {
  fit: JQuery<HTMLElement>
  svgPos: { x: number, y: number, scale: number}

  constructor(ee: EventEmitter) {
    super('Memory', ee)
    this.fit = $('<div class="btn menu-item inline clicked">Fit</div>')
    this.dom.find('.reset').before(this.fit)
    this.fit.on('click', () => this.toggleFitMode())
    ee.on('updateMemory', this, s => this.updateMemory(s))
    this.svgPos = { x: 0, y: 0, scale: 1}
   }

   inFitMode() {
      return this.fit.hasClass('clicked')
   }

   toggleFitMode() {
      if (this.inFitMode())
        this.fit.removeClass('clicked')
      else
        this.fit.addClass('clicked')
      // @ts-ignore
      this.svg.panzoom('reset')
      this.fitSVG()
   }

   disableFitMode() {
      if (this.inFitMode())
        this.toggleFitMode()
   }

   fitSVG() {
    const svgHeight = this.svg.height()
    const svgWidth = this.svg.width()
    const containerHeight = this.container.height()
    const containerWidth = this.container.width()
    if (svgHeight && svgWidth && containerHeight && containerWidth) {
      const zoom_x = containerWidth/svgWidth
      const zoom_y = containerHeight/svgHeight
      //console.log (zoom_x, zoom_y, this.svgPos.scale)
      const zoom = Math.min(zoom_x, zoom_y)
      if (zoom < this.svgPos.scale) {
        // @ts-ignore
        this.svg.panzoom('zoom', zoom, {silent: true})
        const svgOffset = this.svg.offset()
        const containerOffset = this.container.offset()
        if (svgOffset && containerOffset) {
          const delta_x = zoom_x == zoom ? svgOffset.left - containerOffset.left : 0
          const delta_y = svgOffset.top - containerOffset.top
          // @ts-ignore
          this.svg.panzoom('pan', -delta_x, -delta_y, { relative: true })
        }
      }
    }
   }

   updateMemory (s:State) {
    this.setSVG(s.dotMem)
    this.svg.on('panzoomzoom', (elem, panzoom, scale) => {
      this.svgPos.scale = scale
      this.disableFitMode()
    })
    this.svg.on('panzoompan', (elem, panzoom, x, y) => {
      this.svgPos.x = x
      this.svgPos.y = y
    })
    this.svg.on('panzoomreset', () => {
      this.svgPos = { x: 0, y: 0, scale: 1}
    })
    if (this.inFitMode()) {
      this.fitSVG()
    } else {
      // @ts-ignore
      this.svg.panzoom('pan', this.svgPos.x, this.svgPos.y)
      // @ts-ignore
      this.svg.panzoom('zoom', this.svgPos.scale)
    }
    this.ee.on('layoutChanged', this, () => {
      if (this.inFitMode())
        this.fitSVG()
    })
  }

   initial(s: Readonly<State>) {
    // The timeout guarantees that the tab is attached to the DOM.
    // The update is called in the next event loop cycle.
    setTimeout (() => this.updateMemory(s), 0)
  } 
  
}

/*  with CodeMirror editor */
export abstract class Editor extends Tab {
  protected editor: CodeMirror.Editor
  protected tooltip?: HTMLElement
  private skipCursorEvent: boolean

  constructor(title: string, source: string, ee: EventEmitter) {
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

  getLocation(from: Point, to: Point) {
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
      //console.log('on move');
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
        //console.log('blur');
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
      if (tip.parentNode) util.fadeOut(tip)
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
  constructor (title: string, source: string, ee: EventEmitter) {
    super(title, source, ee)
    this.editor.setOption ('readOnly', true)
  }
}

export class Implementation extends ReadOnly {
  constructor (ee: EventEmitter) {
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

/*
export class Execution extends ReadOnly {
  constructor (ee: EventEmitter) {
    super('Execution', '', ee)
    ee.on('update', this, this.update)
    ee.on('updateExecution', this, this.update)
  }

  update (s: State) : void {
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
*/

class Console extends ReadOnly {
  constructor (ee: EventEmitter) {
    super('Console', '', ee)
    this.editor.setOption('lineWrapping', false)
    this.editor.setOption('mode', 'text')
    ee.on('update', this, this.update)
    ee.on('updateExecution', this, this.update) // in case of failures
  }

  /*
  update(s:State) {
    //const vs = s.console.split(':')
    if (vs.length > 2) { // TODO: should put this change in the server
      this.ee.emit('markError', parseInt(vs[1]))
      this.setValue(s.title() + ':' + _.join(_.drop(vs, 1), ':'))
    } else {
      this.setValue(s.console)
    //}
}*/

  update (s: State) : void {
    /*
    if (s.result == '') {
      this.setValue('')
      return
    }
    // TODO: This should be done at the server!!
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
    */
    this.setValue(s.console)
  }
}

/*  C source */
export class Source extends Editor {
  constructor(title: string, source: string, ee: EventEmitter) {
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

  getLocation(from: Point, to: Point) {
    return this.ee.once((s: Readonly<State>) => {
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

  mark(loc: Locations) {
    let options: CodeMirror.TextMarkerOptions = {
      className: util.getColor(loc.color)
    }
    this.editor.getDoc().markText(loc.c.begin, loc.c.end, options)
  }

  markInteractive(loc: any, state: Readonly<State>) {
    if (loc.c) {
      this.editor.getDoc().markText(loc.c.begin, loc.c.end, { className: util.getColorByLocC(state, loc.c) })
      try { this.editor.scrollIntoView(loc.c.begin, 200) }
      catch(e) { console.log(e) }
    }
  }

  markError(l: number) {
    this.editor.setGutterMarker(l-1, 'error', $('<div class="syntax-error">✖</div>')[0])
  }

  highlight(s: State) {
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
  constructor(ee: EventEmitter) {
    super('Cabs', '', ee)
    this.editor.setOption('mode', 'text/x-ast-dump')
    this.editor.setOption('placeholder', '<Cabs elaboration failed...>')
    ee.on('update', this, this.update)
  }
  update(s: State) {
    this.setValue(s.ast.cabs)
  }
}

/*  Ail */
class Ail extends ReadOnly {
  constructor(ee: EventEmitter) {
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
          util.fadeOut(this.tooltip)
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

  update(s:State) {
    this.setValue(s.pp.ail)
  }
}

class Ail_AST extends Ail {
  constructor(ee:EventEmitter) {
    super(ee)
    this.setTitle('Ail (AST)')
    ee.on('update', this, this.update)
  }

  update(s:State) {
    this.setValue(s.ast.ail)
  }
}

/*  Core */
export class Core extends ReadOnly {
  constructor (ee: EventEmitter) {
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
          util.fadeOut(this.tooltip)
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

  initial(s: Readonly<State>) {
    if (s.pp.core == '')
      this.setValue("-- Waiting for core...")
    else
      this.setValue(s.pp.core)
  }

  update(s: State) {
    this.setValue(s.pp.core)
  }

  getLocation(from: Point, to: Point) {
    return this.ee.once((s: State) => {
      let locations = s.locs
      for (let i = 0; i < locations.length; i ++) {
        let loc = locations[i]
        if (loc.core.begin.line <= from.line && loc.core.end.line >= to.line)
          return loc
      }
      return null
    })
  }

  mark(loc: Locations) {
    this.colorLines (loc.core.begin.line, loc.core.end.line, loc.color)
  }

  markInteractive(loc: any, state: Readonly<State>) {
    if (loc.core && state.ranges) {
      const range = state.ranges[loc.core]
      if (range) {
        this.editor.getDoc().markText(range.begin, range.end, { className: loc.c ? util.getColorByLocC(state, loc.c) : 'color0'})
        this.editor.scrollIntoView(range.begin)
      }
    }
  }

  highlight(s: State) {
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

/*  Arena */
export class Arena extends ReadOnly {
  constructor (ee: EventEmitter) {
    super('Arena', '', ee)

    this.editor.setOption('mode', 'text/x-core')
    this.editor.setOption('placeholder', '<Waiting for runtime information...>')

    ee.on('updateArena', this, this.update)
  }

  initial(s: Readonly<State>) {
    this.setValue(s.arena)
  }

  update(s: Readonly<State>) {
    this.setValue(s.arena)
  }
}



class Asm extends ReadOnly {
  private current: JQuery<HTMLElement>
  private options: JQuery<HTMLElement>
  private cc: Compiler
  private source?: Readonly<string>
  locations: any // TODO

  constructor(ee: EventEmitter, cc?: any) {
    if (cc == null) cc = UI.defaultCompiler // Global variable

    super(cc.name, '', ee)

    this.editor.setOption('placeholder', '<Compilation failed...>')
    this.editor.setOption('mode', {name: "gas", architecture: "x86"})

    let toolbar   = $('<div class="toolbar flex"></div>')

    this.current = $('<span>'+cc.name+'</span>')
    const dropdown = $('<div class="menu-item btn contain-subitems"></div>')
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

  update(s: State) {
    this.source = s.source()
    this.compile()
  }

  compile() {
    util.Cursor.wait()
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
          this.ee.once((s: Readonly<State>) => this.highlight(s))
        util.Cursor.done()
      },
    }).fail(() => {
        this.setValue('')
        util.Cursor.done()
    })
  }

  createDropdownContent() {
    const dropdown = $('<div class="dropdown dropdown-left" style="max-height:250px;"></div>')
    const compilers = UI.compilers
    if (!compilers) return dropdown
    for (let i = 0; i < compilers.length; i++) {
      const cc  = compilers[i]
      const opt = $('<div class="menu-item btn">' + cc.name + '</div>')
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
    this.ee.once((s: Readonly<State>) => {
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

  getLocation(from: Point, to: Point) {
    for (let i = 0; i < this.locations.length; i++) {
      if (this.locations[i].begin <= from.line && this.locations[i].end >= to.line)
        return this.locations[i].source
    }
    return null
  }

  mark(loc: Locations) {
    let l = this.locations[loc.c.begin.line+1]
    if (l) this.colorLines (l.begin, l.end, l.color)
  }

  highlight(s: State) {
    for (let i = s.locs.length - 1; i >= 0; i--)
      this.mark(s.locs[i])
  }
}

/* Concrete Tabs Factory */
const Tabs: any = {
  Source, Cabs, Ail, Core, Ail_AST,
  Console, Arena, Asm,
  Interactive, Memory,
  Preferences, Implementation, Help
}

export function create(title: string, ee: EventEmitter): Tab {
  return new Tabs[title](ee)
}

export function instanceOf(tab: Tab, title: string) {
  return tab instanceof Tabs[title]
}

}

export default Tabs