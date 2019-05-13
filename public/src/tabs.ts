import $ from 'jquery'
import _ from 'lodash'
import CodeMirror from 'codemirror'
import * as util from './util'
import * as Mem from './memory'
import { State, EventEmitter, Compiler } from './common'
import { Point, Locations } from './location'
import UI from './ui' 

//@ts-ignore
import Viz from 'viz.js'
//@ts-ignore
import { Module, render } from 'viz.js/full.render.js'

namespace Tabs {

/* Generic  */
export abstract class Tab {
  title: string
  dom: JQuery<HTMLElement>
  ee: EventEmitter

  constructor(title: string, ee: EventEmitter) {
    this.dom = $('<div class="tab-content"></div>')
    this.ee = ee
    this.title = title;
  }

  /** Called when size or visibility of HTML changes */
  refresh () {}

  /** Update value (receives current state) */
  update(s: Readonly<State>) {}

  /** Update initial value (receives current state) */
  initial(s: Readonly<State>) { this.update(s) }
  
  /** Implemented by GoldenLayout when tab content is attached to it */
  setActive () {}

  close() {}
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

export class Experimental extends Tab {
  constructor(ee: EventEmitter) {
    super('Experimental Data', ee)
    this.dom.addClass('page')
    ee.once((s:State) => {
      $.ajax({
        url: `experimental/${s.title()}.html`,
        type: 'GET',
        // WARNING: This assumes that charon2 is outputting the results as an
        // array of HTML elements and the relevant data is in index 24
        success: (data) => {
          this.dom.append($('<p><b>Experimental data</b></p>'))
          let d = $(data)
          this.dom.append(d[24])
        }
      })
    })

  }
}

class SvgGraph extends Tab {
  panzoomOptions: any
  container: JQuery<HTMLElement>
  svg: JQuery<HTMLElement>
  
  constructor(name: string, ee: EventEmitter) {
    super (name, ee)
    const controls = $('<ul class="toolbar menu"></ul>')
    //const zoomIn = $('<li class="menu-item btn inline">Zoom In</li>')
    const zoomIn = $(`<li title="Zoom in" class="menu-item btn inline" style="padding:0;">
    <svg class="menu-icon" xmlns="http://www.w3.org/2000/svg" x="0px" y="0px"
    width="20" height="20"
    viewBox="0 0 192 192"
    style=" fill:#000000;"><g fill="none" fill-rule="nonzero" stroke="none" stroke-width="1" stroke-linecap="butt" stroke-linejoin="miter" stroke-miterlimit="10" stroke-dasharray="" stroke-dashoffset="0" font-family="none" font-weight="none" font-size="none" text-anchor="none" style="mix-blend-mode: normal"><path d="M0,192v-192h192v192z" fill="none"></path><g fill="#ecf0f1"><path d="M83.2,19.2c-35.27042,0 -64,28.72958 -64,64c0,35.27042 28.72958,64 64,64c15.33765,0 29.42326,-5.44649 40.4625,-14.4875l38.2125,38.2125c1.60523,1.67194 3.98891,2.34544 6.23174,1.76076c2.24283,-0.58468 3.99434,-2.33619 4.57902,-4.57902c0.58468,-2.24283 -0.08882,-4.62651 -1.76076,-6.23174l-38.2125,-38.2125c9.04101,-11.03924 14.4875,-25.12485 14.4875,-40.4625c0,-35.27042 -28.72958,-64 -64,-64zM83.2,32c28.35279,0 51.2,22.84722 51.2,51.2c0,28.35279 -22.84721,51.2 -51.2,51.2c-28.35278,0 -51.2,-22.84721 -51.2,-51.2c0,-28.35278 22.84722,-51.2 51.2,-51.2zM83.1,51.1125c-3.5297,0.05517 -6.34834,2.9577 -6.3,6.4875v19.2h-19.2c-2.30807,-0.03264 -4.45492,1.18 -5.61848,3.17359c-1.16356,1.99358 -1.16356,4.45924 0,6.45283c1.16356,1.99358 3.31041,3.20623 5.61848,3.17359h19.2v19.2c-0.03264,2.30807 1.18,4.45492 3.17359,5.61848c1.99358,1.16356 4.45924,1.16356 6.45283,0c1.99358,-1.16356 3.20623,-3.31041 3.17359,-5.61848v-19.2h19.2c2.30807,0.03264 4.45492,-1.18 5.61848,-3.17359c1.16356,-1.99358 1.16356,-4.45924 0,-6.45283c-1.16356,-1.99358 -3.31041,-3.20623 -5.61848,-3.17359h-19.2v-19.2c0.02369,-1.72992 -0.65393,-3.39575 -1.87846,-4.61793c-1.22453,-1.22218 -2.89166,-1.89659 -4.62154,-1.86957z"></path></g></g></svg>
    </li>`)
    const zoomOut = $(`<li title="Zoom out" class="menu-item btn inline" style="padding:0;">
    <svg class="menu-icon" xmlns="http://www.w3.org/2000/svg" x="0px" y="0px"
    width="20" height="20"
    viewBox="0 0 192 192"
    style=" fill:#000000;"><g fill="none" fill-rule="nonzero" stroke="none" stroke-width="1" stroke-linecap="butt" stroke-linejoin="miter" stroke-miterlimit="10" stroke-dasharray="" stroke-dashoffset="0" font-family="none" font-weight="none" font-size="none" text-anchor="none" style="mix-blend-mode: normal"><path d="M0,192v-192h192v192z" fill="none"></path><g fill="#ecf0f1"><path d="M83.2,19.2c-35.27042,0 -64,28.72958 -64,64c0,35.27042 28.72958,64 64,64c15.33765,0 29.42326,-5.44649 40.4625,-14.4875l38.2125,38.2125c1.60523,1.67194 3.98891,2.34544 6.23174,1.76076c2.24283,-0.58468 3.99434,-2.33619 4.57902,-4.57902c0.58468,-2.24283 -0.08882,-4.62651 -1.76076,-6.23174l-38.2125,-38.2125c9.04101,-11.03924 14.4875,-25.12485 14.4875,-40.4625c0,-35.27042 -28.72958,-64 -64,-64zM83.2,32c28.35279,0 51.2,22.84722 51.2,51.2c0,28.35279 -22.84721,51.2 -51.2,51.2c-28.35278,0 -51.2,-22.84721 -51.2,-51.2c0,-28.35278 22.84722,-51.2 51.2,-51.2zM57.6,76.8c-2.30807,-0.03264 -4.45492,1.18 -5.61848,3.17359c-1.16356,1.99358 -1.16356,4.45924 0,6.45283c1.16356,1.99358 3.31041,3.20623 5.61848,3.17359h51.2c2.30807,0.03264 4.45492,-1.18 5.61848,-3.17359c1.16356,-1.99358 1.16356,-4.45924 0,-6.45283c-1.16356,-1.99358 -3.31041,-3.20623 -5.61848,-3.17359z"></path></g></g></svg>
    </li>`)
    const range = $('<input title="Zoom" class="range" type="range" step="0.05" min="0.1" max="2">')
    const range_wrapper = $('<li style="width: calc(100% - 300px) class="menu-item inline"</li>')
    range_wrapper.append(range)
    //const reset = $('<div class="menu-item reset btn inline">Reset</div>')
    const reset = $(`<li title="Reset position" class="menu-item reset btn" style="padding:0;">
    <svg class="menu-icon" xmlns="http://www.w3.org/2000/svg" x="0px" y="0px"
    width="20" height="20"
    viewBox="0 0 192 192"
    style=" fill:#000000;"><g fill="none" fill-rule="nonzero" stroke="none" stroke-width="1" stroke-linecap="butt" stroke-linejoin="miter" stroke-miterlimit="10" stroke-dasharray="" stroke-dashoffset="0" font-family="none" font-weight="none" font-size="none" text-anchor="none" style="mix-blend-mode: normal"><path d="M0,192v-192h192v192z" fill="none"></path><g fill="#ecf0f1"><g id="surface1"><path d="M96,19.2c-40.89,0 -74.37,32.175 -76.59,72.54c-0.18,2.76 1.125,5.4 3.435,6.93c2.31,1.515 5.265,1.68 7.725,0.42c2.46,-1.26 4.065,-3.75 4.17,-6.51c1.785,-32.385 28.395,-58.02 61.26,-58.02c17.61,0 33.405,7.395 44.58,19.2h-10.02c-2.775,-0.045 -5.34,1.41 -6.735,3.81c-1.41,2.385 -1.41,5.355 0,7.74c1.395,2.4 3.96,3.855 6.735,3.81h24.045c0.87,0.15 1.755,0.15 2.64,0h11.715v-38.4c0.03,-2.07 -0.78,-4.065 -2.25,-5.535c-1.47,-1.47 -3.465,-2.28 -5.55,-2.25c-4.23,0.06 -7.62,3.54 -7.56,7.785v14.505c-14.085,-15.96 -34.695,-26.025 -57.6,-26.025zM165.24,92.055c-4.245,-0.18 -7.815,3.12 -7.98,7.365c-1.785,32.385 -28.395,58.02 -61.26,58.02c-17.61,0 -33.39,-7.395 -44.58,-19.2h10.02c2.775,0.045 5.34,-1.41 6.735,-3.81c1.41,-2.385 1.41,-5.355 0,-7.74c-1.395,-2.4 -3.96,-3.855 -6.735,-3.81h-24.12c-0.81,-0.12 -1.62,-0.12 -2.43,0h-11.85v38.4c-0.045,2.775 1.41,5.34 3.81,6.735c2.385,1.41 5.355,1.41 7.74,0c2.4,-1.395 3.855,-3.96 3.81,-6.735v-14.505c14.085,15.96 34.695,26.025 57.6,26.025c40.89,0 74.37,-32.175 76.59,-72.54c0.15,-2.07 -0.555,-4.11 -1.935,-5.655c-1.395,-1.545 -3.345,-2.46 -5.415,-2.55z"></path></g></g></g></svg>
    </li>`)
    controls.append(zoomIn)
    controls.append(zoomOut)
    controls.append(range_wrapper)
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

  setSVG(data: string, callback: () => void, engine?: string){
    this.container.empty()
    // @ts-ignore
    const viz = new Viz({ Module, render })
    // @ts-ignore: Viz.js is loaded later
    viz.renderString(data, {engine}).then(result => {
      this.container.append(result)
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
      callback()
    })
  }
}

export class Interactive extends SvgGraph {
  constructor(ee: EventEmitter) {
    super('Interactive', ee)
    ee.on('updateExecutionGraph', this, (s: State) => this.updateGraph(s))
  }

  private updateGraph (state: Readonly<State>) {
    if (!state.interactive || state.interactive.exec === undefined) {
      this.container.empty()
      return
    }
    this.setSVG(state.interactive.exec, () => {
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
    })
  }

  initial(s: Readonly<State>) {
    // The timeout guarantees that the tab is attached to the DOM.
    // The update is called in the next event loop cycle.
    if (s.interactive != undefined)
      setTimeout (() => this.updateGraph(s), 0)
  }
}

export class BMC extends SvgGraph {
  currentExecution: number = 0;
  status: JQuery<HTMLElement>
  prev: JQuery<HTMLElement>
  next: JQuery<HTMLElement>
  updateBtn: JQuery<HTMLElement>

  constructor(ee: EventEmitter) {
    super('BMC Executions', ee)
    const controls = $('<div class="toolbar"></div>')
    this.status = $('<div class="menu-item inline">Execution 1 of N</div>')
    this.prev = $('<div class="menu-item btn inline">Prev</div>')
    this.prev.addClass('disabled')
    this.next = $('<div class="menu-item btn inline">Next</div>')
    this.updateBtn = $('<div class="menu-item btn inline">Update</div>')
    controls.append(this.status)
    controls.append(this.prev)
    controls.append(this.next)
    controls.append(this.updateBtn)
    this.prev.on('click', () => {
      if (!this.prev.hasClass('disabled')) {
        ee.once(s => {
          this.currentExecution -= 1
          this.setSVG(s.bmc_executions[this.currentExecution], () => {}, 'neato')
          this.status.text(`Execution ${this.currentExecution+1} of ${s.bmc_executions.length}`)
          this.next.removeClass('disabled')
          if (this.currentExecution == 0)
            this.prev.addClass('disabled')
        })
      }
    })
    this.next.on('click', () => {
      if (!this.next.hasClass('disabled')) {
        ee.once(s => {
          this.currentExecution += 1
          this.setSVG(s.bmc_executions[this.currentExecution], () => {}, 'neato')
          this.status.text(`Execution ${this.currentExecution+1} of ${s.bmc_executions.length}`)
          this.prev.removeClass('disabled')
          if (this.currentExecution == s.bmc_executions.length - 1)
            this.next.addClass('disabled')
        })
      }
    })
    this.container.before(controls)
    this.updateBtn.on('click', () => {
      if (!this.updateBtn.hasClass('disabled')) UI.bmc()
    })
    ee.on('updateBMC', this, (s: State) => this.updateGraph(s))
    ee.on('update', this, (s: State) => this.updateGraph(s))
    ee.on('dirty', this, () => this.updateBtn.removeClass('disabled'))
  }

  private updateGraph (state: Readonly<State>) {
    if (state.bmc_executions.length > 0) {
      this.currentExecution = 0
      this.setSVG(state.bmc_executions[0], () => {
        this.status.text(`Execution ${this.currentExecution+1} of ${state.bmc_executions.length}`)
        this.prev.addClass('disabled')
        if (state.bmc_executions.length > 1)
          this.next.removeClass('disabled')
        else
          this.next.addClass('disabled')
        this.updateBtn.addClass('disabled')
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
      }, 'neato')
    } else {
      this.status.text('Execution 0 of 0')
      this.prev.addClass('disabled')
      this.next.addClass('disabled')
      this.container.empty()
    }
  }
}

class Memory extends SvgGraph {
  fit: JQuery<HTMLElement>
  svgPos: { x: number, y: number, scale: number}

  constructor(ee: EventEmitter) {
    super('Memory', ee)
    //this.fit = $('<div class="btn menu-item inline clicked">Fit</div>')
    this.fit = $(`<li title="Fit in the container" class="btn menu-item inline clicked" style="padding:0;">
    <svg class="menu-icon" xmlns="http://www.w3.org/2000/svg" x="0px" y="0px"
    width="20" height="20"
    viewBox="0 0 192 192"
    style=" fill:#000000;"><g fill="none" fill-rule="nonzero" stroke="none" stroke-width="1" stroke-linecap="butt" stroke-linejoin="miter" stroke-miterlimit="10" stroke-dasharray="" stroke-dashoffset="0" font-family="none" font-weight="none" font-size="none" text-anchor="none" style="mix-blend-mode: normal"><path d="M0,192v-192h192v192z" fill="none"></path><g fill="#ecf0f1"><path d="M23.0025,19.1625c-0.16564,0.00181 -0.33098,0.01434 -0.495,0.0375h-3.3075v3.315c-0.04535,0.33849 -0.04535,0.68151 0,1.02v41.745c-0.01959,1.38484 0.708,2.67295 1.90415,3.37109c1.19615,0.69814 2.67555,0.69814 3.8717,0c1.19615,-0.69814 1.92374,-1.98625 1.90415,-3.37109v-32.97l51.045,51.045c0.81262,0.84595 1.9673,1.27412 3.135,1.1625c0.12579,-0.01132 0.25094,-0.02884 0.375,-0.0525c1.40652,-0.27567 2.54249,-1.31164 2.94623,-2.68689c0.40374,-1.37524 0.00806,-2.86088 -1.02623,-3.85311l-51.045,-51.045h32.97c1.38484,0.01959 2.67295,-0.708 3.37109,-1.90415c0.69814,-1.19615 0.69814,-2.67555 0,-3.8717c-0.69814,-1.19615 -1.98625,-1.92374 -3.37109,-1.90415h-41.79c-0.16154,-0.02284 -0.32437,-0.03537 -0.4875,-0.0375zM168.885,19.1625c-0.14309,0.00452 -0.28581,0.01704 -0.4275,0.0375h-41.7375c-1.38484,-0.01959 -2.67295,0.708 -3.37109,1.90415c-0.69814,1.19615 -0.69814,2.67555 0,3.8717c0.69814,1.19615 1.98625,1.92374 3.37109,1.90415h32.97l-51.045,51.045c-1.00316,0.96314 -1.40727,2.39335 -1.05646,3.73904c0.35081,1.3457 1.40171,2.3966 2.74741,2.74741c1.3457,0.35081 2.77591,-0.05329 3.73904,-1.05646l51.045,-51.045v32.97c-0.01959,1.38484 0.708,2.67295 1.90415,3.37109c1.19615,0.69814 2.67555,0.69814 3.8717,0c1.19615,-0.69814 1.92374,-1.98625 1.90415,-3.37109v-41.7525c0.04876,-0.35081 0.04876,-0.70669 0,-1.0575v-3.27h-3.2775c-0.21109,-0.03018 -0.42433,-0.04272 -0.6375,-0.0375zM80.565,107.4825c-0.99763,0.02973 -1.94449,0.44667 -2.64,1.1625l-51.045,51.045v-32.97c0.01421,-1.03795 -0.39236,-2.03745 -1.12708,-2.77076c-0.73472,-0.73331 -1.735,-1.13795 -2.77292,-1.12174c-2.11782,0.0331 -3.809,1.77462 -3.78,3.8925v41.655c-0.07104,0.42203 -0.07104,0.85297 0,1.275v3.15h3.165c0.41714,0.06937 0.84286,0.06937 1.26,0h41.655c1.38484,0.01959 2.67295,-0.708 3.37109,-1.90415c0.69814,-1.19615 0.69814,-2.67555 0,-3.8717c-0.69814,-1.19615 -1.98625,-1.92374 -3.37109,-1.90415h-32.97l51.045,-51.045c1.13572,-1.10397 1.47721,-2.79193 0.85991,-4.25055c-0.6173,-1.45861 -2.06674,-2.38864 -3.64991,-2.34196zM111.3225,107.4825c-1.51365,0.0001 -2.88605,0.8893 -3.50471,2.27075c-0.61866,1.38145 -0.36815,2.99744 0.63971,4.12675c0.06019,0.06718 0.12273,0.13222 0.1875,0.195l51.045,51.045h-32.97c-1.38484,-0.01959 -2.67295,0.708 -3.37109,1.90415c-0.69814,1.19615 -0.69814,2.67555 0,3.8717c0.69814,1.19615 1.98625,1.92374 3.37109,1.90415h41.655c0.42203,0.07104 0.85297,0.07104 1.275,0h3.15v-3.165c0.06937,-0.41714 0.06937,-0.84286 0,-1.26v-41.655c0.01421,-1.03795 -0.39236,-2.03745 -1.12708,-2.77076c-0.73472,-0.73331 -1.735,-1.13795 -2.77292,-1.12174c-2.11782,0.0331 -3.809,1.77462 -3.78,3.8925v32.97l-51.045,-51.045c-0.72296,-0.74317 -1.71569,-1.16244 -2.7525,-1.1625z"></path></g></g></svg>
    </li>`)
    const dot = $('<div class="menu-item btn">DOT</div>')
    const html = $('<div class="menu-item btn">HTML</div>')
    const ps = $('<div class="menu-item btn">PS</div>')
    const svg = $('<div class="menu-item btn">SVG</div>')
    const download_options = $('<div class="dropdown dropdown-left"></div>')
    download_options.append(dot)
    download_options.append(html)
    download_options.append(ps)
    download_options.append(svg)
    const download_btn = $(`<li title="Download" class="btn menu-item inline contain-subitems-no-arrow" style="padding:0;">
    <svg class="menu-icon" xmlns="http://www.w3.org/2000/svg" x="0px" y="0px"
    width="20" height="20"
    viewBox="0 0 192 192"
    style=" fill:#000000;"><g fill="none" fill-rule="nonzero" stroke="none" stroke-width="1" stroke-linecap="butt" stroke-linejoin="miter" stroke-miterlimit="10" stroke-dasharray="" stroke-dashoffset="0" font-family="none" font-weight="none" font-size="none" text-anchor="none" style="mix-blend-mode: normal"><path d="M0,192v-192h192v192z" fill="none"></path><g fill="#ecf0f1"><g id="surface1"><path d="M90,24v99.375l-31.6875,-31.6875l-8.625,8.625l42,42l4.3125,4.125l4.3125,-4.125l42,-42l-8.625,-8.625l-31.6875,31.6875v-99.375zM42,156v12h108v-12z"></path></g></g></g></svg>
    </li>`)
    download_btn.append(download_options)
    const reset = this.dom.find('.reset')
    reset.before(this.fit)
    reset.after(download_btn)
    this.fit.on('click', () => this.toggleFitMode())
    const download = (data: string | undefined, title: string) => {
        if (!data) return
        const e = document.createElement('a')
        e.setAttribute('href', 'data:text/plain;charset=utf-8,'+encodeURIComponent(data))
        e.setAttribute('download', title)
        e.style.display = 'none'
        document.body.appendChild(e)
        e.click()
        document.body.removeChild(e)
    }
    dot.on('click', () => {
      ee.once((s => {
        if (!s.interactive) return
        const filename = `memory_${s.title().replace(/\.[^/.]+$/, "")}_step_${s.interactive.counter}.dot` 
        download (s.interactive.mem, filename)
      }))
    })
    html.on('click', () => {
      ee.once((s => {
        if (!s.interactive) return
        const filename = `memory_${s.title().replace(/\.[^/.]+$/, "")}_step_${s.interactive.counter}.html` 
        download(this.container.html(), filename)
      }))
    })
    ps.on('click', () => {
      ee.once((s => {
        if (!s.interactive) return
        if (!s.interactive.mem) return
        const filename = `memory_${s.title().replace(/\.[^/.]+$/, "")}_step_${s.interactive.counter}.ps` 
        // @ts-ignore
        const viz = new Viz({ Module, render })
        // @ts-ignore: Viz.js is loaded later
        viz.renderString(s.interactive.mem, {format: "ps2"}).then(result => {
          download(result, filename)
        })
      }))
    })
    svg.on('click', () => {
      ee.once((s => {
        if (!s.interactive) return
        const filename = `memory_${s.title().replace(/\.[^/.]+$/, "")}_step_${s.interactive.counter}.svg` 
        download(this.container.html(), filename)
      }))
    })
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
    if (!s.interactive || s.interactive.mem === undefined) {
      this.container.empty()
      return
    }
    this.setSVG(s.interactive.mem, () => {
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
        // @ts-ignore
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
    })
  }

   initial(s: Readonly<State>) {
    // The timeout guarantees that the tab is attached to the DOM.
    // The update is called in the next event loop cycle.
    if (s.interactive != undefined)
      setTimeout (() => this.updateMemory(s), 0)
  } 
  
}

export class SimpleMemory extends Tab {
  container: JQuery<HTMLElement>
  constructor(ee: EventEmitter) {
    super('Simplified Memory', ee)
    this.container = $('<div style="padding-bottom: 50px;">')
    this.dom.addClass('page')
    this.dom.append(this.container)
    ee.on('updateMemory', this, s => this.updateMemory(s))
  }
  updateMemory (s: Readonly<State>) {
    this.container.empty()
    if (!s.interactive) return
    const mem = s.interactive.current.mem
    if (!mem) return
    const table = $('<table>')
    const firstRow = $('<tr><th>id</th><th>address</th><th>type</th><th>name</th><th>value</th></tr>')
    const mkRow = (id: number, addr: string, ty: string, name: string, val: string) => {
      const color = mem.last_used === id ? 'bgcolor="#deffff"' : ''
      return $(`<tr ${color}><td>@${id}</td><td>${addr}</td><td>${ty}</td><td>${name}</td><td>${val}</td></tr>`)
    }
    table.append(firstRow)
    const mkValue = (values: Mem.Value []) => {
      const maxcols = values.reduce((acc, row) => Math.max(acc, row.path.length), 0)+1
      const val = _.reduce(values, (acc, v) => {
        const head = v.path.reduce((acc, tag) => `${acc}<td>${tag}</td>`, '')
        const colspan = String(maxcols-v.path.length)
        if (Mem.ispadding(v)) {
          return `${acc}<tr class="padding">${head}<td colspan="${colspan}"></td></tr>`
        } else {
          return `${acc}<tr>${head}<td colspan="${colspan}">${Mem.string_of_value(v, false, false)}</td></tr>`
        }
      }, '<table>')
      return val + '</table>'
    }
    const mkString = (values: Mem.Value []) => 
      `<table><tr><td>${Mem.mk_string(values)}</td></tr></table>`
    _.map(mem.map, alloc => {
      mkValue(alloc.values)
      table.append(mkRow(alloc.id, /*util.toHex(*/alloc.base/*)*/, alloc.type, alloc.prefix.name,
        alloc.prefix.name === 'string literal' ? mkString(alloc.values) : mkValue(alloc.values)))
    })
    this.container.append(table)
  }
  initial(s: Readonly<State>) {
    this.updateMemory(s)
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

export class Library extends ReadOnly {
  constructor (ee: EventEmitter) {
    super('C11 Library', '', ee)
    this.editor.setOption('placeholder', '<Download failed...>')
    this.editor.setOption('mode', 'text/x-csrc')
    $.ajax({
      url: 'assets/stdlib.c',
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

class Stdout extends ReadOnly {
  constructor (ee: EventEmitter) {
    super('Console', '', ee)
    this.editor.setOption('lineWrapping', false)
    this.editor.setOption('mode', 'text')
    ee.on('update', this, this.update)
    ee.on('updateExecution', this, this.update) // in case of failures
  }
  update (s: State) : void {
    if (s.interactive && s.interactive.current)
      this.setValue(s.interactive.current.stdout)
  }
}

class Stderr extends ReadOnly {
  constructor (ee: EventEmitter) {
    super('Console', '', ee)
    this.editor.setOption('lineWrapping', false)
    this.editor.setOption('mode', 'text')
    ee.on('update', this, this.update)
    ee.on('updateExecution', this, this.update) // in case of failures
  }
  update (s: State) : void {
    if (s.interactive && s.interactive.current)
      this.setValue(s.interactive.current.stderr)
  }
}



class Console extends ReadOnly {
  constructor (ee: EventEmitter) {
    super('Console', '', ee)
    this.editor.setOption('lineWrapping', false)
    this.editor.setOption('mode', 'text')
    ee.on('update', this, this.update)
    ee.on('updateExecution', this, this.update)
  }
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
   // TODO: check why this is needed!
   if (s.console != undefined)
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
    this.title = 'Ail (AST)'
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
    if (loc.core && state.interactive && state.interactive.ranges) {
      const range = state.interactive.ranges[loc.core]
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
    if (s.interactive)
      this.setValue(s.interactive.arena)
  }

  update(s: Readonly<State>) {
    if (s.interactive)
      this.setValue(s.interactive.arena)
  }
}



/*  Herd */
export class Herd extends Editor {
  constructor (ee: EventEmitter) {
    super('Custom herd model', '', ee)
    ee.once(s => {
      if (!s.bmc_herd_file)
        UI.getDefaultHerdFile();
      else
        this.setValue(s.bmc_herd_file)
    })
    this.editor.on('change', () => {
      ee.emit('dirty')
      ee.emit('clear')
    })
    ee.on('updateHerdFile', this, this.update);
    this.editor.setOption('mode', 'text/x-herd')
    this.editor.setOption('placeholder', '<Empty herd file...>')
  }

  update(s: Readonly<State>) {
    if (s.bmc_herd_file)
      this.setValue(s.bmc_herd_file)
  }
}



class Asm extends ReadOnly {
  private current: JQuery<HTMLElement>
  private options: JQuery<HTMLElement>
  private cc: Compiler
  private source?: Readonly<string>
  locations: any // TODO

  constructor(ee: EventEmitter) {
    const cc = UI.defaultCompiler // Global variable

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
        this.ee.once((s: Readonly<State>) => {
          if (s.options.colour_all)
            this.highlight(s)
        })
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
  Source, Cabs, Ail, Core, Ail_AST, BMC, Herd,
  Console, Stdout, Stderr, Arena, Asm,
  Interactive, Memory, SimpleMemory,
  Experimental, Implementation, Library, Help
}

export function create(title: string, ee: EventEmitter, ...args: any[]): Tab {
  return new Tabs[title](ee, args)
}

export function instanceOf(tab: Tab, title: string) {
  return tab instanceof Tabs[title]
}

}

export default Tabs