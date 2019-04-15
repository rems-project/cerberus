import $ from 'jquery'
import _ from 'lodash'
import { Option, State, Compiler, InteractiveMode, ResultRequest, InteractiveRequest, AllocModel, CoreOpt, ExecOpt, BmcModel } from './common'
import * as util from './util'
import View from './view'
import Widget from './widget';

/** Possible actions to request to the server */
type ExecutionMode = 'random' | 'exhaustive'
type Action = 'elaborate' | 'random' | 'exhaustive' | 'step' | 'bmc' | 'shorten'

export class CerberusUI {
  /** List of existing views */
  private views: View[]
  /** Current displayed view */
  private currentView?: View
  /** Contains the div where views are located */
  private dom: JQuery<HTMLElement>
  /** UI settings */
  private short_share: boolean
  /** C11 Standard in JSON */
  private std: any
  /** Godbolt default compiler */
  defaultCompiler: Compiler
  /** List of compilers */
  compilers?: Compiler []
  /** Step buttons */
  private updateUI: (s: State) => void

  constructor () {
    this.views = []          

    this.dom = $('#views');
    this.short_share = false
    window.onresize = () => this.refresh()

    this.defaultCompiler = {
      id: 'clang500',
      name: 'x86-64 clang 5.0.0'
    }

    // New view
    $('#new').on('click', () => {
      let title = prompt('Please enter the file name', 'source.c');
      if (title)
        this.add(new View(title, ''))
    })

    // Load File
    $('#load').on('click', () => {
      $('#file-input').trigger('click');
    })
    $('#file-input').on('change', (e) => {
      if (!(e.target instanceof HTMLInputElement) || !e.target.files) return
      let file = e.target.files[0]
      let reader = new FileReader()
      reader.onload = (e: ProgressEvent) => {
        if (e.target instanceof FileReader)
          this.add(new View(file.name, e.target.result as string))
      }
      reader.readAsText(file)
    })

    // Load defacto tests
    let defacto: Widget.Widget | undefined
    $('#load_defacto').on('click', () => {
      if (defacto === undefined)
        defacto = new Widget.Defacto()
      else
        defacto.show()
    })
    let gcc2018: Widget.Widget | undefined
    $('#load_demo').on('click', () => {
      if (gcc2018 === undefined)
        gcc2018 = new Widget.GCC2018()
      else
        gcc2018.show()
    })
    let popl19: Widget.POPL19 | undefined
    $('#load_popl19').on('click', () => {
      if (popl19 === undefined)
        popl19 = new Widget.POPL19()
      else
        popl19.show()
    })
    let cav19: Widget.CAV19 | undefined
    $('#load_cav19').on('click', () => {
      if (cav19 === undefined)
        cav19 = new Widget.CAV19()
      else
        cav19.show()
    })
    let pnvi_n2263: Widget.PNVI_N2263_EXAMPLES | undefined
    $('#load_pnvi_n2263').on('click', () => {
      if (pnvi_n2263 === undefined)
        pnvi_n2263 = new Widget.PNVI_N2263_EXAMPLES()
      else
        pnvi_n2263.show()
    })

    // BMC
    $('#bmc').on('click', () => this.bmc ())

    // Run (Execute)
    $('#random').on('click', () => this.exec ('random'))
    $('#exhaustive').on('click', () => this.exec ('exhaustive'))

    // Interactive Buttons
    const stepBack = $('#step-back')
    stepBack.on('click', (e) => {
      if (!stepBack.hasClass('disabled'))
        this.getView().stepBack()
    })
    const stepForward = $('#step-forward')
    stepForward.on('click', (e) => {
      if (!stepForward.hasClass('disabled'))
        this.getView().stepForward()
    })
    const stepForwardLeft = $('#step-forward-left')
    stepForwardLeft.on('click', (e) => this.getView().stepForwardLeft())
    const stepForwardMiddle = $('#step-forward-middle')
    stepForwardMiddle.on('click', (e) => this.getView().stepForwardMiddle())
    const stepForwardRight = $('#step-forward-right')
    stepForwardRight.on('click', (e) => this.getView().stepForwardRight())
    const stepCounter = $('.step-counter')
    $('#restart').on('click', () => this.getView().restartInteractive())

    // Interactive Options
    const setInteractiveMode = (mode: InteractiveMode) => {
      const view = this.getView()
      view.setInteractiveMode(mode)
      this.updateUI(view.state)
    }
    $('#step-tau').on('click', () => setInteractiveMode(InteractiveMode.Tau))
    $('#step-eval').on('click', () => setInteractiveMode(InteractiveMode.Core))
    $('#step-mem-action').on('click', () => setInteractiveMode(InteractiveMode.Memory))
    $('#step-C-line').on('click', () => setInteractiveMode(InteractiveMode.CLine))
    $('#open-memory').on('click', () => this.getView().newTab('Memory'))
    $('#open-memory-table').on('click', () => this.getView().newTab('SimpleMemory'))
    $('#open-interactive').on('click', () => this.getView().newTab('Interactive'))
    $('#open-arena').on('click', () => this.getView().newTab('Arena'))
    $('#open-stdout').on('click', () => this.getView().newTab('Stdout'))
    $('#open-stderr').on('click', () => this.getView().newTab('Stderr'))

    // Pretty print elab IRs
    $('#cabs').on('click', () => this.elab ('Cabs'))
    $('#ail-ast') .on('click', () => this.elab ('Ail_AST'))
    $('#ail') .on('click', () => this.elab ('Ail'))
    $('#core').on('click', () => this.elab ('Core'))

    // Compilers
    $('#compile').on('click', () => this.getView().newTab('Asm', 'Asm (Godbolt)'))

    // Share
    let update_share_link = () => {
      if (!this.currentView) return
      const url = 'https://cerberus.cl.cam.ac.uk/#'
                + this.currentView.getEncodedState()
      if (this.short_share)
        this.shortURL((url: string) => $('#sharelink').val(url))
      else
        $('#sharelink').val(url)
    }
    let update_options_share = (short_share: boolean) => {
      if (short_share) {
        $('#current-share').text('Short')
        $('#option-share').text('Long')
      } else {
        $('#current-share').text('Long')
        $('#option-share').text('Short')
      }
    }
    update_options_share (this.short_share)
    $('#option-share').on('click', () => {
      this.short_share = !this.short_share
      update_options_share (this.short_share)
      update_share_link()
    })
    $('#sharebtn').on('click', () => {
      $('#sharelink').select()
      document.execCommand('Copy')
    })
    $('#share').on('mouseover', update_share_link)

    // Options
    const toggle = (m:{[k:string]:boolean}, k:string) => {
      m[k] = !m[k]
      $('#cb_'+k).prop('checked', m[k])
    }

    $('.option').on('click', (e) => {
      const opt = e.currentTarget.id
      if (!Option.is(opt)) throw Option.Err(opt)
      toggle(this.getView().state.options, opt)
    })

    $('.switch').on('click', (e) => {
      if (e.currentTarget.classList.contains('disabled')) return
      const sw = e.currentTarget.id
      const view = this.getView()
      const state = view.state
      const on = _.includes(state.model.switches, sw)
      if (!on) state.model.switches.push(sw)
      else _.pull(state.model.switches, sw)
      $('#cb_'+sw).prop('checked', !on)
      view.emit('dirty')
    })

    $('.prov-switch').on('click', (e) => {
      if (e.currentTarget.classList.contains('disabled')) return
      const sw = e.currentTarget.id
      const view = this.getView()
      _.pull(view.state.model.switches, 'PVI', 'PNVI', 'PNVI_ae', 'PNVI_ae_udi')
      view.state.model.switches.push(sw)
      $('.prov-switch input').prop('checked', false)
      $('#cb_'+sw).prop('checked', true)
      view.emit('dirty')
    })

    $('.prov-model').on('click', (e) => {
      if (e.currentTarget.classList.contains('disabled')) return
      const am = e.currentTarget.id
      if (!AllocModel.is(am)) throw AllocModel.Err(am)
      const view = this.getView()
      view.emit('dirty')
      const model = view.state.model
      model.alloc_model = am
      $('#r_concrete').prop('checked', model.alloc_model === 'concrete')
      $('#r_symbolic').prop('checked', model.alloc_model === 'symbolic')
      this.updateUI(view.state)
    })

    $('.bmc-model').on('click', (e) => {
      if (e.currentTarget.classList.contains('disabled')) return
      const m = e.currentTarget.id
      if (!BmcModel.is(m)) throw BmcModel.Err(m)
      const view = this.getView()
      view.emit('dirty')
      view.state.bmc_model = m
      $('#r_bmc_c11').prop('checked', m === 'bmc_c11')
      $('#r_bmc_rc11').prop('checked', m === 'bmc_rc11')
      $('#r_bmc_rc11_hardcoded').prop('checked', m === 'bmc_rc11_hardcoded')
      $('#r_bmc_linux').prop('checked', m === 'bmc_linux')
      this.updateUI(view.state)
    })

    $('.core-opt').on('click', (e) => {
      if (e.currentTarget.classList.contains('disabled')) return
      const opt = e.currentTarget.id
      if (!CoreOpt.is(opt)) throw CoreOpt.Err(opt)
      const view = this.getView()
      toggle(view.state.model.core_options, opt)
      view.emit('dirty')
    })

    $('.exec-opt').on('click', (e) => {
      if (e.currentTarget.classList.contains('disabled')) return
      const opt = e.currentTarget.id
      if (!ExecOpt.is(opt)) throw ExecOpt.Err(opt)
      const view = this.getView()
      toggle(view.state.model.exec_options, opt)
      view.emit('dirty')
    })

    $('.highlight').on('click', (e) => {
      if (e.currentTarget.classList.contains('disabled')) return
      const view = this.getView()
      view.emit('clear')
      view.emit('highlight')
    })

    $('.update-exec-graph').on('click', (e) => {
      if (e.currentTarget.classList.contains('disabled')) return
      this.getView().updateExecutionGraph()
    })

    $('.update-mem-graph').on('click', (e) => {
      if (e.currentTarget.classList.contains('disabled')) return
      this.getView().updateMemory()
    })

    // Help
    $('#help').on('click', () => this.getView().newTab('Help'))

    // Implementation Defined Choices
    $('#implementation').on('click', () => this.getView().newTab('Implementation'))

    // Library
    $('#library').on('click', () => this.getView().newTab('Library'))

    // ISO C
    $('#isoC').on('click', () => {
      window.open('http://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf')
    })

    // REMS
    $('#rems').on('click', () => {
      window.open('http://www.cl.cam.ac.uk/~pes20/rems/')
    })

    // Update every 2s
    window.setInterval(() => this.elab(), 2000);

    // Update UI

    const updateCheckBoxes = (ids: {[key: string]: boolean}) =>
      _.map(ids, (v, k) => {
        //$('#'+k).toggleClass('disabled', !isConc)
        $('#cb_'+k).prop('checked', v)
      })

    this.updateUI = (s: State) => {
      // Options
      updateCheckBoxes(s.options)
      // Core options
      updateCheckBoxes(s.model.core_options)
      // Execution options
      updateCheckBoxes(s.model.exec_options)
      $('#r-step-mem-action').prop('checked', s.interactiveMode == InteractiveMode.Memory)
      $('#r-step-C-line').prop('checked', s.interactiveMode == InteractiveMode.CLine)
      $('#r-step-eval').prop('checked', s.interactiveMode == InteractiveMode.Core)
      $('#r-step-tau').prop('checked', s.interactiveMode == InteractiveMode.Tau)
      // Interactive step buttons
      stepBack.toggleClass('disabled', s.interactive === undefined || s.interactive.history.length == 0)
      stepForward.toggleClass('disabled', s.interactive != undefined && s.interactive.next_options.length != 1 && s.interactive.history.length != 0)
      stepForward.toggleClass('invisible', s.interactive != undefined && s.interactive.next_options.length >= 2)
      stepForwardLeft.toggleClass('invisible', s.interactive === undefined || s.interactive.next_options.length < 2)
      stepForwardMiddle.toggleClass('invisible', s.interactive === undefined || s.interactive.next_options.length < 3)
      stepForwardRight.toggleClass('invisible', s.interactive === undefined || s.interactive.next_options.length < 2)
      stepCounter.text(s.interactive === undefined ? 0 : s.interactive.counter)
      // Disabled options only supported by concrete
      $('.conc').toggleClass('disabled', s.model.alloc_model != 'concrete')
    }

    // Get standard
    $.getJSON('std.json').done((res) => this.std = res).fail(() => {
      console.log('Failing when trying to download "std.json"')
    })

    // Get list of compilers
    $.ajax({
      headers: {Accept: 'application/json'},
      url: 'https://gcc.godbolt.org/api/compilers/c',
      type: 'GET',
      success: (data, status, query) => {
        this.defaultCompiler = $.grep(data, (e: Compiler) => e.id == 'cclang500')[0]
        this.compilers       = data
      }
    })

    /** Align dropdown menu (left or right) */
    $('.contain-subitems').on('mouseenter', (e) => {
      const item = $(e.currentTarget)
      const dropdown = $(e.currentTarget).find('.dropdown')
      const offset = item.offset()
      if (offset !== undefined) {
        const left  = offset.left
        const width = dropdown.width()
        const winWidth = $(window).width()
        if (width !== undefined && winWidth !== undefined) {
          if (left + width > winWidth) {
            dropdown.addClass('dropdown-right')
            dropdown.removeClass('dropdown-left')
          } else {
            dropdown.addClass('dropdown-left')
            dropdown.removeClass('dropdown-right')
          }
        }
      }
    })

    { // Scrolling menu section
      let ticking = false // to next animation frame
      let scrolling = false // whenever the menu is scrolling manually
      let scrollDir = ''
      const scrollDistance = 120
      const container = $('.x-scrollable')
      const menu = $('.x-scrollable > .menu')

      // check if one should display the scroll arrows
      container.attr('data-overflowing', util.checkOverflow(menu, container))
      // check for every window resize
      window.addEventListener('resize', () =>
        container.attr('data-overflowing', util.checkOverflow(menu, container)))
      // and when scrolling
      container.on('scroll', () => {
        if (!ticking) {
          window.requestAnimationFrame(() => {
            container.attr('data-overflowing', util.checkOverflow(menu, container))
            ticking = false;
          })
        }
        ticking = true;
      })

      $('#menu-scroll-left').on('click', () => {
        // if we are already scrolling, do nothing
        if (scrolling) return
        const overflow = util.checkOverflow(menu, container)
        if (overflow === 'left' || overflow == 'both') {
          const availableScroll = menu.scrollLeft()
          if (availableScroll && availableScroll < scrollDistance * 2)
            menu.css('transform', `translateX(${availableScroll}px)`)
          else
            menu.css('transform', `translateX(${scrollDistance}px)`)
          menu.removeClass('menu-no-transition')
          scrollDir = 'left'
          scrolling = true
        }
        container.attr('data-overflowing', util.checkOverflow(menu, container))
      })

      $('#menu-scroll-right').on('click', () => {
        // if we are already scrolling, do nothing
        if (scrolling) return
        const overflow = util.checkOverflow(menu, container)
        if (overflow === 'right' || overflow == 'both') {
          const rightEdge = menu[0].getBoundingClientRect().right;
          const scrollerRightEdge = container[0].getBoundingClientRect().right;
          const availableScroll = Math.floor(rightEdge - scrollerRightEdge)
          if (availableScroll && availableScroll < scrollDistance * 2)
            menu.css('transform', `translateX(-${availableScroll}px)`)
          else
            menu.css('transform', `translateX(-${scrollDistance}px)`)
          menu.removeClass('menu-no-transition')
          scrollDir = 'right'
          scrolling = true
        }
        container.attr('data-overflowing', util.checkOverflow(menu, container))
      })

      menu.on('transitionend', () => {
        // get the amount to scroll in the transition matrix
        const style = window.getComputedStyle(menu[0], null)
        const tr = style.getPropertyValue('-webkit-transform') || style.getPropertyValue('transform')
        const amount = Math.abs(parseInt(tr.split(',')[4]) || 0)
        menu.css('transform', 'none')
        menu.addClass('menu-no-transition')
        container.scrollLeft((container.scrollLeft() || 0) + (scrollDir === 'left' ? - amount : + amount))
        scrolling = false
      })
    }

  }

  private setCurrentView(view: View) {
    if (this.currentView)
      this.currentView.hide()
    $('#current-view-title').text(view.title)
    this.currentView = view
    this.updateUI(view.state)
    view.show()
  }

  public elab (lang?: string) {
    const view = this.getView()
    if (lang) view.newTab(lang)
    if (view.isDirty()) {
      this.request('elaborate', (res: ResultRequest) => {
        view.updateState(res)
        view.emit('update')
        view.emit('highlight')
        view.resetInteractive()
      })
    }
  }

  private exec (mode: ExecutionMode) {
    this.request(mode, (res: ResultRequest) => {
      const view = this.getView()
      const cons = view.getConsole()
      if (cons) cons.setActive()
      view.updateState(res)
      view.emit('updateExecution')
    })
  }

  public bmc () {
    this.request('bmc', (res: ResultRequest) => {
      const view = this.getView()
      const cons = view.getConsole()
      if (cons) cons.setActive()
      view.updateState(res)
      view.emit('updateExecution') // Not sure
    })
  }

  private getView(): Readonly<View> {
    if (this.currentView)
      return this.currentView
    throw new Error("Panic: no view")
  }

  private add (view: View) {
    this.views.push(view)
    this.dom.append(view.dom)
    let nav = $('<div class="menu-item btn">'+view.title+'</div>')
    $('#dropdown-views').append(nav)
    nav.on('click', () => this.setCurrentView(view))
    view.on('updateUI', this, (s: State) => this.updateUI(s))
    this.setCurrentView(view)
    view.getSource().refresh()
  }

  addView(title: string, source: string, config?: any) {
    this.add(new View(title, source, config))
    this.refresh()
  }

  public checkExperimentalTab(title: string) {
    // Check Charon2 experimental data
    $.ajax({
      url: `experimental/${title}.html`,
      type: 'GET',
      success: (data) => {
        this.getView().newTab('Experimental', 'Experimental Data', data)
      },
      error: () => {}
    })
  }

  public openExperimentalTab() {
    this.getView().newTab('Experimental')
  }

  public step(active: {id: number, state: string} | null): void {
    const view = this.getView()
    if (active != null) {
      const state = view.state
      if (state.interactive === undefined)
        throw new Error('not in interactive mode')
      this.request('step', (data: ResultRequest) => {
        view.updateState(data)
      }, {
        lastId: state.interactive.last_node_id,
        state: active.state,
        active: active.id,
        tagDefs: state.interactive.tag_defs
      })
    } else {
      this.request('step', (data: ResultRequest) => {
        view.updateState(data)
      })
    }
  }

  public execGraphNodeClick(i: number) {
    this.getView().execGraphNodeClick(i)
  }

  shortURL(onSuccess: Function) {
    this.request('shorten', (data: ResultRequest) => {
      if (data.status == 'shorten')
        onSuccess("https://cerberus.cl.cam.ac.uk/?short/" + data.url)
      else if (data.status == 'failure')
        alert (data.console)
      else
        throw new Error("Unknown response for shorten: " + data)
    })
  }

  request (action: Action, onSuccess: Function, interactive?: InteractiveRequest) {
    const view = this.getView()
    const model = view.state.model
    util.Cursor.wait()
    $.ajax({
      url:  '/query',
      type: 'POST',
      headers: {Accept: 'application/json; charset=utf-8'},
      contentType: 'application/json; charset=utf-8',
      timeout: 60000, /* 1 min timeout */
      data: {
        'action':  action,
        'source':  view.getSource().getValue(),
        'name': view.getSource().title,
        'rewrite': model.core_options.rewrite,
        'sequentialise': model.core_options.sequentialise,
        'libc': model.exec_options.libc,
        'model': model.alloc_model,
        'bmc_model': view.state.bmc_model,
        'switches': view.state.model.switches,
        'interactive': interactive
      },
      dataType: 'json'
    }).done((data, status, query) => {
      onSuccess(data);
    }).fail((req, status) => {
      alert('Failed request!' + status)
    }).always(() => {
      util.Cursor.done()
    })
  }

  getSTDSection (section: string) {
    if (!this.std) return
    const locs = section.match(/\d(\.\d)*(#\d)?/)
    if (!locs) return
    let loc = locs[0].split(/#/)
    let ns = loc[0].match(/\d+/g)
    if (!ns) return
    let title = '§'
    let p = this.std
    let content = ""
    for (let i = 0; i < ns.length; i++) {
      p = p[ns[i]]
      title += ns[i] + '.'
      if (p['title'])
        content += '<h3>'+ns[i]+'. '+p['title']+'</h3>'
    }
    // if has a paragraph
    if (loc[1] && p['P'+loc[1]]) {
      title = title.slice(0,-1) + '#' + loc[1]
      content += p['P'+loc[1]]
    } else {
      let j = 1
      while (p['P'+j]) {
        content += p['P'+j] + '</br>'
        j++
      }
    }
    let div = $('<div class="std">'+content+'</div>')
    // Create footnotes
    div.append('<hr/>')
    div.children('foot').each(function(i) {
      let n = '['+(i+1)+']'
      $(this).replaceWith(n)
      div.append('<div style="margin-top: 5px;">'+n+'. '+ $(this).html()+'</div>')
    })
    div.append('<br>')
    return {title: title, data: div}
  }

  refresh() {
    // Refresh might happen without a view
    if (this.currentView)
      this.currentView.refresh()
  }
}

const UI = new CerberusUI()
export default UI

// This is used to debug
//@ts-ignore
window.UI = UI