import $ from 'jquery'
import _ from 'lodash'
import { ID, Bytes, State, Compiler, InteractiveMode, ResultRequest, InteractiveRequest } from './common'
import * as util from './util'
import View from './view'

/** Memory models */
export type Model = 'concrete' | 'symbolic' | 'twin'

/** UI Settings */
export interface Settings {
  rewrite: boolean,
  sequentialise: boolean,
  auto_refresh: boolean,
  colour: boolean,
  colour_cursor: boolean,
  short_share: boolean
  model: Model,
}

/** Possible actions to request to the server */
type ExecutionMode = 'random' | 'exhaustive'
type Action = 'elaborate' | 'random' | 'exhaustive' | 'step'

export class CerberusUI {
  /** List of existing views */
  private views: View[]
  /** Current displayed view */
  private currentView?: View
  /** Contains the div where views are located */
  private dom: JQuery<HTMLElement>
  /** UI settings */
  private settings: Settings
  private updateSettings: () => void
  /** C11 Standard in JSON */
  private std: any
  /** Godbolt default compiler */
  defaultCompiler: Compiler
  /** List of compilers */
  compilers?: Compiler []
  /** Step buttons */
  private updateInteractiveButtons: (s: State) => void

  constructor () {
    this.views = []          

    this.settings = {
      rewrite: false,
      sequentialise: false,
      auto_refresh: true,
      colour: false,
      colour_cursor: true,
      short_share: false,
      model: 'concrete',
    }

    this.dom = $('#views');
    window.onresize = () => this.refresh()

    this.defaultCompiler = {
      id: 'clang500',
      name: 'x86-64 clang 5.0.0'
    }

    // UI settings
    this.updateSettings = () => {
      $('#cb_concrete').prop('checked', this.settings.model === 'concrete')
      $('#cb_rewrite').prop('checked', this.settings.rewrite)
      $('#cb_sequentialise').prop('checked', this.settings.sequentialise)
      $('#cb_auto_refresh').prop('checked', this.settings.auto_refresh)
      $('#cb_colour').prop('checked', this.settings.colour)
      $('#cb_colour_cursor').prop('checked', this.settings.colour_cursor)
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
    $('#load_defacto').on('click', () => {
      $('#defacto').css('visibility', 'visible')
    })

    $('#load_defacto_cancel').on('click', () => {
      $('#defacto').css('visibility', 'hidden')
    })

    $('#load_demo').on('click', () => {
      $('#demo').css('visibility', 'visible')
    })

    $('#load_demo_cancel').on('click', () => {
      $('#demo').css('visibility', 'hidden')
    })

    $('#demo .tests a').on('click', (e) => {
      const name = e.target.textContent as string
      util.get('demo/'+name, (data: string) => {
        $('#demo').css('visibility', 'hidden')
        this.add(new View(name, data))
        this.refresh()
      })
    })

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
    const stepCounter = $('#step-counter')
    $('#restart').on('click', () => this.getView().restartInteractive())

    this.updateInteractiveButtons = (s: State) => {
      const onInteractiveMode = s.tagDefs != undefined
      util.setDisabled(stepBack, s.history.length == 0 || !onInteractiveMode)
      util.setDisabled(stepForward, s.exec_options.length != 1 && s.history.length != 0 && onInteractiveMode) 
      util.setInvisible(stepForward, s.exec_options.length >= 2)
      util.setInvisible(stepForwardLeft, s.exec_options.length < 2)
      util.setInvisible(stepForwardMiddle, s.exec_options.length < 3)
      util.setInvisible(stepForwardRight, s.exec_options.length < 2)
      stepCounter.text(s.step_counter)
    }

    // Interactive Options
    const toggleInteractiveOptions = (flag: string) => {
      const view = this.getView()
      view.toggleInteractiveOptions(flag)
      view.updateExecutionGraph()
      this.updateInteractiveOptions(view)
      view.emit('updateInteractive')
    }
    const setInteractiveMode = (mode: InteractiveMode) => {
      const view = this.getView()
      view.setInteractiveMode(mode)
      this.updateInteractiveOptions(view)
    }
    $('#supress-tau').on('click', () => toggleInteractiveOptions('hide_tau'))
    $('#skip-tau').on('click', () => toggleInteractiveOptions('skip_tau'))
    $('#step-mem-action').on('click', () => setInteractiveMode(InteractiveMode.Memory))
    $('#step-C-line').on('click', () => setInteractiveMode(InteractiveMode.CLine))
    $('#step-Core-trans').on('click', () => setInteractiveMode(InteractiveMode.Core))
    $('#open-memory').on('click', () => this.getView().newTab('Memory'))
    $('#open-interactive').on('click', () => this.getView().newTab('Interactive'))
    $('#open-arena').on('click', () => this.getView().newTab('Arena'))

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
      const url = 'http://www.cl.cam.ac.uk/~pes20/cerberus/server/#'
                + this.currentView.getEncodedState()
      if (this.settings.short_share)
        util.shortURL(url, (url: string) => $('#sharelink').val(url))
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
    update_options_share (this.settings.short_share)
    $('#option-share').on('click', () => {
      this.settings.short_share = !this.settings.short_share
      update_options_share (this.settings.short_share)
      update_share_link()
    })
    $('#sharebtn').on('click', () => {
      $('#sharelink').select()
      document.execCommand('Copy')
    })
    $('#share').on('mouseover', update_share_link)

    // Settings
    $('#concrete').on('click', (e) => {
      this.settings.model =
        (this.settings.model === 'concrete' ? 'symbolic' : 'concrete')
      $('#cb_concrete').prop('checked', this.settings.model === 'concrete')
    })
    $('#rewrite').on('click', (e) => {
      this.settings.rewrite = !this.settings.rewrite;
      $('#cb_rewrite').prop('checked', this.settings.rewrite)
      this.getView().emit('dirty')
    })
    $('#sequentialise').on('click', (e) => {
      this.settings.sequentialise = !this.settings.sequentialise;
      $('#cb_sequentialise').prop('checked', this.settings.sequentialise)
      this.getView().emit('dirty')
    })
    $('#auto_refresh').on('click', (e) => {
      this.settings.auto_refresh = !this.settings.auto_refresh;
      $('#cb_auto_refresh').prop('checked', this.settings.auto_refresh)
    })
    $('#colour').on('click', (e) => {
      const view = this.getView()
      this.settings.colour = !this.settings.colour
      $('#cb_colour').prop('checked', this.settings.colour)
      view.emit('clear')
      view.emit('highlight')
    })
    $('#colour_cursor').on('click', (e) => {
      this.settings.colour_cursor = !this.settings.colour_cursor;
      $('#cb_colour_cursor').prop('checked', this.settings.colour_cursor)
    })

    $('.switch').on('click', (e) => {
      const sw = e.currentTarget.id, view = this.getView()
      view.toggleProvSwitch(sw)
      $('#cb_' + sw).prop('checked', _.includes(view.getSwitches(), sw))
      view.emit('clear')
      view.emit('dirty')
    })

    $('.prov-switch').on('click', (e) => {
      const sw = e.currentTarget.id, view = this.getView()
      view.toggleProvSwitch(sw)
      $('.prov-switch input').prop('checked', false)
      $('#cb_' + sw).prop('checked', true)
      view.emit('clear')
      view.emit('dirty')
    })

    // Preferences
    $('#preferences').on('click', () => this.getView().newTab('Preferences'))

    // Help
    $('#help').on('click', () => this.getView().newTab('Help'))

    // Implementation Defined Choices
    $('#implementation').on('click', () => this.getView().newTab('Implementation'))

    // ISO C
    $('#isoC').on('click', () => {
      window.open('http://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf')
    })

    // REMS
    $('#rems').on('click', () => {
      window.open('http://www.cl.cam.ac.uk/~pes20/rems/')
    })

    // Update every 2s
    window.setInterval(() => {
      if (this.settings.auto_refresh) this.elab()
    }, 2000);

    const serverStatus = $('#server-status')
    let serverStatusFlag = true
    // Check server status
    window.setInterval(() => {
      $.ajax({
        url: 'index.html',
        type: 'HEAD'
      }).done(() => {
        if (!serverStatusFlag) {
          serverStatusFlag = true
          serverStatus.text('')
        }
      }).fail(() => {
        if (serverStatusFlag) {
          serverStatusFlag = false
          serverStatus.text(' (SERVER DOWN)')
        }
      })
    }, 5000)

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

  private updateInteractiveOptions(view: Readonly<View>) {
    const state = view.getState()
    $('#cb-supress-tau').prop('checked', state.hide_tau)
    $('#cb-skip-tau').prop('checked', state.skip_tau)
    $('#r-step-mem-action').prop('checked', state.mode == InteractiveMode.Memory)
    $('#r-step-C-line').prop('checked', state.mode == InteractiveMode.CLine)
    $('#r-step-Core-trans').prop('checked', state.mode == InteractiveMode.Core)
  }

  private setCurrentView(view: View) {
    if (this.currentView)
      this.currentView.hide()
    $('#current-view-title').text(view.title)
    this.currentView = view
    this.updateInteractiveOptions(view)
    this.updateInteractiveButtons(view.getState())
    view.show()
  }

  private elab (lang?: string) {
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
      //const exec = view.getExec()
      const cons = view.getConsole()
      if (cons) cons.setActive()
      view.updateState(res)
      view.emit('updateExecution')
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

    // Interactive stuff
    view.on('update', this, (s: State) => this.updateInteractiveButtons(s))
    // TODO: see if I can delete this event:
    view.on('updateStepButtons', this, (s: State) => this.updateInteractiveButtons(s))

    this.setCurrentView(view)
    view.getSource().refresh()
  }

  getSettings(): Readonly<Settings> {
    return this.settings
  }

  setSettings(settings: Readonly<Settings>): void {
    this.settings = settings;
    this.updateSettings()
  }

  addView(title: string, source: string, config?: any) {
    this.add(new View(title, source, config))
    this.refresh()
  }

  public step(active: {id: ID, state: Bytes} | null): void {
    const view = this.getView()
    if (active != null) {
      this.request('step', (data: ResultRequest) => {
        view.updateState(data)
      }, {
        lastId: view.getState().lastNodeId,
        state: active.state,
        active: active.id,
        tagDefs: view.getState().tagDefs
      })
    } else {
      this.request('step', (data: ResultRequest) => {
        view.updateState(data)
      })
    }
  }

  public execGraphNodeClick(i: ID) {
    this.getView().execGraphNodeClick(i)
  }

  request (action: Action, onSuccess: Function, interactive?: InteractiveRequest) {
    const view = this.getView()
    util.Cursor.wait()
    $.ajax({
      url:  '/cerberus',
      type: 'POST',
      headers: {Accept: 'application/json; charset=utf-8'},
      contentType: 'application/json; charset=utf-8',
      data: {
        'action':  action,
        'source':  view.getSource().getValue(),
        'rewrite': this.settings.rewrite,
        'sequentialise': this.settings.sequentialise,
        'model': this.settings.model,
        'switches': view.getSwitches(),
        'interactive': interactive
      },
      dataType: 'json'
    }).done((data, status, query) => {
      onSuccess(data);
    }).fail((e) => {
      console.log('Failed request!', e)
      // TODO: this looks wrong
      this.settings.auto_refresh = false
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

// TODO: move this to a widget
// Get list of defacto tests
util.get('defacto_tests.json', (data: any) => {
  let div = $('#defacto_body')
  for (let i = 0; i < data.length; i++) {
    let questions = $('<div class="questions"></div>')
    for (let j = 0; j < data[i].questions.length; j++) {
      let q = data[i].questions[j]
      let tests = $('<ul class="tests"></ul>')
      for (let k = 0; q.tests && k < q.tests.length; k++) {
        let name = q.tests[k]
        let test = $('<li><a href="#">'+name+'</a></li>')
        test.on('click', () => {
          $.get('defacto/'+name).done((data) => {
            $('#defacto').css('visibility', 'hidden')
            UI.addView(name, data)
          })
        })
        tests.append(test)
      }
      questions.append(q.question)
      questions.append(tests)
    }
    div.append($('<h3>'+data[i].section+'</h3>'))
    div.append(questions)
  }
})

/** UI start up */

const UI = new CerberusUI()
export default UI

// This is used to debug
//@ts-ignore
window.UI = UI