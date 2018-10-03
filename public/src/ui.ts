import $ from 'jquery'
import GoldenLayout from 'golden-layout'
import Common from './common'
import Util from './util'
import View from './view'

/** UI Settings */
export interface Settings {
  rewrite: boolean,
  sequentialise: boolean,
  auto_refresh: boolean,
  colour: boolean,
  colour_cursor: boolean,
  short_share: boolean
  model: Common.Model
}

export class CerberusUI {
  /** List of existing views */
  private views: View[]
  /** Current displayed view */
  private currentView?: View
  /** Contains the div where views are located */
  private dom: JQuery<HTMLElement>
  /** UI settings */
  private settings: Settings
  /** C11 Standard in JSON */
  private std: any
  /** Godbolt default compiler */
  defaultCompiler: Common.Compiler
  /** List of compilers */
  compilers?: Common.Compiler []

  // TODO!
  public demo(name: string) {
    Util.get('demo/'+name, (data: string) => {
      $('#demo').css('visibility', 'hidden')
      this.add(new View(name, data))
      this.refresh()
    })
  }

  constructor (settings: Settings) {
    this.views = []          

    this.dom = $('#views');
    window.onresize = () => this.refresh()

    this.defaultCompiler = {
      id: 'clang500',
      name: 'x86-64 clang 5.0.0'
    }

    // UI settings
    this.settings = settings
    $('#cb_concrete').prop('checked', this.settings.model == Common.Model.Concrete)
    $('#cb_rewrite').prop('checked', this.settings.rewrite)
    $('#cb_sequentialise').prop('checked', this.settings.sequentialise)
    $('#cb_auto_refresh').prop('checked', this.settings.auto_refresh)
    $('#cb_colour').prop('checked', this.settings.colour)
    $('#cb_colour_cursor').prop('checked', this.settings.colour_cursor)

    // Menu bar event handlers

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
      const name = e.target.textContent + '.c'
      Util.get('demo/'+name, (data: string) => {
        $('#demo').css('visibility', 'hidden')
        this.add(new View(name, data))
        this.refresh()
      })
    })

    // Run (Execute)
    $('#random').on('click', () => this.exec (Common.ExecutionMode.Random))
    $('#exhaustive').on('click', () => this.exec (Common.ExecutionMode.Exhaustive))

    // Interactive
    $('#step-back').on('click', () => this.getView().stepBack())
    $('#step-forward').on('click', () => this.getView().stepForward())
    $('#restart').on('click', () => this.getView().restartInteractive())

    // Interactive Options
    const toggleInteractiveOptions = (flag: string) => {
      const view = this.getView()
      view.toggleInteractiveOptions(flag)
      view.updateExecutionGraph()
      this.updateInteractiveOptions(view)
      view.emit('updateInteractive')
    }
    const setInteractiveMode = (mode: Common.InteractiveMode) => {
      const view = this.getView()
      view.setInteractiveMode(mode)
      this.updateInteractiveOptions(view)
    }
    $('#supress-tau').on('click', () => toggleInteractiveOptions('hide_tau'))
    $('#skip-tau').on('click', () => toggleInteractiveOptions('skip_tau'))
    $('#step-mem-action').on('click', () => setInteractiveMode(Common.InteractiveMode.Memory))
    $('#step-C-line').on('click', () => setInteractiveMode(Common.InteractiveMode.CLine))
    $('#step-Core-trans').on('click', () => setInteractiveMode(Common.InteractiveMode.Core))
    $('#open-memory').on('click', () => this.getView().newTab('Memory'))
    $('#open-interactive').on('click', () => this.getView().newTab('Interactive'))
    $('#open-arena').on('click', () => this.getView().newTab('Arena'))

    // Pretty print elab IRs
    $('#cabs').on('click', () => this.elab ('Cabs'))
    $('#ail-ast') .on('click', () => this.elab ('Ail_AST'))
    $('#ail') .on('click', () => this.elab ('Ail'))
    $('#core').on('click', () => this.elab ('Core'))

    // Compilers
    $('#compile').on('click', () => {
      if (this.currentView)
        this.currentView.newTab('Asm')
    })

    // Share
    let update_share_link = () => {
      if (!this.currentView) return
      const url = 'http://www.cl.cam.ac.uk/~pes20/cerberus/server/#'
                + this.currentView.getEncodedState()
      if (this.settings.short_share)
        Util.shortURL(url, (url: string) => $('#sharelink').val(url))
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
        (this.settings.model == Common.Model.Concrete ? Common.Model.Symbolic : Common.Model.Concrete)
      $('#cb_concrete').prop('checked', this.settings.model == Common.Model.Concrete)
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

    // About
    $('#about').on('click', () => {
      window.open('https://www.cl.cam.ac.uk/~pes20/cerberus/')
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
          serverStatus.text('(SERVER DOWN)')
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
        this.defaultCompiler = $.grep(data, (e: Common.Compiler) => e.id == 'cclang500')[0]
        this.compilers       = data
      }
    })
  }

  private updateInteractiveOptions(view: Readonly<View>) {
    const state = view.getState()
    $('#cb-supress-tau').prop('checked', state.hide_tau)
    $('#cb-skip-tau').prop('checked', state.skip_tau)
    $('#r-step-mem-action').prop('checked', state.mode == Common.InteractiveMode.Memory)
    $('#r-step-C-line').prop('checked', state.mode == Common.InteractiveMode.CLine)
    $('#r-step-Core-trans').prop('checked', state.mode == Common.InteractiveMode.Core)
  }

  private setCurrentView(view: View) {
    if (this.currentView)
      this.currentView.hide()
    $('#current-view-title').text(view.title)
    this.currentView = view
    this.updateInteractiveOptions(view)
    view.show()
  }

  private elab (lang?: string) {
    const view = this.getView()
    if (lang) view.newTab(lang)
    if (view.isDirty()) {
      this.request(Common.Elaborate(), (res: Common.ResultRequest) => {
        view.updateState(res)
        view.emit('update')
        view.emit('highlight')
        view.resetInteractive()
      })
    }
  }

  private exec (mode: Common.ExecutionMode) {
    this.request(Common.Execute(mode), (res: Common.ResultRequest) => {
      const view = this.getView()
      const exec = view.getExec()
      if (exec) exec.setActive()
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

    let nav = $('<div class="btn">'+view.title+'</div>')
    $('#dropdown-views').append(nav)
    nav.on('click', () => this.setCurrentView(view))

    this.setCurrentView(view)
    view.getSource().refresh()
  }

  getSettings(): Readonly<Settings> {
    return this.settings
  }

  addView(title: string, source: string, config?: any) {
    this.add(new View(title, source, config))
    this.refresh()
  }

  public step(active: {id: Common.ID, state: Common.Bytes} | null): void {
    const view = this.getView()
    if (active) {
      this.request(Common.Step(), (data: Common.ResultRequest) => {
        view.updateState(data)
      }, {
        lastId: view.getState().lastNodeId,
        state: active.state,
        active: active.id,
        tagDefs: view.getState().tagDefs
      })
    } else {
      this.request(Common.Step(), (data: Common.ResultRequest) => {
        view.updateState(data)
      })
    }
  }

  public execGraphNodeClick(i: Common.ID) {
    this.getView().execGraphNodeClick(i)
  }

  request (action: Common.Action, onSuccess: Function, interactive?: Common.InteractiveRequest) {
    const view = this.getView()
    Util.Cursor.wait()
    $.ajax({
      url:  '/cerberus',
      type: 'POST',
      headers: {Accept: 'application/json'},
      data: JSON.stringify ({
        'action':  Common.string_of_action(action),
        'source':  view.getSource().getValue(),
        'rewrite': this.settings.rewrite,
        'sequentialise': this.settings.sequentialise,
        'model': Common.string_of_model(this.settings.model),
        'interactive': interactive
      }),
      success: (data, status, query) => {
        onSuccess(data);
        Util.Cursor.done()
      }
    }).fail((e) => {
      console.log('Failed request!', e)
      // TODO: this looks wrong
      this.settings.auto_refresh = false
      Util.Cursor.done()
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
    this.getView().refresh()
  }

}

// TODO: move this to a widget
// Get list of defacto tests
Util.get('defacto_tests.json', (data: any) => {
  let div = $('#defacto_body')
  for (let i = 0; i < data.length; i++) {
    let questions = $('<ul class="questions"></ul>')
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

type StartupMode =
  { kind: 'default', settings: Settings } |
  { kind: 'permalink', config: any, settings: Settings } |
  { kind: 'fixedlink', file: string, settings: Settings }

function getDefaultSettings(): Settings {
    return { rewrite: false,
             sequentialise: false,
             auto_refresh: true,
             colour: false,
             colour_cursor: true,
             short_share: false,
             model: Common.Model.Concrete 
           }
}

function getStartupMode(): StartupMode {
  function parsedFixedArguments(args: string []): [string, Settings] {
    let file: string | undefined
    const settings = getDefaultSettings()
    function updateSettings(param: string, value: string) {
      const toBool = (b: string) => b === 'true'
      switch(param) {
        case 'rewrite':
          settings.rewrite = toBool(value)
          break
        case 'sequentialise':
          settings.sequentialise = toBool(value)
          break
        case 'auto_refresh':
          settings.auto_refresh = toBool(value)
          break
        case 'color':
        case 'colour':
          settings.colour = toBool(value)
          break
        case 'color_cursor':
        case 'colour_cursor':
          settings.colour_cursor = toBool(value)
          break
        case 'short_share':
          settings.short_share = toBool(value)
          break
        case 'model':
          settings.model = Common.model_of_string(value)
          break
        default:
          throw `Unknown argument ${param}`
      }
    }
    args.map(arg => {
      const params = arg.split('=')
      if (params[0] && params[1]) {
        updateSettings(params[0], params[1])
      } else {
        file = params[0]
      }
    })
    if (file !== undefined)
      return [file, settings]
    throw 'Missing filename in fixed link'
  }
  try {
    // First try a permanent link
    let uri = document.URL.split('#')
    if (uri && uri.length == 2 && uri[1] !== '') {
      const config = GoldenLayout.unminifyConfig(JSON.parse(decodeURIComponent(uri[1])))
      return { kind: 'permalink',
              config: config,
              settings: getDefaultSettings()
            }
    }
    // Try fixed links
    uri = document.URL.split('?')
    if (uri && uri.length == 2 && uri[1] !== '') {
      const [file, settings] = parsedFixedArguments(uri[1].split('&'))
      return { kind: 'fixedlink',
              file: file,
              settings: settings
            }
    }
    // Default
    return { kind: 'default', settings: getDefaultSettings() }
  } catch (e) {
    console.log(`Startup error: ${e}`)
    return { kind: 'default', settings: getDefaultSettings() }
  }
}

function defaultStart() {
  Util.get('buffer.c', (source: string) => {
    UI.addView('example.c', source)
  }, () => {
    console.log('Error when trying to download "buffer.c"... Using an empty file.')
    UI.addView('example.c', '')
  })
}

export function onLoad() {
  switch (mode.kind) {
    case 'default':
      defaultStart()
      break
    case 'permalink':
      UI.addView(mode.config.title, mode.config.source, mode.config)
      break
    case 'fixedlink':
      Util.get(mode.file, (source: string) => {
        UI.addView(mode.file, source)
      }, () => {
        console.log(`Error when trying to download ${mode.file}`)
        alert(`Error downloading ${mode.file}...`)
        defaultStart()
      })
      break
  }
}

const mode = getStartupMode()
const UI = new CerberusUI(mode.settings)

//@ts-ignore 
window.UI = UI
export default UI