import $ from "jquery"
import GoldenLayout from "golden-layout"
import _ from "lodash"
import Common from './common'
import { Tab, TabSource, TabCore, TabInteractive, createTab, instanceOf } from "./tabs"
import Util from "./util"
import View from "./view"

/** UI Settings */
interface Settings {
  rewrite: boolean,
  sequentialise: boolean,
  auto_refresh: boolean,
  colour: boolean,
  colour_cursor: boolean,
  short_share: boolean
  model: Common.Model
}

export class UI {
  /** List of existing views */
  views: View[]
  /** Current displayed view */
  currentView?: View
  /** Contains the div where views are located */
  dom: JQuery<HTMLElement>
  /** UI settings */
  settings: Settings

  constructor (settings: Settings) {
    this.views = []          

    this.dom = $('#views');
    window.onresize = () => this.refresh()

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
          this.add(new View(file.name, e.target.result))
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

    // Run (Execute)
    $('#run').on('click', () => {})
    $('#random').on('click', () => this.exec ('Random'))
    $('#exhaustive').on('click', () => this.exec ('Exhaustive'))
    $('#interactive').on('click', () => this.interactive())

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
      let url = document.URL.split('#', 1)+'#'+this.currentView.getEncodedState()
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
      this.getView().state.dirty = true;
    })
    $('#sequentialise').on('click', (e) => {
      this.settings.sequentialise = !this.settings.sequentialise;
      $('#cb_sequentialise').prop('checked', this.settings.sequentialise)
      this.getView().state.dirty = true;
    })
    $('#auto_refresh').on('click', (e) => {
      this.settings.auto_refresh = !this.settings.auto_refresh;
      $('#cb_auto_refresh').prop('checked', this.settings.auto_refresh)
    })
    $('#colour').on('click', (e) => {
      this.settings.colour = !this.settings.colour
      if (!this.settings.colour) this.getState().isHighlighted = false
      $('#cb_colour').prop('checked', this.settings.colour)
      this.highlight()
    })
    $('#colour_cursor').on('click', (e) => {
      this.settings.colour_cursor = !this.settings.colour_cursor;
      $('#cb_colour_cursor').prop('checked', this.settings.colour_cursor)
    })

    // Help
    $('#help').on('click', () => this.getView().newTab('Help'))

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

  }

  setCurrentView(view: View) {
    if (this.currentView)
      this.currentView.hide()
    $('#current-view-title').text(view.title)
    this.currentView = view
    view.show()
  }

  add (view: View) {
    this.views.push(view)
    this.dom.append(view.dom)

    let nav = $('<div class="btn">'+view.title+'</div>')
    $('#dropdown-views').append(nav)
    nav.on('click', () => this.setCurrentView(view))

    this.setCurrentView(view)
    this.getSource().refresh()
  }

  request (mode: string, onSuccess: Function, interactive?: any) {
    this.wait()
    $.ajax({
      url:  '/cerberus',
      type: 'POST',
      headers: {Accept: 'application/json'},
      data: JSON.stringify ({
        'action':  mode,
        'source':  this.getSource().getValue(),
        'rewrite': this.settings.rewrite,
        'sequentialise': this.settings.sequentialise,
        'model': this.settings.model,
        'interactive': interactive
      }),
      success: (data, status, query) => {
        onSuccess(data);
        this.done()
      }
    }).fail((e) => {
      console.log('Failed request!', e)
      this.getState().dirty = false
      this.done()
    })
  }

  elab (lang?: string) {
    const view = this.getView()
    if (lang) this.getView().newTab(lang)
    if (this.getState().dirty) {
      this.request('Elaborate', (s: any) => {
        view.mergeState(s)
        view.update()
        view.clearInteractive()
      })
    }
  }

  exec (mode: string) {
    this.request(mode, (s: any) => {
      let exec = this.getView().getExec()
      //if (exec) exec.setActive()
      this.getView().mergeState(s)
      this.getView().update()
    })
  }

  // start interactive mode
  interactive() {
    this.request('Step', (data: any) => {
      this.getView().mergeState(data.state)
      this.getView().newInteractiveTab(data.steps)
    })
  }

  // step interactive mode
  step(active: any) {
    if (active) {
      this.request('Step', (data: any) => {
        this.getView().mergeState(data.state)
        this.getView().updateInteractive(active.id, data.steps)
      }, {
        lastId: this.getState().lastNodeId,
        state: active.state,
        active: active.id,
        tagDefs: this.getState().tagDefs
      })
    } else {
      console.log('error: node '+active+' unknown')
    }
  }

  wait () {
    $('body').addClass('wait')
  }

  done () {
    $('body').removeClass('wait')
  }

  getView(): View {
    if (this.currentView)
      return this.currentView
    throw new Error("Panic: no view")
  }

  refresh() {
    this.getView().refresh()
  }

  // CurrentView Proxy Methods

  highlight() {
    if (!this.settings.colour)
      this.getView().clear();
    else
      this.getView().highlight()
  }

  updateMemory(mem:any) {
    this.getView().updateMemory(mem)
  }

  mark(loc:any) {
    this.getView().mark(loc)
  }

  clear() {
    this.getView().clear()
  }

  fit() {
    this.getView().fit()
  }

  getState() {
    return this.getView().state
  }

  getSource() {
    return this.getView().source
  }
}

/*
 * UI initialisation
 */

interface Compiler {
  id: string
  name: string
}

const ui = new UI({
  rewrite:       false,
  sequentialise: true,
  auto_refresh:  true,
  colour:        true,
  colour_cursor: true,
  short_share:   false,
  model:         Common.Model.Concrete
})
const style = Util.createStyle()
let std             = null // JSON of standard
let compilers       = []   // Godbolt compilers
let config: any     = null // Permalink configuration

// Godbolt default compiler
let defaultCompiler: Compiler = {
  id: 'clang500',
  name: 'x86-64 clang 5.0.0'
}

// Get standard
$.getJSON('std.json').done((res) => std = res).fail(() => {
  console.log('Failing when trying to download "std.json"')
})

// Get list of compilers
$.ajax({
  headers: {Accept: 'application/json'},
  url: 'https://gcc.godbolt.org/api/compilers/c',
  type: 'GET',
  success: (data, status, query) => {
    defaultCompiler = $.grep(data, (e: Compiler) => e.id == 'cclang500')[0]
    compilers       = data
  }
})

// Get list of defacto tests
$.get('defacto_tests.json').done((data) => {
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
            ui.add(new View(name, data))
            ui.refresh()
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

// Get list demo examples
$.get('defacto_tests.json').done((data) => {
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
            ui.add(new View(name, data))
            ui.refresh()
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



// Detect if URL is a permalink
try {
  let uri = document.URL.split('#')
  if (uri && uri.length > 1 && uri[1] != "")
    config = GoldenLayout.unminifyConfig(JSON.parse(decodeURIComponent(uri[1])))
} catch (e) {
  console.log(e + ': impossible to parse permalink')
}

// Add view
export function onLoad() {
  if (config) {
    ui.add(new View(config.title, config.source, config))
    ui.refresh()
  } else {
    $.get('buffer.c').done((source) => {
      ui.add(new View('example.c', source))
      ui.refresh()
    }).fail(() => {
      console.log('Failing when trying to download "buffer.c"')
    })
  }
}

