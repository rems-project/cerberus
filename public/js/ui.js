'use_strict'

class UI {

  constructor (settings) {
    this.views = []           /* List of existing views */
    this.currentView = null   /* Current displayed view */

    this.dom = $('#views');
    window.onresize = () => this.refresh()

    // UI settings
    assert(settings != null)
    this.settings = settings
    $('#cb_concrete').prop('checked', this.settings.model == 'Concrete')
    $('#cb_rewrite').prop('checked', this.settings.rewrite)
    $('#cb_sequentialise').prop('checked', this.settings.sequentialise)
    $('#cb_auto_refresh').prop('checked', this.settings.auto_refresh)
    $('#cb_colour').prop('checked', this.settings.colour)
    $('#cb_colour_cursor').prop('checked', this.settings.colour_cursor)

    /*
     * Menu bar event handlers
     */

    // New view
    $('#new').on('click', () => {
      let title = prompt('Please enter the file name', 'source.c');
      if (title)
        this.add(new View(title))
    })

    // Load File
    $('#load').on('click', () => {
      $('#file-input').trigger('click');
    })
    $('#file-input').on('change', (e) => {
      let file = e.target.files[0]
      if (!file)
        return;
      let reader = new FileReader()
      reader.onload = (e) => this.add(new View(file.name, e.target.result))
      reader.readAsText(file)
    })

    // Save (download) file
    // TODO: not being used right now
    $('#save').on('click', () => {
      function download(data, filename) {
        let a = document.createElement('a')
        a.setAttribute('href', "data:text/plain;charset=utf-8,"
          + encodeURIComponent(data))
        a.setAttribute('download', filename)
        a.click()
      }

      function getFilename(tab) {
        if (tab instanceof TabCore) {
          if (tab.srcTab)
            return tab.srcTab.title + '.core'
        }
        return tab.title
      }

      if (!this.activePane || !this.activePane.activeTab)
        alert('fatal error: no active tab')

      let data = ""
      let filename = ""

      let tab = this.activePane.activeTab
      // TODO: this probably needs to go
      if (tab instanceof TabGraph) {
        data = tab.dot
        filename = tab.srcTab ? tab.srcTab.title + '.dot' : tab.title
      } else {
        data = tab.editor.getValue()
        filename = getFilename(tab)
      }

      download(data, filename)
    })

    // Load defacto tests
    $('#load_defacto').on('click', () => {
      $('#defacto').css('visibility', 'visible')
    })

    $('#load_defacto_cancel').on('click', () => {
      $('#defacto').css('visibility', 'hidden')
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
      this.currentView.newTab('Asm')
    })

    // Share
    let update_share_link = () => {
      let url = document.URL.split('#', 1)+'#'+this.currentView.getEncodedState()
      if (this.settings.short_share)
        shortURL(url, (url) => $('#sharelink').val(url))
      else
        $('#sharelink').val(url)
    }
    let update_options_share = (short_share) => {
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
        (this.settings.model == 'Concrete' ? 'Symbolic' : 'Concrete')
      $('#cb_concrete').prop('checked', this.settings.model == 'Concrete')
    })
    $('#rewrite').on('click', (e) => {
      this.settings.rewrite = !this.settings.rewrite;
      $('#cb_rewrite').prop('checked', this.settings.rewrite)
      this.currentView.state.dirty = true;
    })
    $('#sequentialise').on('click', (e) => {
      this.settings.sequentialise = !this.settings.sequentialise;
      $('#cb_sequentialise').prop('checked', this.settings.sequentialise)
      this.currentView.state.dirty = true;
    })
    $('#auto_refresh').on('click', (e) => {
      this.settings.auto_refresh = !this.settings.auto_refresh;
      $('#cb_auto_refresh').prop('checked', this.settings.auto_refresh)
    })
    $('#colour').on('click', (e) => {
      this.settings.colour = !this.settings.colour
      if (!this.settings.colour) this.currentView.isHighlighted = false
      $('#cb_colour').prop('checked', this.settings.colour)
      this.highlight()
    })
    $('#colour_cursor').on('click', (e) => {
      this.settings.colour_cursor = !this.settings.colour_cursor;
      $('#cb_colour_cursor').prop('checked', this.settings.colour_cursor)
    })

    // Help
    $('#help').on('click', () => this.currentView.newTab('Help'))

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

  setCurrentView(view) {
    if (this.currentView)
      this.currentView.hide()
    $('#current-view-title').text(view.title)
    this.currentView = view
    view.show()
  }

  add (view) {
    this.views.push(view)
    this.dom.append(view.dom)

    let nav = $('<div class="btn">'+view.title+'</div>')
    $('#dropdown-views').append(nav)
    nav.on('click', () => this.setCurrentView(view))

    this.setCurrentView(view)
    this.currentView.source.refresh()
  }

  request (mode, onSuccess, interactive) {
    this.wait()
    $.ajax({
      url:  '/cerberus',
      type: 'POST',
      headers: {Accept: 'application/json'},
      data: JSON.stringify ({
        'action':  mode,
        'source':  this.source.getValue(),
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
      this.state.dirty = false
      this.done()
    })
  }

  elab (lang) {
    if (lang) this.currentView.newTab(lang)
    if (this.currentView.state.dirty) {
      this.request('Elaborate', (s) => {
        this.currentView.mergeState(s)
        this.currentView.update()
        this.currentView.clearInteractive()
      })
    }
  }

  exec (mode) {
    this.request(mode, (s) => {
      this.currentView.exec.setActive()
      this.currentView.mergeState(s)
      this.currentView.update()
    })
  }

  // start interactive mode
  interactive() {
    this.request('Step', (data) => {
      this.currentView.mergeState(data.state)
      this.currentView.newInteractiveTab(data.steps)
    })
  }

  // step interactive mode
  step(active) {
    if (active) {
      this.request('Step', (data) => {
        this.currentView.mergeState(data.state)
        this.currentView.updateInteractive(active.id, data.steps)
      }, {
        lastId: this.state.lastNodeId,
        state: active.state,
        active: active.id,
        tagDefs: this.state.tagDefs
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

  refresh() {
    if (this.currentView)
      this.currentView.refresh()
  }

  // CurrentView Proxy Methods

  highlight() {
    if (!this.settings.colour)
      this.currentView.clear();
    else
      this.currentView.highlight()
  }

  updateMemory(mem) {
    this.currentView.updateMemory(mem)
  }

  mark(loc) {
    this.currentView.mark(loc)
  }

  clear() {
    this.currentView.clear()
  }

  fit() {
    this.currentView.fit()
  }

  get state() {
    return this.currentView.state
  }

  get source() {
    return this.currentView.source
  }

}

/*
 * UI initialisation
 */

const ui = new UI({
  rewrite:       false,
  sequentialise: true,
  auto_refresh:  true,
  colour:        true,
  colour_cursor: true,
  short_share:   false,
  model:         'Concrete'
})
const style = createStyle()
let std             = null // JSON of standard
let compilers       = []   // Godbolt compilers
let config          = null // Permalink configuration

// Godbolt default compiler
let defaultCompiler = {
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
    defaultCompiler = $.grep(data, (e) => e.id == 'cclang500')[0]
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

// Detect if URL is a permalink
try {
  let uri = document.URL.split('#')
  if (uri && uri.length > 1 && uri[1] != "")
    config = GoldenLayout.unminifyConfig(JSON.parse(decodeURIComponent(uri[1])))
} catch (e) {
  console.log(e + ': impossible to parse permalink')
}

// Add view
function onLoad() {
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

$(window).ready(onLoad)
