'use_strict'

class UI {

  constructor () {
    this.views = []           /* List of existing views */
    this.currentView = null   /* Current displayed view */

    this.dom = $('#views');
    //this.dom.prevWidth = this.dom.width();

    window.prevWidth = window.innerWidth
    window.onresize = () => this.refresh()

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
      if (tab instanceof TabGraph) {
        data = tab.dot
        filename = tab.srcTab ? tab.srcTab.title + '.dot' : tab.title
      } else {
        data = tab.editor.getValue()
        filename = getFilename(tab)
      }

      download(data, filename)
    })

    // Run (Execute)
    $('#run').on('click', () => {})
    $('#random').on('click', () => this.exec ('random'))
    $('#exhaustive').on('click', () => this.exec ('exhaustive'))

    // Create Execution Graph
    $('#graph').on('click', () => {
      this.request('graph', (data) => this.currentView.graph.setValue(data))
    })

    // Pretty print AST IRs
    $('#cabs').on('click', () => this.ast ('cabs'))
    $('#ail') .on('click', () => this.ast ('ail'))
    $('#core').on('click', () => this.ast ('core'))

    // Compilers
    $('#compile').on('click', () => {
      this.currentView.newPane.add(new TabAsm(defaultCompiler))
    })

    // Views
    $('#new_pane')   .on('click', () => this.currentView.add(new Pane()))
    $('#source_tab') .on('click', () => this.currentView.getSource().setActive())
    $('#exec_tab')   .on('click', () => this.currentView.exec.setActive())
    $('#cabs_tab')   .on('click', () => this.currentView.cabs.setActive())
    $('#ail_tab')    .on('click', () => this.currentView.ail.setActive())
    $('#core_tab')   .on('click', () => this.currentView.core.setActive())
    $('#console_tab').on('click', () => this.currentView.console.setActive())
    $('#graph_tab')  .on('click', () => this.currentView.graph.setActive())
    $('#unsplit')    .on('click', () => this.currentView.unsplit())

    // Help
    $('#help').on('click', () => {
      this.wait();
      $.ajax({
        url: 'help.html',
        type: 'GET',
        success: (data, status, query) => {
          let tab = new Tab('Help')
          tab.dom.content.addClass('help');
          tab.dom.content.append(data)
          this.currentView.newPane.add(tab)
          tab.setActive()
          this.done()
        }
      })
    })

    // REMS
    $('#rems').on('click', () => {
      window.open('http://www.cl.cam.ac.uk/~pes20/rems/')
    })

  }

  setCurrentView(view) {
    if (this.currentView)
      this.currentView.hide()
    $('#current-view').text(view.title)
    this.currentView = view
    view.show()
  }

  add (view) {
    this.views.push(view)
    this.dom.append(view.dom)

    let nav = $('<a href="#">'+view.title+'</a>')
    $('#dropdown-views').append(nav)
    nav.on('click', () => this.setCurrentView(view))

    this.setCurrentView(view)
    this.currentView.source.refresh()
  }

  request (mode, onSuccess) {
    this.wait()
    $.ajax({
      url:  '/'+mode,
      type: 'POST',
      headers: {Accept: 'application/json'},
      data: this.currentView.getValue(),
      success: (data, status, query) => {
        if (query.getResponseHeader('cerberus') == 0)
          onSuccess(data)
        else
          this.currentView.console.appendValue(data)
        this.done()
      }
    })
  }

  exec (mode) {
    this.request(mode, (data) => this.currentView.exec.setValue(data))
  }

  ast (mode) {
    let view = this.currentView

    if (!view.dirty) {
      view[mode].dirty = false
      view[mode].setValue(view.content[mode]);
      view.highlight()
      return;
    }

    this.request("elab", (data) => {


      let result = parseCerberusResult(data.core)

      // Set colors for every location
      for (let i = 0; i < result.locations.length; i++)
        result.locations[i].color = getColor(i)

      view.dirty = false

      view.source.dirty = false
      view.locations = result.locations
      view.isHighlighted = false

      view.content.cabs = data.cabs;
      view.content.ail  = data.ail;
      view.content.core = result.ast

      view[mode].dirty = false
      view[mode].setValue(view.content[mode]);
      view.highlight()

    })
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
}

/*
 * UI initialisation
 */

const ui = new UI()
const style = createStyle()
let std             = null
let defaultCompiler = null
let compilers       = null

// Get standard
$.getJSON('std.json').done((res) => std = res).fail(() => {
  console.log('Failing when trying to download "std.json"')
})

// Get list of compilers
$.ajax({
  headers: {Accept: 'application/json'},
  url: 'https://gcc.godbolt.org/api/compilers',
  type: 'GET',
  success: (data, status, query) => {
    defaultCompiler = $.grep(data, (e) => e.id == 'clang500')[0]
    compilers       = data
  }
})

// Get default buffer
$.get('buffer.c').done((data) => {
  $(window).ready(() => {
    ui.add(new View('hello.c', data))
    ui.refresh()
  })
}).fail(() => {
  console.log('Failing when trying to download "buffer.c"')
})
