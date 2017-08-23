'use_strict'

class UI {

  constructor () {
    this.panes = []
    window.prevWidth = window.innerWidth
    this.div = $('#panes')
    this.activePane = null

    // Run
    $('#run').on('click', () => {
    })

    $('#random').on('click', () => {
      this.exec ('random')
    })

    $('#exhaustive').on('click', () => {
      this.exec ('exhaustive')
    })

    $('#graph').on('click', () => {
      this.wait()
      let tab = this.activePane.activeTab
      $.ajax({
        url: '/graph',
        type: 'POST',
        data: tab.editor.getValue(),
        success: (data, status, query) => {
          if (query.getResponseHeader('cerberus') == 0) {
            tab.graphTab.setGraph(data)
            tab.graphTab.setActive()
          } else {
            alert('could not run dot');
          }
          this.done()
        }
      })
    })

    // Load
    $('#load').on('click', () => {
      $('#file-input').trigger('click');
    })

    $('#file-input').on('change', (e) => {
      let file = e.target.files[0]
      if (!file)
        return;
      let reader = new FileReader()
      reader.onload = (e) => {
        let tab = new TabSource()
        tab.editor.setValue(e.target.result)
        this.activePane.addTab(tab)
        tab.setActive()
      }
      reader.readAsText(file)
    })

    $('#core').on('click', () => {
      this.exec_core ('core')
    })

    // View

    $('#new_pane').on('click', () => {
      let pane = new Pane()
      pane.addTab(new TabSource())
      this.addPane(pane)
      this.setup()
    })

    $('#new_tab').on('click', () => {
      let tab = new TabSource()
      this.activePane.addTab(tab)
      tab.setActive()
    })

    // Help
    $('#help').on('click', () => {
      let tab = new Tab('Help')
      tab.content.append($('#help-template').clone().contents())
      this.activePane.addTab(tab)
      tab.setActive()
    })

    window.onresize = () => this.refresh()
  }

  toggleSourceButtons (on) {
    $('#run').disable(!on);
    $('#random').disable(!on);
    $('#exhaustive').disable(!on);
    $('#core').disable(!on);
    $('#graph').disable(!on);
  }

  exec (mode) {
    this.wait()
    let tab = this.activePane.activeTab
    $.ajax({
      url: '/'+mode,
      type: 'POST',
      data: tab.editor.getValue(),
      success: (data, status, query) => {
        if (query.getResponseHeader('cerberus') == 0) {
          tab.execTab.editor.setValue(data)
          tab.execTab.setActive()
          tab.execTab.refresh()
        } else {
          tab.consoleTab.editor.setValue(tab.consoleTab.editor.getValue()+data)
          tab.consoleTab.setActive()
          tab.consoleTab.refresh()
        }
        this.done()
      }
    })
  }

  exec_core (mode) {
    this.wait()
    let tab = this.activePane.activeTab
    $.ajax({
      url: '/'+mode,
      type: 'POST',
      data: tab.editor.getValue(),
      success: (data, status, query) => {
        if (query.getResponseHeader('cerberus') == 0) {

          let result = parseCerberusResult(data)

          // Set colors for every location
          for (let i = 0; i < result.locations.length; i++)
            result.locations[i].color = generateColor()

          tab.locations = result.locations
          tab.dirty = false

          tab.coreTab.editor.setValue(result.core)
          tab.coreTab.locations = result.locations
          tab.coreTab.setActive()
          tab.coreTab.refresh()
          tab.highlight()

          if (result.success && result.batch) {
            tab.execTab.editor.setValue(result.batch)
            tab.execTab.setActive()
            tab.execTab.refresh()
          }

          if (!result.success) {
            tab.consoleTab.editor.setValue (
              tab.consoleTab.editor.getValue()+result.console
            )
            tab.consoleTab.setActive()
            tab.consoleTab.refresh()
          }

        } else {
          tab.consoleTab.editor.setValue(tab.consoleTab.editor.getValue()+data)
          tab.consoleTab.setActive()
          tab.consoleTab.refresh()
        }
        this.done()
      }
    })
  }

  run () {
    this.wait()
    let tab = this.activePane.activeTab
    let source = tab.editor.getValue()
    let result = parseCerberusResult(cerberus.run(source, false, false))

    // Set colors for every location
    for (let i = 0; i < result.locations.length; i++)
      result.locations[i].color = generateColor()

    tab.data = result
    tab.dirty = false
    tab.coreTab.editor.setValue(result.core)
    tab.coreTab.setActive()
    tab.coreTab.refresh()
    tab.highlight()
    this.done()
  }

  cerberusResult(result) {
    this.waitingResult = false
    //let result = parseCerberusResult(res)
    let tab = this.activePane.activeTab

    // Set colors for every location
    for (let i = 0; i < result.locations.length; i++)
      result.locations[i].color = generateColor()

    tab.data = result
    tab.dirty = false
    tab.coreTab.editor.setValue(result.core)
    tab.coreTab.setActive()
    tab.coreTab.refresh()
    tab.highlight()

    if (result.success && result.batch) {
      tab.execTab.editor.setValue(result.batch)
      tab.execTab.setActive()
      tab.execTab.refresh()
    }

    if (!result.success) {
      tab.consoleTab.editor.setValue (
        tab.consoleTab.editor.getValue()+result.console
      )
      tab.consoleTab.setActive()
      tab.consoleTab.refresh()
    }

    this.done()
  }

  setup () {
    let w = window.innerWidth/this.panes.length + 'px'
    for (let i = 0; i < this.panes.length; i++) {
      this.panes[i].div.width(w)
    }
    $('.pane-separator').on('mousedown', e => this.onresize(e))
  }

  wait () {
    $('body').addClass('wait')
  }

  done () {
    $('body').removeClass('wait')
  }

  setActivePane(pane) {
    if (this.activePane)
      this.activePane.setInactive()
    this.activePane = pane
    this.toggleSourceButtons(this.activePane.activeTab instanceof TabSource)

    // Change page name
    if (this.activePane && this.activePane.activeTab) {
      let newTitle = 'Cerberus: ' + this.activePane.activeTab.title
      if (document.title != newTitle)
        document.title = newTitle
    }
  }

  addPane (pane) {
    if (this.panes.length > 0) {
      $('<div class="pane-separator vertical"></div>').appendTo(this.div)
    }
    this.panes.push(pane)
    this.div.append(pane.div)
    pane.parent = this
    pane.refresh()
  }

  get secondaryPane () {
    if (this.panes.length < 2 || !this.activePane) {
      let pane = new Pane()
      this.addPane(pane)
      this.setup()
      return pane
    }
    for (let i = 1; i < this.panes.length - 1; i++) {
      if (this.panes[i-1] == this.activePane)
        return this.panes[i]
    }
    return this.panes[this.panes.length - 1]
  }

  removePane (pane) {
    if (this.panes.length == 1) {
      pane.div.remove()
      this.setup()
      return
    }
    let sep = null
    if (this.panes[0] === pane)
      sep = pane.div.next('.pane-separator')
    else
      sep = pane.div.prev('.pane-separator')
    sep.remove()
    pane.div.remove()

    for (let i = 0; i < this.panes.length; i++) {
      if (this.panes[i] === pane) {
        this.panes.splice(i, 1)
      }
    }
    this.setup()
  }

  refresh () {
    let factor = window.innerWidth / window.prevWidth
    for (let i = 0; i < this.panes.length; i++) {
      let w = parseFloat(this.panes[i].div.siblings()[0].style.width.slice(0, -2))
      this.panes[i].div.siblings()[0].style.width = (w * factor)+'px'
    }
    window.prevWidth = window.innerWidth
  }

  onresize (evt) {
    let x0 = evt.clientX
    let sep = $(evt.currentTarget)
    let pane = sep.prev()
    let paneWidth = pane.width()
    let nextPane = sep.next()
    let nextPaneWidth = nextPane.width()
    let minX = pane.position().left
    let maxX = nextPane.position().left + nextPaneWidth

    function resize (evt) {
      if (minX < evt.clientX && evt.clientX < maxX) {
        let delta = evt.clientX - x0
        pane.width(paneWidth+delta)
        nextPane.width(nextPaneWidth-delta)
      }
    }

    function stop (evt) {
      sep.removeClass('resize')
      $('div').each((i, e) => e.style.pointerEvents = '')
      $(document).off('mousemove');
      $(document).off('mouseup');
    }

    $(sep).addClass('resize')
    $('div').each((i, e) => e.style.pointerEvents = 'none')
    $(document).on('mousemove', e => resize(e));
    $(document).on('mouseup', e => stop(e));
  }

}


/*
 * UI initialisation
 */

const ui = new UI()
const style = createStyle()
let std = null

// Get standard
$.getJSON('std.json').done((res) => std = res).fail(() => {
  console.log('Failing when trying to download "std.json"')
})

// Get default buffer
$.get('buffer.c').done((data) => {
  $(window).ready(() => {
    ui.activePane = new Pane()
    ui.addPane(ui.activePane)
    ui.activePane.addTab(new TabSource())
    ui.setup()
    let tab = ui.activePane.activeTab;
    tab.setTitle('hello.c')
    tab.editor.setValue(data)
    tab.setActive()
    tab.refresh()
  })
}).fail(() => {
  console.log('Failing when trying to download "buffer.c"')
})
