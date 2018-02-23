'use_strict'

const Tabs = {
  TabSource,
  TabCabs,
  TabAil,
  TabCore,
  TabGraph,
  TabExecution,
  TabConsole
}

class View {
  constructor (title, data) {
    this.tabs = []
    this.title  = title

    let config = null
    let uri = document.URL.split('#')
    if (uri && uri.length > 1) {
      try {
        config = app(uri[1])
                .app(decodeURIComponent)
                .app(JSON.parse)
                .app(GoldenLayout.unminifyConfig)
                .return
      } catch (e) {
        console.log(e)
        config = null
      }
    }
    this.source = config ? new TabSource(config.title, config.source)
                         : new TabSource(title, data)
    this.tabs.push(this.source)

    // GUI
    this.dom = $('<div class="view"></div>')
    $('#views').append(this.dom)
    this.initLayout(config)

    // State
    this.setStateEmpty()
    this.isHighlighted = false;
    this.dirty = true;
  }

  initLayout(config) {
    function component(title) {
      return {
        type: 'component',
        componentName: 'tab',
        componentState: { tab: ('Tab'+title) },
        title: title
      }
    }
    if (config == null) {
      config = {
        settings:{
            hasHeaders: true,
            constrainDragToContainer: true,
            reorderEnabled: true,
            selectionEnabled: false,
            popoutWholeStack: false,
            blockedPopoutsThrowError: true,
            closePopoutsOnUnload: true,
            showPopoutIcon: false,
            showMaximiseIcon: true,
            showCloseIcon: true
        },
        dimensions: {
            borderWidth: 5,
            minItemHeight: 10,
            minItemWidth: 10,
            headerHeight: 20,
            dragProxyWidth: 300,
            dragProxyHeight: 200
        },
        labels: {
            close: 'Close',
            maximise: 'Maximise',
            minimise: 'Minimise'
        },
        content: [{
        type: 'row',
        content: [{
          type: 'column',
          content: [{
            type: 'component',
            componentName: 'source',
            title: this.source.title,
            isClosable: false
          },{
            type: 'stack',
            content: [
              component('Console'),
              component('Execution')
            ]}
          ]},
          component('Core')
        ]}]
      }
    }
    let self = this // WARN: Golden Layout does not work with arrow function
    this.layout = new GoldenLayout (config, this.dom);
    this.layout.registerComponent('source', function (container, state) {
      container.parent.tabcontent = self.source // Attach tab to contentItem
      container.getElement().append(self.source.dom)
      self.source.refresh()
    })
    this.layout.registerComponent('tab', function (container, state) {
      let tab  = new Tabs[state.tab]
      self.tabs.push(tab)
      container.parent.tabcontent = tab // Attach tab to contentItem
      container.getElement().append(tab.dom)
      if (state.update) {
        tab.update(self.state)
        tab.highlight(self.state)
        delete state.update // WARN: update should be null in initialisation
        container.setState(state)
      }
    })
    this.layout.on('itemDestroyed', (c) => {
      if (c.componentName == 'tab') {
        for (let i = 0; i < this.tabs.length; i++) {
          if (this.tabs[i] === c.tabcontent) {
            this.tabs.splice(i, 1)
            break
          }
        }
      }
    })
    this.layout.on( 'tabCreated', (header) => {
      if (header.contentItem.isComponent) {
        let tab = header.contentItem.tabcontent
        header.element.on('mousedown', () => tab.refresh())
        tab.setActive = () => triggerClick(header.element[0])
      }
    })
    this.layout.init()
  }

  setStateEmpty() {
    this.state = {
      status: 'failure',
      pp: {
        cabs: '',
        ail:  '',
        core: ''
      },
      ast: {
        cabs: '',
        ail:  '',
        core: ''
      },
      locs: [],
      steps: [],
      result: '',
      console: ''
    }
  }

  getValue() {
    return this.source.getValue()
  }

  forEachTab(f) {
    for (let i = 0; i < this.tabs.length; i++)
      f(this.tabs[i])
  }

  findTab(title) {
    for (let i = 0; i < this.tabs.length; i++) {
      if (this.tabs[i] instanceof Tabs['Tab'+title]) {
        return this.tabs[i]
      }
    }
    return null
  }

  newTab(title) {
    this.layout.root.contentItems[0].addChild({
      type: 'component',
      componentName: 'tab',
      title: title,
      componentState: {
        tab: ('Tab'+title),
        update: true
      }
    })
    this.refresh()
  }

  getPermanentLink() {
    let miniConfig = GoldenLayout.minifyConfig(this.layout.toConfig())
    miniConfig.title = this.source.title
    miniConfig.source = this.source.getValue()
    return encodeURIComponent(JSON.stringify(miniConfig))
  }

  // Return this first instance (or create a new one)
  getTab(title) {
    let tab = this.findTab(title)
    if (tab == null) {
      this.newTab(aClass, title)
      tab = this.findTab(title)
    }
    return tab
  }
  get exec()    { return this.getTab('Execution') }
  get cabs()    { return this.getTab('Cabs') }
  get ail()     { return this.getTab('Ail') }
  get core()    { return this.getTab('Core') }
  get console() { return this.getTab('Console') }
  get graph()   { return this.getTab('Graph') }

  mark(loc) {
    if (loc) this.forEachTab((tab) => tab.mark(loc))
  }

  clear() {
    this.forEachTab((tab) => tab.clear())
  }

  markSelection(loc) {
    if (!this.dirty && loc) {
      this.isHighlighted = false
      this.clear()
      this.mark(loc)
    }
  }

  highlight() {
    if (!ui.colour) {
      this.clear()
      return;
    }
    if (this.isHighlighted||this.dirty) return;
    this.clear()
    this.forEachTab((tab) => tab.highlight(this.state))
    this.isHighlighted = true
  }

  show() {
    this.dom.show()
  }

  hide() {
    this.dom.hide()
  }

  update() {
    this.forEachTab((tab) => tab.update(this.state))
    this.highlight()
  }

  setState (s) {
    if (s.status == 'failure') {
      this.setStateEmpty()
      this.console.setActive()
    }
    Object.assign(this.state, s) // merge states
    this.dirty = false
    this.isHighlighted = false
    this.update()
  }

  refresh () {
    this.forEachTab((tab) => tab.refresh())
    this.layout.updateSize()
  }
}
