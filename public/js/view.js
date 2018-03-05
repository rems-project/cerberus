'use_strict'

class View {
  constructor (title, data, config) {
    this.tabs = []
    this.title  = title

    this.source = new TabSource(title, data)
    this.tabs.push(this.source)

    // DOM
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
        componentState: { tab: title },
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
      let tab = createTab(state.tab)
      self.tabs.push(tab)
      container.parent.tabcontent = tab // Attach tab to contentItem
      container.getElement().append(tab.dom)
      if (state.update) {
        tab.update(self.state)
        tab.highlight(self.state)
        delete state.update
      }
      container.setState(state)
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
      view: [],
      interactive: null,
      steps: {
        nodes: new vis.DataSet([]),
        edges: new vis.DataSet([]),
        hide_tau: {
          nodes: new vis.DataSet([]),
          edges: new vis.DataSet([])
        }
      },
      result: '',
      console: ''
    }
  }

  findTab(title) {
    for (let i = 0; i < this.tabs.length; i++) {
      if (instanceOf(this.tabs[i], title)) {
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
        tab: title,
        update: true
      }
    })
    this.refresh()
  }

  startInteractive() {
    if (!this.state.interactive.steps) {
      console.log('impossible initialise interactive mode')
      return
    }
    if (this.state.steps.nodes.length > 0) {
      console.log('interactive mode already initialised')
      return
    }
    // Create init node
    let init = this.state.interactive.steps.nodes[0]
    this.state.steps.nodes.add({id: init.id, label: init.label})
    // Create temporary next node
    let next = {
      id: init.id + 1,
      label: 'Next step.',
      group: 'leaf',
      state: init.state
    }
    this.state.steps.nodes.add(next)
    this.state.steps.edges.add({from: init.id, to: next.id})
  }

  newInteractiveTab() {
    this.startInteractive()
    this.layout.root.contentItems[0].addChild({
      type: 'column',
      content: [{
        type: 'component',
        componentName: 'tab',
        title: 'Interactive',
        componentState: {
          tab: 'Interactive'
        }
      },{
        type: 'component',
        componentName: 'tab',
        title: 'Memory',
        componentState: {
          tab: 'Memory',
          update: true
        }
      }]
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
      this.newTab(title)
      tab = this.findTab(title)
    }
    return tab
  }
  get exec()    { return this.getTab('Execution') }
  get cabs()    { return this.getTab('Cabs') }
  get ail()     { return this.getTab('Ail') }
  get core()    { return this.getTab('Core') }
  get console() { return this.getTab('Console') }
  get interactive()   { return this.getTab('Interactive') }

  clear() {
    this.tabs.forEach((tab) => tab.clear())
  }

  mark(loc) {
    if (!this.dirty && loc) {
      this.isHighlighted = false
      this.clear()
      this.tabs.forEach((tab) => tab.mark(loc))
    }
  }

  highlight() {
    if (this.isHighlighted||this.dirty) return;
    this.clear()
    this.tabs.forEach((tab) => tab.highlight(this.state))
    this.isHighlighted = true
  }

  show() {
    this.dom.show()
  }

  hide() {
    this.dom.hide()
  }

  update() {
    this.tabs.forEach((tab) => tab.update(this.state))
    this.highlight()
  }

  mergeState (s) {
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
    this.tabs.forEach((tab) => tab.refresh())
    this.layout.updateSize()
  }
}
