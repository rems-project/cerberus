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
            minItemWidth: 150,
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
      //container.setTitle(tab.title)
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
      mem: {
        nodes: new vis.DataSet([]),
        edges: new vis.DataSet([])
      },
      result: '',
      console: '',
      lastNodeId: 0,
      isHighlighted: false,
      dirty: true
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
    // Create initial node
    let init = this.state.interactive.steps.nodes[0]
    this.state.steps.nodes.add(init)
    this.state.steps.hide_tau.nodes.add(init)
    this.state.lastNodeId = 1
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

  isInteractiveOpen() {
    for (let i = 0; i < this.tabs.length; i++) {
      if (this.tabs[i] instanceof TabInteractive) return true
    }
    return false
  }

  clearInteractive() {
    this.state.steps.edges.clear()
    this.state.steps.nodes.clear()
    this.state.steps.hide_tau.edges.clear()
    this.state.steps.hide_tau.nodes.clear()
    this.state.interactive = null
    if (this.state.status == 'success' && this.isInteractiveOpen()) {
      ui.request('Step', (data) => {
        this.mergeState(data)
        this.startInteractive()
      })
    }
    this.fit()
  }

  getEncodedState() {
    let miniConfig = GoldenLayout.minifyConfig(this.layout.toConfig())
    miniConfig.title = this.source.title
    miniConfig.source = this.source.getValue()
    return encodeURIComponent(JSON.stringify(miniConfig))
  }
  //
  // Return this first instance (or create a new one)
  getTab(title) {
    let tab = this.findTab(title)
    if (tab == null) {
      this.newTab(title)
      tab = this.findTab(title)
    }
    return tab
  }
  get exec()          { return this.getTab('Execution') }
  get cabs()          { return this.getTab('Cabs') }
  get ail()           { return this.getTab('Ail') }
  get core()          { return this.getTab('Core') }
  get console()       { return this.getTab('Console') }
  get interactive()   { return this.getTab('Interactive') }

  clear() {
    this.tabs.map((tab) => tab.clear())
  }

  mark(loc) {
    if (!this.state.dirty && loc) {
      this.state.isHighlighted = false
      this.clear()
      this.tabs.map((tab) => tab.mark(loc))
    }
  }

  highlight() {
    if (this.state.isHighlighted) return;
    this.clear()
    this.tabs.map((tab) => tab.highlight(this.state))
    this.state.isHighlighted = true
  }

  show() {
    this.dom.show()
  }

  hide() {
    this.dom.hide()
  }

  fit() {
    this.tabs.map((tab) => tab.fit())
  }

  update() {
    this.tabs.map((tab) => tab.update(this.state))
    this.highlight()
  }

  updateMemory(mem) {
    let nodes = []
    let edges = []
    let toHex = (n) => { return "0x" + ("00" + n.toString(16)).substr(-2) }
    let readValue = (id, base, end) => {
      let map = mem.bytemap
      let value = 0
      if (!map[base]) return 'undef' // undefined value in allocation
      if (map[base][0].Some) // Has a provenance
        edges.push({from: id, to: map[base][0].Some})
      for (let i = base; i < end; i++)
        if (map[i]) value += map[i][1]
      return value
    }
    Object.keys(mem.allocations).map((k) => {
      let alloc = mem.allocations[k]
      let base = parseInt(alloc.base)
      let end  = parseInt(alloc.base) + parseInt(alloc.size)
      let value = readValue(k, base, end)
      let label = 'Region '+k+' ['+toHex(base)+'-'+toHex(end)+']: '+value
      nodes.push({id: k, label: label})
    })
    this.state.mem.nodes = new vis.DataSet(nodes)
    this.state.mem.edges = new vis.DataSet(edges)
    this.tabs.map((tab) => tab.updateMemory(this.state))
  }

  mergeState (s) {
    if (s.status == 'failure') {
      this.setStateEmpty()
      this.console.setActive()
    }
    Object.assign(this.state, s) // merge states
    this.state.isHighlighted = false
    this.state.dirty = false
    this.update()
  }

  refresh () {
    this.tabs.map((tab) => tab.refresh())
    this.layout.updateSize()
  }
}
