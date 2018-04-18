import $ from "jquery"
import GoldenLayout from "golden-layout"
import _ from "lodash"
import { Node, Edge, Graph } from "./graph"
import { Tab, TabSource, TabInteractive, createTab, instanceOf } from "./tabs"
import Util from "./util"
import Common from './common'

type bytes = string

export default class View {
  public tabs: Tab[]
  title: string


  // NOT SURE ABOUT !
  layout!: GoldenLayout;
  source: TabSource
  state!: Common.State;

  dom: JQuery<HTMLElement>

  constructor (title: string, data: string, config?: GoldenLayout.Config) {
    this.tabs = []

    this.title  = title

    this.source = new TabSource(title, data)
    this.tabs.push(this.source)

    // State
    this.setStateEmpty()

    // DOM
    this.dom = $('<div class="view"></div>')
    $('#views').append(this.dom)
    this.initLayout(config)
  }

  initLayout(config?: GoldenLayout.Config) {
    function component(title: string) {
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
              component('Execution'),
              component('Memory')
            ]}
          ]},
          component('Core')
        ]}]
      }
    }
    let self = this // WARN: Golden Layout does not work with arrow function
    this.layout = new GoldenLayout (config, this.dom);
    this.layout.registerComponent('source', function (container: GoldenLayout.Container, state: any) {
      //@ts-ignore
      container.parent.tabcontent = self.source // Attach tab to contentItem
      container.getElement().append(self.source.dom)
      self.source.refresh()
    })
    this.layout.registerComponent('tab', function (container: GoldenLayout.Container, state: any) {
      let tab = createTab(state.tab)
      self.tabs.push(tab)
      //@ts-ignore
      container.parent.tabcontent = tab // Attach tab to contentItem
      container.getElement().append(tab.dom)
      container.setState(state)
      tab.update(self.state)
      tab.highlight(self.state)
    })
    this.layout.on('itemDestroyed', (c: GoldenLayout.ContentItem) => {
      //@ts-ignore
      if (c.componentName == 'tab') {
        for (let i = 0; i < this.tabs.length; i++) {
      //@ts-ignore
          if (this.tabs[i] === c.tabcontent) {
            this.tabs.splice(i, 1)
            break
          }
        }
      }
    })
      //@ts-ignore
    this.layout.on( 'tabCreated', (header) => {
      //@ts-ignore
      if (header.contentItem.isComponent) {
        let tab = header.contentItem.tabcontent
        header.element.on('mousedown', () => tab.refresh())
        tab.setActive = () => Util.triggerClick(header.element[0])
      }
    })
    this.layout.init()
  }

  setStateEmpty() {
    this.state = {
      title: this.title,
      status: 'failure',
      pp: { cabs: '', ail:  '', core: '' },
      ast: { cabs: '', ail:  '', core: '' },
      locs: [],
      graph: new Graph(),
      mem: new Graph(),
      result: '',
      console: '',
      lastNodeId: 0,
      tagDefs: undefined,
      isHighlighted: false,
      dirty: true
    }
  }

  findTab(title: string) {
    for (let i = 0; i < this.tabs.length; i++) {
      if (instanceOf(this.tabs[i], title)) {
        return this.tabs[i]
      }
    }
    return null
  }

  newTab(title: string) {
    this.layout.root.contentItems[0].addChild({
      type: 'component',
      componentName: 'tab',
      title: title,
      componentState: { tab: title }
    })
    this.refresh()
  }

  startInteractive(steps: any) {
    if (steps.nodes.length != 1) {
      console.log('impossible initialise interactive mode')
      return
    }
    // Create initial node
    let init = steps.nodes[0]
    init.isVisible = true
    init.isLeaf = true
    init.isTau = false
    this.state.graph.clear()
    this.state.graph.nodes.add(init)
    this.state.lastNodeId = 1
    // Update interactive tabs
    this.tabs.map(tab => tab.updateGraph(this.state.graph))
  }

  newInteractiveTab(steps: any) {
    this.layout.root.contentItems[0].addChild({
      type: 'column',
      content: [{
        type: 'component',
        componentName: 'tab',
        title: 'Interactive',
        componentState: { tab: 'Interactive' }
      }]
    })
    this.refresh()
    this.startInteractive(steps)
  }

  isInteractiveOpen() {
    for (let i = 0; i < this.tabs.length; i++) {
      if (this.tabs[i] instanceof TabInteractive) return true
    }
    return false
  }

  clearInteractive() {
    this.state.graph.clear()
    if (this.state.status == 'success' && this.isInteractiveOpen()) {
      //@ts-ignore
      ui.request('Step', (data) => {
        this.mergeState(data.state)
        this.startInteractive(data.steps)
      })
    }
    this.fit()
  }

  // TODO: this is wrong, this tree is not a graph
  updateInteractive(activeId: Common.ID, tree: Graph) {
    // Give a better label to the node (TODO)
    const nodeLabel = (str: string) => {
      if (str == 'Step_eval(first operand of a Create)')
        return 'Eval first operand of create'
      if (str == 'Step_eval(Esseq)')
        return 'Eval strong sequencing'
      if (str == 'Step_eval(Ewseq)')
        return 'Eval weak sequencing'
      if (str == 'Step_eval(Epure)')
        return 'Eval pure expression'
      if (str == 'Step_tau(End)')
        return 'Non deterministic choice'
      return str
    }

    // Check node is a tau transition
    const isTau = (n: Node) => _.includes(n.label, "tau") && !_.includes(n.label, "End")

    const isTauById = (nId: Common.ID) => isTau(graph.nodes.get(nId))

    // Return immediate edge upward
    const getIncommingEdge = (nId: Common.ID) => _.find(graph.edges.get(), n => n.to == nId)

    // Search for a no tau parent
    const getNoTauParent: (_:Common.ID) => Common.ID | undefined = (nId: Common.ID) => {
      const e = getIncommingEdge(nId)
      if (!e || !e.from) {
        Util.error('Could not find incomming edge!')
        return
      }
      if (isTauById(e.from))
        return getNoTauParent(e.from)
      return e.from
    }

    const graph = this.state.graph
    let lastLeafNodeId = null

    // Update tree nodes labels
    tree.nodes.map((n) => n.label = nodeLabel(n.label))

    // Update current point to become branch
    const active = graph.nodes.get(activeId)
    active.group = 'branch'
    active.state = null
    graph.nodes.update(active)

    // Add nodes
    tree.nodes.map((n) => {
      n.isTau = isTau(n)
      n.isVisible = false
      graph.nodes.add(n)
      if (n.group == 'leaf') lastLeafNodeId = n.id
    })

    // Edges are added twice (for tau transitions)
    tree.edges.map((e) => {
      e.isTau = true
      graph.edges.add(e)
    })
    tree.edges.map((e) => {
      const n = graph.nodes.get(e.to)
      if (!n.isTau)
        graph.edges.add({from: getNoTauParent(e.to), to: e.to, isTau: false})
    })

    // Set visible all tau nodes descendent from active until first non-tau
    graph.setChildrenVisible(activeId)

    // Update any instance of interactive
    this.tabs.map((tab) => tab.updateGraph(graph))

    // WARN: Assume tree node is decreasing order
    // This is a seed to the server
    //@ts-ignore
    this.state.lastNodeId = tree.nodes[0].id
  }

  getEncodedState() {
    let miniConfig = GoldenLayout.minifyConfig(this.layout.toConfig())
    miniConfig.title = this.source.title
    miniConfig.source = this.source.getValue()
    return encodeURIComponent(JSON.stringify(miniConfig))
  }

  // Return this first instance (or create a new one)
  getTab(title: string) {
    let tab = this.findTab(title)
    if (tab == null) {
      this.newTab(title)
      tab = this.findTab(title)
    }
    return tab
  }
  getExec()          { return this.getTab('Execution') }
  getCabs()          { return this.getTab('Cabs') }
  getAil()           { return this.getTab('Ail') }
  getCore()          { return this.getTab('Core') }
  getConsole()       { return this.getTab('Console') }
  getInteractive()   { return this.getTab('Interactive') }

  clear() {
    this.tabs.map((tab) => tab.clear())
  }

  mark(loc: any) {
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

  refresh () {
    this.tabs.map((tab) => tab.refresh())
    this.layout.updateSize()
  }

  updateMemory(mem: Graph) {
    const nodes: Node[] = []
    const edges: Edge[] = []
    const toHex = (n:number) => { return "0x" + ("00" + n.toString(16)).substr(-2) }
    const isPointer = (type:string) => {
      return type.slice(-1) == '*'
    }
    const updateConcreteMemory = () => {
      let readValue = (id:Common.ID, base:any, end:any) => {
        let value = 0
        //@ts-ignore
        const map = mem.bytemap
        if (!map[base]) return 'unspecified' // undefined value in allocation
        if (map[base].prov) // Has a provenance
        //@ts-ignore
          edges.push({from: id, to: map[base].prov})
        for (let i = base; i < end; i++)
          if (map[i]) value += map[i].value
        return value
      }
        //@ts-ignore
      Object.keys(mem.allocations).map((k) => {
        //@ts-ignore
        const alloc = mem.allocations[k]
        const base = parseInt(alloc.base)
        const end  = parseInt(alloc.base) + parseInt(alloc.size)
        const value = (isPointer(alloc.type)) ? ''
                        : '\n<i>Value:</i> ' + readValue(k, base, end)
        const type  = '\n<i>Type:</i> ' + alloc.type
        const title  = '<i>Base address:</i> ' + toHex(base)
        const size  = '\n<i>Size:</i> ' + alloc.size
        const label = title + type + size + value
        //@ts-ignore
        nodes.push({id: k, label: label})
      })
    }
    const updateSymbolicMemory = () => {
      Object.keys(mem).map((k) => {
        //@ts-ignore
        const alloc = mem[k]
        const type  = '<i>Type:</i> ' + alloc.type
        const value = '\n<i>Value:</i> ' + alloc.value
        const label = type + value
        //@ts-ignore
        nodes.push({id: k, label: label})
      })
    }
        //@ts-ignore
    if (mem.allocations)
      updateConcreteMemory()
    else
      updateSymbolicMemory()
    // Save in case another memory tab is open
    this.state.mem = new Graph(nodes, edges)
    this.tabs.map((tab) => tab.updateMemory(this.state.mem))
  }

  mergeState (s: Common.State) {
    if (s.status == 'failure') {
      this.setStateEmpty()
        //@ts-ignore
      this.console.setActive()
    }
    if (s.tagDefs == null) s.tagDefs = this.state.tagDefs // avoid lose info
    _.assign(this.state, s) // merge states
    this.state.isHighlighted = false
    this.state.dirty = false
  }

}
