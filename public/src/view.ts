import $ from "jquery"
import GoldenLayout from "golden-layout"
import _ from "lodash"
import { Node, Edge, Graph } from "./graph"
import Tabs from "./tabs"
import Util from "./util"
import Common from './common'
import UI from './ui'

export default class View {
  title: string
  dom: JQuery<HTMLElement>

  public tabs: Tabs.Tab[]

  private source: Tabs.Source

  /** Golden Layout */
  private layout!: GoldenLayout;

  /** Private state */
  private state!: Common.State;

  /** Highlight has already been performed */
  private isHighlighted: boolean

  /** Source has been modified */
  private dirty: boolean

  /** Events */
  private events: { [eventName:string]: [any, Function][]; }

  /** Event Emitter */
  private ee: Common.EventEmitter

  constructor (title: string, data: string, config?: GoldenLayout.Config) {
    this.tabs = []
    this.events = {}
    this.ee = {
      on: (e: Common.Event, l: any, f: Function) => this.on(e, l, f),
      off: (f) => this.off(f),
      once: (f => f(this.state)),
      emit: (e: Common.Event, ...args: any[]) => this.emit (e, ...args)
    }
    this.dirty = true
    this.on('dirty', this, () => this.dirty = true)
    this.title  = title
    this.isHighlighted = false
    this.setStateEmpty()

    this.source = new Tabs.Source(title, data, this.ee)
    this.tabs.push(this.source)

    this.dom = $('<div class="view"></div>')
    $('#views').append(this.dom)
    this.initLayout(config)

    this.on('step', this, this.step)
    this.on('resetInteractive', this, this.resetInteractive)
    this.on('setMemory', this, this.setMemory)
  }

  private initLayout(config?: GoldenLayout.Config) {
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
    interface ContentItem extends GoldenLayout.ContentItem {
      componentName: string
      content: Tabs.Tab
    }
    let self = this // WARN: Golden Layout does not work with arrow function
    this.layout = new GoldenLayout (config, this.dom);
    this.layout.registerComponent('source', function (container: GoldenLayout.Container, state: any) {
      (container.parent as ContentItem).content = self.source
      container.getElement().append(self.source.dom)
      self.source.refresh()
    })
    this.layout.registerComponent('tab', function (container: GoldenLayout.Container, state: any) {
      const tab = Tabs.create(state.tab, self.ee)
      self.tabs.push(tab);
      (container.parent as ContentItem).content = tab
      container.getElement().append(tab.dom)
      container.setState(state)
      tab.update(self.state)
      tab.refresh()
      const unsafeTab: any = tab
      if (unsafeTab.highlight && UI.getSettings().colour)
        unsafeTab.highlight(self.state)
    })
    this.layout.on('itemDestroyed', (c: ContentItem) => {
      if (c.componentName == 'tab') {
        for (let i = 0; i < this.tabs.length; i++) {
          if (this.tabs[i] === c.content) {
            this.tabs.splice(i, 1)
            break
          }
        }
        this.off(c.content)
      }
    })
    this.layout.on( 'tabCreated', (header: GoldenLayout.Tab) => {
      if (header.contentItem.isComponent) {
        let tab = (header.contentItem as ContentItem).content
        header.element.on('mousedown', () => tab.refresh())
        tab.setActive = () => Util.triggerClick(header.element[0])
      }
    })
    this.layout.init()
  }

  private setStateEmpty() {
    this.state = {
      title: () => this.title,
      source: () => this.source.getValue(),
      pp: { cabs: '', ail:  '', core: '' },
      ast: { cabs: '', ail:  '', core: '' },
      locs: [],
      graph: new Graph(),
      mem: new Graph(),
      result: '',
      console: '',
      lastNodeId: 0,
      tagDefs: undefined,
      dirty: true
    }
  }

  findTab(title: string) {
    for (let i = 0; i < this.tabs.length; i++) {
      if (Tabs.instanceOf(this.tabs[i], title)) {
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

  /** Start interactive tabs (with the first state Init) */
  startInteractive(steps: Common.ResultTree) {
    if (steps.nodes.length != 1) {
      console.log('impossible initialise interactive mode')
      return
    }
    // Create initial node
    let init = steps.nodes[0]
    init.isVisible = true
    init.isTau = false
    this.state.graph.clear()
    this.state.graph.nodes.add(init)
    this.state.lastNodeId = 1
    // Update interactive tabs
    this.emit('updateGraph')
  }

  /** Create a new interactive tab and update its graph */
  newInteractiveTab(steps: Common.ResultTree) {
    let start = !this.isInteractiveOpen()
    this.layout.root.contentItems[0].addChild({
      type: 'column',
      content: [{
        type: 'component',
        componentName: 'tab',
        title: 'Interactive',
        componentState: { tab: 'Interactive' }
      }]
    })
    if (start)
      this.startInteractive(steps)
    else
      this.emit('updateGraph')
  }

  /** Check if there are interactive tabs opened */
  private isInteractiveOpen() {
    for (let i = 0; i < this.tabs.length; i++) {
      if (this.tabs[i] instanceof Tabs.Interactive) return true
    }
    return false
  }

  /** Restart interactive mode in all the tabs */
  resetInteractive() {
    this.state.graph.clear()
    this.emit('clearGraph')
    if (this.isInteractiveOpen()) {
      UI.request(Common.Step(), (data: Common.ResultStep) => {
        this.updateState(data.state)
        this.startInteractive(data.steps)
      })
    }
  }

  /** Update interactive state mode and raise event to update graphs */
  updateInteractive(activeId: Common.ID, tree: Common.ResultTree) {
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
      if (!e || !e.from)
        throw new Error('Could not find incomming edge!')
      if (isTauById(e.from))
        return getNoTauParent(e.from)
      return e.from
    }
    const graph = this.state.graph
    // Update tree nodes labels
    tree.nodes.map((n) => n.label = nodeLabel(n.label))
    // Update current point to become branch
    const active = graph.nodes.get(activeId)
    active.group = 'branch'
    delete active.state
    graph.nodes.update(active)
    // Add nodes
    tree.nodes.map((n) => {
      n.isTau = isTau(n)
      n.isVisible = false
      graph.nodes.add(n)
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
    this.emit('updateGraph')
    // WARN: Assume tree node is decreasing order
    // This is a seed to the server
    this.state.lastNodeId = tree.nodes[0].id
  }

  /** Execute a step (it might call the server to update interactive state) */
  step(active: Node) {
    if (this.state.graph.children(active.id).length == 0)
      UI.step(active)
    else {
      active.group = 'branch'
      this.state.graph.nodes.update(active)
      this.state.graph.setChildrenVisible(active.id)
      this.emit('updateGraph')
    }
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
      tab = <Tabs.Tab>this.findTab(title)
    }
    return tab
  }

  getSource(): Readonly<Tabs.Source> {
    return this.source
  }

  getExec() {
    return this.getTab('Execution')
  }

  getConsole() {
    return this.getTab('Console')
  }

  getMemory() {
    return this.getTab('Memory')
  }

  show() {
    this.dom.show()
  }

  hide() {
    this.dom.hide()
  }

  refresh () {
    this.tabs.map((tab) => tab.refresh())
    this.layout.updateSize()
  }

  setMemory(mem: any) {
    if (mem === undefined) mem = {allocations: {}}
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
    this.getMemory().setActive()
    this.emit('updateMemory')
  }

  isDirty(): Readonly<boolean> {
    return this.dirty
  }

  getState(): Readonly<Common.State> {
    return this.state
  }

  updateState(res: Common.ResultRequest) {
    switch (res.status) {
      case 'elaboration':
        this.state.pp = res.pp
        this.state.ast = res.ast
        this.state.locs = res.locs
        this.state.console = ''
        break
      case 'execution':
        this.state.result = res.result
        this.state.console = ''
        break
      case 'stepping':
        this.state.result = res.result // TODO: not sure about this
        if (res.tagDefs) this.state.tagDefs = res.tagDefs
        this.state.console = ''
        break
      case 'failure':
        this.setStateEmpty()
        this.state.console = res.console
        this.getConsole().setActive()
        break
    }
    this.isHighlighted = false
    this.dirty = false
  }

  on(e: Common.Event, l: any, f: Function) {
    let listeners = this.events[e]
    if (!listeners) {
      listeners = []
      this.events[e] = listeners
    }
    listeners.push([l, f])
  }

  off(e_l: any) {
    if (typeof e_l === 'string') { // If an event name
      this.events[e_l] = []
    } else { // If a listener (unsubscribe all)
      for (const e in this.events) {
        this.events[e] = this.events[e].filter(listener => listener[0] !== e_l)
      }
    }
  }

  emit(e: string, ...args: any[]) {
    const settings = UI.getSettings()
    switch (e) {
      case 'highlight':
        if (this.isHighlighted || !settings.colour || this.dirty) return
        this.isHighlighted = true
        break;
      case 'clear':
        this.isHighlighted = false
        break;
      case 'mark':
        if (!settings.colour_cursor || this.dirty) return
        break;
    }
    console.log(e)
    const listeners = this.events[e]
    args.push(this.state)
    if (listeners)
      listeners.map(listener => listener[1].apply(listener[0], args))
  }

}
