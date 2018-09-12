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

    this.on('step', this, this.execGraphNodeClick)
    this.on('resetInteractive', this, this.resetInteractive)
    this.on('setMemory', this, this.setMemory)
    this.on('updateDOT', this, this.updateDOT)
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
      result: '',
      console: '',
      lastNodeId: 0,
      tagDefs: undefined,
      dirty: true,
      graph: new Graph(),
      hide_tau: true,
      skip_tau: true,
      eager_mem: true,
      dotMem: '',
      dotExecGraph: '',
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
    init.selected = true
    init.can_step = true
    this.state.graph.clear()
    this.state.graph.nodes.push(init)
    this.state.lastNodeId = 0
    this.updateDOT()
  }

  /** Restart interactive mode in all the tabs */
  resetInteractive() {
    this.state.graph.clear()
    this.emit('clearGraph')
    if (this.findTab('Interactive')) {
      UI.request(Common.Step(), (data: Common.ResultRequest) => {
        this.updateState(data)
      })
    }
  }

  /** Update DOT and raise an event to update interactive graph */
  updateDOT() {
    const graph = this.state.graph
    const dotHead = 'digraph Memory { node [shape=box, fontsize=12];'
    const nodes = this.state.hide_tau
                ? _.filter(graph.nodes, n => !n.isTau && n.isVisible)
                : _.filter(graph.nodes, n => n.isVisible)
    const edges = _.filter(graph.edges, e => this.state.hide_tau ? !e.isTau : e.isTau)
    const dotNodes = _.reduce(nodes, (acc, n) => 
      acc + 'n' + n.id + '['
      + 'href="javascript:UI.execGraphNodeClick('+n.id+')",'
      + (n.selected ? 'color="blue", ' : '')
      + (n.can_step ? 'fontcolor="blue", ' : '')
      + 'label=<' + (n.can_step ? '<u>' + n.label + '</u>' : n.label) + '>'
      + '];', '')
    const dotEdges = _.reduce(edges, (acc, e) => {
      if (graph.nodes[e.from].isVisible && graph.nodes[e.to].isVisible)
        return acc + 'n' + e.from + '->n' + e.to + ';'
      else return acc
    }, '')
    this.state.dotExecGraph = dotHead + dotNodes + dotEdges + '}'
    // Update any instance of interactive
    this.emit('updateGraph')
  }

  setChildrenVisible(nID, last = false) {
    const graph = this.state.graph
    let children
    if (this.state.skip_tau) {
      graph.tauChildrenTransClosure(nID).map(nID => graph.nodes[nID]).map(child => child.isVisible = true)
      children = graph.nonTauChildren(nID).map(nID => graph.nodes[nID])
      children.map(child => child.isVisible = true)
    } else {
      children = graph.tauChildren(nID).map(nID => graph.nodes[nID])
      if (children.length > 0) {
        children.map(child => child.isVisible = true)  
      } else {
        children = graph.children(nID).map (nID => graph.nodes[nID])
        children.map(child => child.isVisible = true)  
      }
    }
    if (!last && this.state.eager_mem && children.length > 0) {
      const label = children[0].label
      if (label == 'CreateRequest' || label == 'StoreRequest' || label == 'KillRequest')
        children = this.setChildrenVisible(children[0].id, true)
      else if (label != 'Non deterministic choice')
        children = this.setChildrenVisible(children[0].id)
    }
    return children
  }

  /** Update interactive display state and raise event to update DOT */
  executeInteractiveStep(activeId) {
    const children = this.setChildrenVisible(activeId)
    children.map(child => child.can_step = true)
    this.state.graph.nodes.map(n => n.selected = false)
    if (children.length > 0) {
      children[0].selected = true
      this.setMemory(children[0].mem)
      this.emit('clear')
      if (children[0].loc)
        this.emit('markInteractive', children[0].loc)
    }
    this.updateDOT();
  }

  /** Update interactive state mode and raise event to update DOT */
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
    const isTau = (n: Node) => n && _.includes(n.label, "tau") && !_.includes(n.label, "End")
    const isTauById = (nId: Common.ID) => isTau(graph.nodes[nId])
    // Return immediate edge upward
    const getIncommingEdge = (nId: Common.ID) => _.find(graph.edges, n => n.to == nId)
    // Search for a no tau parent
    const getNoTauParent: (_:Common.ID) => Common.ID | undefined = (nId: Common.ID) => {
      const e = getIncommingEdge(nId)
      if (e == undefined || e.from == undefined)
        throw new Error('Could not find incomming edge!')
      if (isTauById(e.from))
        return getNoTauParent(e.from)
      return e.from
    }
    // This is a seed to the server
    this.state.lastNodeId = tree.nodes[0].id
    tree.nodes.reverse()
    const graph = this.state.graph
    // Update tree nodes labels
    tree.nodes.map((n) => n.label = nodeLabel(n.label))
    // Update current point to become branch
    const active = graph.nodes[activeId]
    if (!active) {
      alert('point active error')
      return
    }
    active.can_step = false
    delete active.state
    // Add nodes
    tree.nodes.map((n) => {
      n.isTau = isTau(n)
      n.isVisible = false
      graph.nodes.push(n)
    })
    // Edges are added twice (for tau transitions)
    tree.edges.map((e) => {
      e.isTau = true
      graph.edges.push(e)
    })
    tree.edges.map((e) => {
      const n = _.find(graph.nodes, n => n.id == e.to)
      if (n && !n.isTau) {
        const from = getNoTauParent(e.to)
        if (from != undefined)
          graph.edges.push({from: from, to: e.to, isTau: false})
      }
    })
    // Set visible nodes descendent from active
    this.executeInteractiveStep(activeId)
  }

  /** Execute a step (it might call the server to update interactive state) */
  execGraphNodeClick(activeId: Common.ID) {
    if (this.state.graph.children(activeId).length == 0)
      UI.step(this.state.graph.nodes[activeId])
    else {
      const active = this.state.graph.nodes[activeId]
      if (active.can_step) {
        active.can_step = false
        this.executeInteractiveStep(activeId)
      } else  {
        this.setMemory(active.mem)
        this.emit('clear')
        if (active.loc)
          this.emit('markInteractive', active.loc)
      }
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

  // TODO: CHECK IF I REALLY NEED UNDEFINED
  setMemory(mem: Common.Memory | undefined) {
    if (mem === undefined) return
    const toHex = (n:number) => { return "0x" + ("00" + n.toString(16)).substr(-2) }
    const createNode = (alloc: Common.MemoryAllocation) => {
      if (alloc.prefix == null) // HACK! TODO: check malloc case
        return ''
      const box = (n, ischar=false) =>
        '<td width="7" height="'+(ischar?'20':'7')+'" fixedsize="true" port="'+String(n)
        +'"><font point-size="1">&nbsp;</font></td>'
      const maxcols = _.reduce(alloc.rows, (acc, row) => Math.max(acc, row.path.length), 0)+1
      const tooltip = "allocation: " + String(alloc.id)
      const title =
        '<tr><td height="7" width="7" fixedsize="true" border="0">&nbsp;</td>'
          + '<td border="0" colspan="' + maxcols + '"><b>'
          + alloc.prefix + '</b>: <i>' + alloc.type + '</i>&nbsp;[' + toHex(alloc.base)
          + ']</td></tr>'
      let index = 0
      const body = _.reduce(alloc.rows, (acc, row) => {
        const p = _.reduce(row.path, (acc, tag) => {
          return acc + '<td rowspan="'+row.size+'">'+tag+'</td>'
        },'')
        const spath = _.reduce(row.path, (acc, tag) => acc + '_' + tag, '')
        const v = '<td port="'+ spath + 'v" rowspan="'+row.size+'" colspan="'+String(maxcols-row.path.length)+'"'
                +(row.ispadding?' bgcolor="grey"':'')+'>'+(row.pointsto === null ? row.value : toHex(parseInt(row.value)))+'</td>'
        acc += '<tr>' + box(index, row.size == 1)+p+v+'</tr>'
        index++
        for (let j = 1; j < row.size; j++, index++)
          acc += '<tr>' + box(index) + '</tr>'
        return acc
      }, '')
      const lastrow = '<tr border="0"><td border="0" width="7" height="7" fixedsize="true" port="'+String(alloc.size)+'"><font point-size="1">&nbsp;</font></td></tr>'
      return 'n'+alloc.id+'[label=<<table border="0" cellborder="1" cellspacing="0" >'+title+body+lastrow+'</table>>, tooltip="'+tooltip+'"];'
    }
    type Pointer = {from: string /*id path*/, to: number /*prov*/, addr: number /*pointer*/}
    const getPointersInAlloc = (alloc: Common.MemoryAllocation) => {
      if (alloc.prefix === null) return []
      return _.reduce(alloc.rows, (acc: Pointer[], row) => {
        if (row.pointsto !== null) {
          const from = _.reduce(row.path, (acc, tag) => acc + '_' + tag, 'n'+alloc.id + ':')
          const p: Pointer = {from: from, to: row.pointsto, addr: parseInt(row.value)}
          return _.concat(acc, [p])
        } else {
          return acc
        }
      }, [])
    }
    const createEdges = (ps: Pointer[], mem: Common.Memory) => {
      return _.reduce(ps, (acc, p) => {
        const target = _.find(mem, alloc => alloc.base <= p.addr && p.addr < alloc.base + alloc.size)
        if (target) {
          const offset = p.addr - target.base
          acc += p.from + "v->n" + target.id + ':' + offset + (target.id != p.to ? '[color="red"]': '') + ';'
        } else {
          const toprov = _.find(mem, alloc => alloc.id == p.to)
          if (toprov) {
            const offset = p.addr - toprov.base
            acc += p.from + "v->n" + toprov.id + ':' + offset + '[color="red"];'
          } else {
            // TODO: WHAT SHOULD I DO?
            // POINTER TO UNKNOWN MEMORY
          }
        }
        return acc;
      }, '')
    }
    const g = 'digraph Memory { node [shape=none, fontsize=12]; rankdir=LR;'
    const ns = _.reduce(mem, (ns, alloc) => ns + createNode(alloc), '')
    const ps: Pointer[] = _.reduce(mem, (acc: Pointer[], alloc) => _.concat(acc, getPointersInAlloc(alloc)), [])
    const es = createEdges(ps, mem)
    this.state.dotMem = g + ns + es + '}' // Save in case another memory tab is open 
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
      case 'interactive':
        this.state.tagDefs = res.tagDefs
        this.state.ranges = res.ranges
        this.state.console = ''
        this.startInteractive(res.steps)
        break;
      case 'stepping':
        this.state.result = res.result
        this.state.console = ''
        this.updateInteractive(res.activeId, res.steps)
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
