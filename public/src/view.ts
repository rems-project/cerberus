import $ from "jquery"
import GoldenLayout from "golden-layout"
import { pull, filter, reduce, find, concat, includes, startsWith, endsWith } from "lodash"
import { Node, Graph, ID, GraphFragment } from "./graph"
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
    this.on('dirty', this, () => {
      if (!this.dirty) {
        this.state.graph.clear()
        this.state.history = []
        this.state.step_counter = 0
        delete this.state.tagDefs
        this.state.arena = this.state.dotMem = this.state.dotExecGraph = ''
        this.emit('updateArena')
        this.emit('updateMemory')
        //this.emit('updateExecution')
        this.emit('updateExecutionGraph')
        this.dirty = true
      }
    })
    this.title  = title
    this.isHighlighted = false
    this.setStateEmpty()

    this.source = new Tabs.Source(title, data, this.ee)
    this.tabs.push(this.source)

    this.dom = $('<div class="view"></div>')
    $('#views').append(this.dom)
    this.initLayout(config)
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
              //component('Execution'),
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
      tab.initial(self.state)
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
      //result: '',
      console: '',
      switches: ['integer_provenance'],
      lastNodeId: 0,
      tagDefs: undefined,
      dirty: true,
      arena: '',
      history: [],
      graph: new Graph(),
      step_counter: 0,
      stdout: '',
      exec_options: [],
      hide_tau: true,
      skip_tau: true,
      mode: Common.InteractiveMode.Memory,
      dotMem: '',
      dotExecGraph: '',
    }
  }

  toggleSwitch (sw: string): void {
    if (!includes(this.state.switches, sw))
      this.state.switches.push(sw)
    else
      pull(this.state.switches, sw)
  }

  toggleProvSwitch (sw: string): void {
    pull(this.state.switches,
      'integer_provenance', 'no_integer_provenance',
      'no_integer_provenance_v1', 'no_integer_provenance_v4')
    this.state.switches.push(sw)
  }

  getSwitches(): string[] {
    return this.state.switches
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
  startInteractive(steps: GraphFragment) {
    if (steps.nodes.length != 1)
      throw new Error('impossible initialise interactive mode')
    let init = steps.nodes[0]
    init = { ...init,
      isVisible: true,
      isTau: false,
      selected: true,
      can_step: true
    }
    this.state.graph.clear()
    this.state.graph.nodes.push(init)
    this.state.lastNodeId = 0
    this.execGraphNodeClick(0)
  }

  /** Restart interactive mode in all the tabs */
  resetInteractive() {
    this.state.history = []
    this.state.graph.clear()
    this.state.step_counter = 0
    this.state.console = ''
  }

  /** Restart interactive execution */
  restartInteractive() {
    this.resetInteractive()
    this.emit('updateExecution')
    UI.step(null)
  }

  /** Update execution graph DOT */
  updateExecutionGraph() {
    const graph = this.state.graph
    const dotHead = 'digraph Memory { node [shape=box, fontsize=12]; edge [fontsize=10];'
    const nodes = this.state.hide_tau
                ? filter(graph.nodes, n => !n.isTau && n.isVisible)
                : filter(graph.nodes, n => n.isVisible)
    const edges = filter(graph.edges, e => this.state.hide_tau ? !e.isTau : e.isTau)
    const label = (n : Node) => {
      if (n.arena) {
        if (n.arena.length > 30)
          return n.arena.substring(0,30) + '...'
        return n.arena
      }
      return n.info.debug
    }
    const dotNodes = reduce(nodes, (acc, n) => 
      acc + `n${n.id}[href="javascript:UI.execGraphNodeClick(${n.id})",`
      + (n.selected ? 'color="blue", ' : '')
      + (n.can_step ? 'fontcolor="blue", ' : '')
      + (n.id == 0 ? 'style=invis, height=0, width=0, ' : '')
      + `label="${label(n)}"];`, '')
    const dotEdges = reduce(edges, (acc, e) => {
      if (graph.nodes[e.from].isVisible && graph.nodes[e.to].isVisible) {
        const label = graph.nodes[e.from].info.kind
        return acc + `n${e.from}->n${e.to}[label="${label}"];`
      }
      else return acc
    }, '')
    this.state.dotExecGraph = dotHead + dotNodes + dotEdges + '}'
    this.emit('updateExecutionGraph')
  }

  private setMemory(mem: Common.Memory | undefined) {
    if (mem === undefined) return
    const trackProvInteger = includes(this.state.switches, 'integer_provenance')
    const toHex = (n:number) => { return "0x" + ("00" + n.toString(16)).substr(2) }
    const createNode = (alloc: Common.MemoryAllocation) => {
      if (alloc.prefix == null) // HACK! TODO: check malloc case
        return ''
      // TODO: bit of a hack, change later!
      if (alloc.prefix == 'string literal') return ''
      if (startsWith(alloc.prefix, 'Core')) return ''
      // TODO: THIS IS ANOTHER HACK!!
      if (startsWith(alloc.prefix, '__'))
        return ''
      const box = (n:number, ischar=false) =>
        `<td width="7" height="${ischar?'20':'7'}" fixedsize="true" port="${String(n)}">
          <font point-size="1">&nbsp;</font>
         </td>`
      const maxcols = alloc.rows.reduce((acc, row) => Math.max(acc, row.path.length), 0)+1
      const tooltip = "allocation: " + String(alloc.id)
      const title =
        `<tr>
          <td height="7" width="7" fixedsize="true" border="0">&nbsp;</td>
          <td border="0" colspan="${maxcols}"><b>${alloc.prefix}</b>: <i>${alloc.type}</i>&nbsp;[@${alloc.id}, ${toHex(alloc.base)}]</td>
         </tr>`
      let index = 0
      const body = alloc.rows.reduce((acc, row) => {
        const head    = row.path.reduce((acc, tag) =>
                          `${acc}<td rowspan="${row.size}">${tag}</td>`, '')
        const spath   = row.path.reduce((acc, tag) => acc + '_' + tag, '')
        const colspan = String(maxcols-row.path.length)
        const color   = row.ispadding ? ' bgcolor="grey"' : ''
        const prov    = row.prov != undefined ? ( trackProvInteger || !row.dashed ? `@${row.prov}, ` : '') : ''
        const value   = row.hex ? toHex(parseInt(row.value)) : row.value
        const body = `<td port="${spath}v" rowspan="${row.size}"
                          colspan="${colspan}" ${color}>${prov}${value}</td>`
        acc += `<tr>${box(index, row.size == 1)}${head}${body}</tr>`
        index++
        for (let j = 1; j < row.size; j++, index++)
          acc += `<tr>${box(index)}</tr>`
        return acc
      }, '')
      const lastrow =
        `<tr border="0">
          <td border="0" width="7" height="7" fixedsize="true"
              port="${String(alloc.size)}">
            <font point-size="1">&nbsp;</font>
          </td>
         </tr>`
      return `n${alloc.id}[label=<
        <table border="0" cellborder="1" cellspacing="0">
          ${title}${body}${lastrow}
         </table>>, tooltip="${tooltip}"];`
    }
    type Pointer = {from: string /*id path*/, to: number /*prov*/, addr: number /*pointer*/, dashed: boolean}
    const getPointersInAlloc = (alloc: Common.MemoryAllocation) => {
      if (alloc.prefix === null) return []
      // THIS IS A TERRIBLE HACK:
      if (startsWith(alloc.prefix, 'arg')) return []
      if (startsWith(alloc.prefix, 'Core')) return []
      return alloc.rows.reduce((acc: Pointer[], row) => {
        if (row.pointsto !== null) {
          const from = row.path.reduce((acc, tag) => acc + '_' + tag, `n${alloc.id}:`)
          const p: Pointer = {from: from, to: row.pointsto, addr: parseInt(row.value), dashed: row.dashed}
          return concat(acc, [p])
        } else {
          return acc
        }
      }, [])
    }
    const createEdges = (ps: Pointer[], mem: Common.Memory) => {
      return reduce(ps, (acc, p) => {
        const target = find(mem, alloc => alloc.base <= p.addr && p.addr < alloc.base + alloc.size)
        const dashed = p.dashed ? 'style="dashed"' : 'style="solid"'
        if (target) {
          const offset = p.addr - target.base
          const color  = target.id != p.to && trackProvInteger ? ',color="red"': ''
          acc += `${p.from}v->n${target.id}:${offset}[${dashed}${color}];`
        } else {
          const toprov = find(mem, alloc => alloc.id == p.to)
          if (toprov) {
            const offset = p.addr - toprov.base
            acc += `${p.from}v->n${toprov.id}:${offset}[${dashed},color="red"];`
          } else {
            // TODO: WHAT SHOULD I DO?
            // POINTER TO UNKNOWN MEMORY
          }
        }
        return acc;
      }, '')
    }
    const g = 'digraph Memory { node [shape=none, fontsize=12]; rankdir=LR;'
    const ns = reduce(mem, (ns, alloc) => ns + createNode(alloc), '')
    const ps: Pointer[] = reduce(mem, (acc: Pointer[], alloc) => concat(acc, getPointersInAlloc(alloc)), [])
    const es = createEdges(ps, mem)
    this.state.dotMem = g + ns + es + '}' // Save in case another memory tab is open 
    this.getMemory().setActive()
    this.emit('updateMemory')
  }

  private executeInteractiveMode(nID: ID, skip_tau: boolean, lastCline?: number): Node[] {
    let children = this.state.graph.setChildrenVisible(nID, skip_tau)
    if (children.length == 1) {
      const active = children[0]
      switch (this.state.mode) {
        case Common.InteractiveMode.Memory:
          switch (active.info.kind) {
            case 'action request':
            case 'done':
              children = this.state.graph.setChildrenVisible(active.id, skip_tau)
              break
            default:
              children = this.executeInteractiveMode(active.id, skip_tau, lastCline)
              break
          }
          break
        case Common.InteractiveMode.Core:
          // Nothing to do
          break
        case Common.InteractiveMode.CLine:
          if (lastCline != undefined && active.loc != undefined && lastCline == active.loc.c.begin.line)
            children = this.executeInteractiveMode(active.id, skip_tau, lastCline)
          break
      }
    }
    return children
  }

  private setActiveInteractiveNode(active: Node) {
    // Arena
    this.state.arena = `-- Environment:\n${active.env}-- Arena:\n${active.arena}`
    this.emit('updateArena')
    // Memory graph
    this.setMemory(active.mem)
    // Locations
    this.emit('clear')
    if (active.loc) this.emit('markInteractive', active.loc)
  }

  /** Update interactive display state and raise event to update DOT */
  private executeInteractiveStep(activeId: ID) {
    const active = this.state.graph.nodes[activeId]
    const lastCline = (active.loc && active.loc.c ? active.loc.c.begin.line : undefined)
    let children = this.executeInteractiveMode(activeId, this.state.skip_tau, lastCline)

    if (children.length == 0) {
      alert ('Internal error: active node has no children')
      throw new Error('active node has no children')
    }

    const firstChoice = children[0]
    const lastNode =
      children.length == 1 && this.state.graph.children(firstChoice.id).length == 0

    if (firstChoice.info.file && (endsWith(firstChoice.info.file, '.h') || endsWith (firstChoice.info.file, '.core'))) {
      this.executeInteractiveStep(firstChoice.id)
      return
    }

    this.state.graph.nodes.map(n => n.selected = false)
    this.state.history.push(activeId)

    this.state.step_counter += 1
    this.state.exec_options = children.map(n => n.id)

    children.map(child => child.can_step = !lastNode)
    firstChoice.selected = !lastNode

    this.setActiveInteractiveNode(firstChoice)
    this.updateExecutionGraph();

    if (firstChoice.outp != this.state.stdout) {
      this.state.stdout = firstChoice.outp
    }
    this.state.console = this.state.stdout
    this.emit('updateExecution')
    
    if (lastNode) {
      this.state.exec_options = []
      this.getConsole().setActive()
      if (includes(firstChoice.info.kind, 'killed')) {
        // TODO: add location
        // the killed node has no location coming from cerberus
        const loc = firstChoice.info.error_loc && firstChoice.info.error_loc.begin ? ` at line ${firstChoice.info.error_loc.begin.line+1}` : ''
        this.state.console = `Unsuccessful termination of this execution:\n\t${firstChoice.info.kind.replace('killed', 'Undefined behaviour')}${loc}`
      } else {
        this.state.console = `Successful termination of this execution:\n\t${firstChoice.info.kind}`
      }
      this.emit('updateExecution')
    }

    /*
    if (children.length > 3) {
      this.getExecutionGraph().setActive()
    }
    */

    this.emit('updateStepButtons')
  }

  /** Update interactive state mode and update DOT */
  private updateInteractive(activeId: Common.ID, tree: GraphFragment) {
    // This is a seed to the server
    this.state.lastNodeId = tree.nodes[0].id
    tree.nodes.reverse()
    const graph = this.state.graph
    // Update current point to become branch
    const active = graph.nodes[activeId]
    if (!active)
      throw new Error('Active point in update Interactive is undefined!')
    active.can_step = false
    delete active.state
    // Add nodes
    tree.nodes.map((n) => {
      n.isTau = n && n.info.kind == 'tau' && tree.siblings(n.id).length == 1
      n.isVisible = false
      graph.nodes.push(n)
    })
    // Edges are added twice (for tau transitions)
    tree.edges.map((e) => {
      e.isTau = true
      graph.edges.push(e)
    })
    tree.edges.map((e) => {
      const n = find(graph.nodes, n => n.id == e.to)
      if (n && !n.isTau) {
        const from = graph.getNoTauParent(e.to)
        if (from != undefined)
          graph.edges.push({from: from, to: e.to, isTau: false})
      }
    })
    // Set visible nodes descendent from active
    this.executeInteractiveStep(activeId)
  }

  /** Execute a step (it might call the server to update interactive state) */
  execGraphNodeClick(activeId: Common.ID) {
    if (this.state.graph.children(activeId).length == 0) {
      // Node has no children, just ask more to the server
      // TODO: should check if it is the end or if there a state to ask
      UI.step(this.state.graph.nodes[activeId])
    } else {
      const active = this.state.graph.nodes[activeId]
      if (active.can_step) {
        // Node can step (it has hidden children)
        active.can_step = false
        this.executeInteractiveStep(activeId)
      } else  {
        // Just set the node as active
        this.setActiveInteractiveNode(active)
      }
    }
  }

  stepBack() {
    const activeId = this.state.history.pop()
    if (activeId == undefined)
      throw new Error('Already in the beginning!')
    const setChildrenInvisible = (nID: ID) => {
      this.state.graph.children(nID).map(nID => {
        const n = this.state.graph.nodes[nID]
        if (n.isVisible) {
          n.isVisible = false
          setChildrenInvisible(nID)
        }
      })
    }
    setChildrenInvisible(activeId)
    const active = this.state.graph.nodes[activeId]
    active.can_step = true
    this.state.graph.nodes.map(n => n.selected = false)
    active.selected = true
    this.state.exec_options = this.state.graph.siblings(active.id)
    this.state.step_counter -= 1
    this.setActiveInteractiveNode(active)
    this.updateExecutionGraph();
    this.emit('updateStepButtons')
  }

  stepForward() {
    if (this.state.graph.isEmpty()) {
      UI.step(null)
    } else {
      const active = find(this.state.graph.nodes, n => n.selected)
      if (active)
        this.execGraphNodeClick(active.id)
      else
        alert('No selected node.')
    }
  }

  stepForwardLeft() {
    this.execGraphNodeClick(this.state.exec_options[0])
  }

  stepForwardMiddle() {
    this.execGraphNodeClick(this.state.exec_options[1])
  }

  stepForwardRight() {
    this.execGraphNodeClick(this.state.exec_options[this.state.exec_options.length == 2 ? 1 : 2])
  }

  setInteractiveMode(mode: Common.InteractiveMode) {
    this.state.mode = mode
  }

  /** Toggle Hide/Skip Tau transition options  */
  toggleInteractiveOptions(flag: string) {
    // @ts-ignore: (flag: 'skip_tau' | 'hide_tau')/set
    this.state[flag] = !this.state[flag]
    // if we don't skip tau we should show the transitions
    this.state.hide_tau = this.state.skip_tau && this.state.hide_tau
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

  getConsole() {
    return this.getTab('Console')
  }

  getExecutionGraph() {
    return this.getTab('Interactive')
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
        this.state.console = res.result
        break
      case 'interactive':
        this.state.tagDefs = res.tagDefs
        this.state.ranges = res.ranges
        this.state.console = ''
        this.startInteractive(new GraphFragment(res.steps))
        break;
      case 'stepping':
        this.state.console = ''
        this.updateInteractive(res.activeId, new GraphFragment(res.steps))
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
    // DEBUG events
    //console.log(e)
    const listeners = this.events[e]
    args.push(this.state)
    if (listeners)
      listeners.map(listener => listener[1].apply(listener[0], args))
  }

}
