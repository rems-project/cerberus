import $ from "jquery"
import _ from "lodash"
import GoldenLayout from "golden-layout"
import { Range } from "./location"
import { Node, Graph, GraphFragment } from "./graph"
import Tabs from "./tabs"
import { triggerClick } from "./util"
import * as Memory from './memory'
import { State, Event, EventEmitter, InteractiveMode, ResultRequest } from './common'
import UI from './ui'
import bigInt from 'big-integer'

/** A view contains the state of a C program.
 * One can change a view in the dropdown in the top toolbar */
export default class View {
  title: string
  dom: JQuery<HTMLElement>

  public tabs: Tabs.Tab[]
  private source: Tabs.Source
  private layout!: GoldenLayout;
  public state!: State;

  /** Highlight has already been performed */
  private isHighlighted: boolean

  /** Source has been modified */
  private dirty: boolean

  /** Events */
  private events: { [eventName:string]: [any, Function][]; }

  /** Event emitter, the events are handled only for the current view */
  private ee: EventEmitter

  constructor (title: string, data: string, initial_state?: State, config?: GoldenLayout.Config) {
    this.tabs = []
    this.events = {}
    this.ee = {
      on: (e: Event, l: any, f: Function) => this.on(e, l, f),
      off: (f) => this.off(f),
      once: (f => f(this.state)),
      emit: (e: Event, ...args: any[]) => this.emit (e, ...args)
    }
    this.dirty = true
    this.on('dirty', this, () => {
      if (!this.dirty) {
        delete this.state.interactive
        this.state.bmc_executions = []
        this.emit('clear')
        this.emit('updateArena')
        this.emit('updateMemory')
        this.emit('updateExecutionGraph')
        this.emit('updateUI')
        this.dirty = true
      }
    })
    this.title  = title
    this.isHighlighted = false
    if (initial_state)
      this.state = initial_state
    else
      this.setStateEmpty()

    this.source = new Tabs.Source(title, data, this.ee)
    this.tabs.push(this.source)

    this.dom = $('<div class="view"></div>')
    $('#views').append(this.dom)
    this.initLayout(config)
    //this.getTab('Core').setActive()
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
              /*component('Stdout'),
              component('Stderr'),
              component('Memory')*/
            ]}
          ]}, {
            type: 'stack',
            content: [
              /*
              component('Cabs'),
              component('Ail_AST'),
              component('Core')
              */
             // HACK used to initialised a different componenet for BMC
             // @ts-ignore
             window.isBMC ? component('BMC') : component('Memory')
            ]
          }
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
      const tab = Tabs.create(state.tab, self.ee, state.args)
      self.tabs.push(tab);
      (container.parent as ContentItem).content = tab
      container.getElement().append(tab.dom)
      container.setState(state)
      tab.initial(self.state)
      tab.refresh()
      const unsafeTab: any = tab
      if (unsafeTab.highlight && self.state.options.colour_all)
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
        tab.setActive = () => triggerClick(header.element[0])
        tab.close = () => header.contentItem.remove()
      }
    })
    this.layout.on('stateChanged', () => this.emit('layoutChanged'))
    this.layout.init()
  }

  private setStateEmpty() {
    this.state = {
      title: () => this.title,
      source: () => this.source.getValue(),
      dirty: true,
      pp: { cabs: '', ail:  '', core: '' },
      ast: { cabs: '', ail:  '', core: '' },
      locs: [],
      console: '',
      model: {
        alloc_model: 'concrete',
        core_options: {
          rewrite: false,
          sequentialise: false
        },
        exec_options: {
          libc: false
        },
        switches: ['PNVI_ae_udi', 'strict_pointer_relationals', 'zap_dead_pointers']
      },
      interactiveMode: InteractiveMode.Memory,
      interactive: undefined,
      options: {
        show_integer_provenances: true,
        show_string_literals: false,
        show_pointer_bytes: false,
        hide_tau: true,
        colour_all: false,
        colour_cursor: true,
        show_mem_order: false,
        align_allocs: false,
      },
      bmc_model: 'bmc_c11',
      bmc_executions: []
    }
  }

  private clearState() {
    this.state = {
      title: () => this.title,
      source: () => this.source.getValue(),
      dirty: true,
      pp: { cabs: '', ail:  '', core: '' },
      ast: { cabs: '', ail:  '', core: '' },
      locs: [],
      console: '',
      model: this.state.model,
      interactiveMode: InteractiveMode.Memory,
      interactive: undefined,
      options: this.state.options,
      bmc_model: this.state.bmc_model,
      bmc_executions: []
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

  newTab(tab: string, title?: string, notClosable?: boolean, ...args: any []) {
    if (title === undefined) title = tab;
    this.layout.root.contentItems[0].addChild({
      type: 'component',
      componentName: 'tab',
      isClosable: !notClosable,
      title: title,
      componentState: { tab: tab, args: args }
    })
    this.refresh()
  }

  /** Start interactive tabs (with the first state Init) */
  startInteractive(ranges: Range[], tag_defs: string, steps: GraphFragment) {
    if (steps.nodes.length != 1)
      throw new Error('impossible initialise interactive mode')
    let init = steps.nodes[0]
    init = { ...init,
      isVisible: true,
      isTau: false,
      selected: true,
      can_step: true
    }
    this.state.interactive = {
      current: init,
      next_options: [init.id],
      tag_defs: tag_defs,
      ranges: ranges,
      last_node_id: init.id,
      counter: 0,
      steps: new Graph({nodes: [init], edges: []}),
      history: [],
      arena: '',
      mem: undefined,
      exec: undefined,
    }
    this.execGraphNodeClick(0)
  }

  /** Restart interactive mode in all the tabs */
  resetInteractive() {
    delete this.state.interactive
    this.state.console = ''
  }

  /** Restart interactive execution */
  restartInteractive() {
    this.resetInteractive()
    this.emit('clear')
    this.emit('updateExecution')
    this.emit('updateExecutionGraph')
    this.emit('updateMemory')
    this.emit('updateUI')
  }

  /** Update execution graph DOT */
  updateExecutionGraph() {
    if (!this.state.interactive) return
    const graph = this.state.interactive.steps
    const dotHead = 'digraph G { node [shape=box, fontsize=12]; edge [fontsize=10];'
    const nodes = this.state.options.hide_tau
                ? _.filter(graph.nodes, n => !n.isTau && n.isVisible)
                : _.filter(graph.nodes, n => n.isVisible)
    const edges = _.filter(graph.edges, e => this.state.options.hide_tau ? !e.isTau : e.isTau)
    const label = (n : Node) => {
      if (n.arena) {
        if (n.arena.length > 30)
          return n.arena.substring(0,30) + '...'
        return n.arena
      }
      return n.info.kind
    }
    const dotNodes = _.reduce(nodes, (acc, n) => 
      acc + `n${n.id}[href="javascript:UI.execGraphNodeClick(${n.id})",`
      + (n.selected ? 'color="blue", ' : '')
      + (n.can_step ? 'fontcolor="blue", ' : '')
      + (n.id == 0 ? 'style=invis, height=0, width=0, ' : '')
      + `label="${label(n)}"];`, '')
    const dotEdges = _.reduce(edges, (acc, e) => {
      if (graph.nodes[e.from].isVisible && graph.nodes[e.to].isVisible) {
        const label = graph.nodes[e.from].info.kind
        return acc + `n${e.from}->n${e.to}[label="${label}"];`
      }
      else return acc
    }, '')
    if (this.state.interactive === undefined)
      throw new Error ('not in interactive mode')
    this.state.interactive.exec = dotHead + dotNodes + dotEdges + '}'
    this.emit('updateExecutionGraph')
  }

  public updateMemory() {
    if (!this.state.interactive) return
    const mem = this.state.interactive.current.mem
    if (!mem) return
    const pvi = _.includes(this.state.model.switches, 'PVI')
    const createNode = (alloc: Memory.Allocation): string => {
      if (alloc.prefix.kind === 'string literal' && !this.state.options.show_string_literals)
        return ''
      const box = (n:number, charsize=false) =>
        `<td width="7" height="${charsize?'20':'7'}" fixedsize="true" port="${String(n)}">
          <font point-size="1">&nbsp;</font>
         </td>`
      const maxcols = alloc.values.reduce((acc, row) => Math.max(acc, row.path.length), 0)+1
      const tooltip = "allocation: " + String(alloc.id)
      const name = () => {
        const p = alloc.prefix
        if (alloc.dyn)
          return `malloc'd`
        if (p.kind == 'arg' || p.kind == 'malloc')
          return p.name
        switch (Memory.unique(p, mem.map)) {
          case 'unique':
            return p.name
          case 'unique-in-scope':
            const uniq_scope = p.scope != null ? p.scope : 'global'
            return `${p.name}(${uniq_scope})`
          case 'non-unique':
            const line = p.loc && p.loc.begin ? `:${p.loc.begin.line+1}` : ''
            const scope = p.scope != null ? p.scope + line : 'global'
            return `${alloc.prefix.name}(${scope})`
        }
      }
      const title =
        `<tr>
          <td height="7" width="7" fixedsize="true" border="0">&nbsp;</td>
          <td ${alloc.exposed ? 'bgcolor="burlywood1"': ''} border="0" colspan="${maxcols}">
              <b>${name()}</b>: ${alloc.type}&nbsp;[@${alloc.id}${alloc.exposed ? ' exp' : ''}, 0x${bigInt(alloc.base).toString(16)}]
          </td>
         </tr>`
      let index = 0
      const body = alloc.values.reduce((acc, row) => {
        const head    = row.path.reduce((acc, tag) => `${acc}<td rowspan="${row.size}">${tag}</td>`, '')
        const spath   = row.path.reduce((acc, tag) => acc + '_' + tag, '')
        const colspan = String(maxcols-row.path.length)
        const bgcolor = Memory.ispadding(row) ? ' bgcolor="grey"' : (mem.last_used != null && mem.last_used === alloc.id ? 'bgcolor="lightcyan"' : '')
        const [value, multirow] = Memory.string_of_value(row, pvi && this.state.options.show_integer_provenances, this.state.options.show_pointer_bytes)
        const body    = `<td port="${spath}v" rowspan="${row.size}" colspan="${colspan}" ${bgcolor}>${value}</td>`
        acc += `<tr>${box(index, row.size == 1 || multirow)}${head}${body}</tr>`
        index++
        for (let j = 1; j < row.size; j++, index++)
          acc += `<tr>${box(index, multirow)}</tr>`
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
    type Pointer = {
      from: string /*id path*/,
      to: number[] /*prov*/,
      addr: bigInt.BigInteger /*pointer*/,
      intptr: boolean,
      invalid: boolean
    }
    const getPointersInAlloc = (alloc: Memory.Allocation) => {
      return alloc.values.reduce((acc: Pointer[], row) => {
        const provs = (p: Memory.Provenance) => {
          switch (p.kind) {
            case 'prov':
              return [p.value]
            case 'iota':
              return p.iota
            case 'empty':
              return []
          }
        }
        if (Memory.pointsto(row) && row.value != 'unspecified') {
          const from = row.path.reduce((acc, tag) => acc + '_' + tag, `n${alloc.id}:`)
          const p: Pointer = {
            from: from,
            to: provs (row.prov),
            addr: bigInt(row.value),//parseInt(row.value),
            intptr: row.kind == 'intptr',
            invalid: Memory.isInvalidPointer(pvi, row)
          }
          return _.concat(acc, [p])
        } else {
          return acc
        }
      }, [])
    }
    const createEdges = (ps: Pointer[], mem: Memory.State) => {
      const color = (p: Pointer, target: Memory.Allocation) => {
        // correct provenance
        if (_.includes(p.to, target.id))
          return 'black'
        // intptr in PNVI
        if (!pvi && p.intptr) 
          return 'black'
        // incorrect pointer
        return 'red'
      }
      const style = (p: Pointer) => {
        if (p.intptr)
          return 'dashed'
        if (!pvi && p.invalid)
          return 'dotted'
        return 'solid'
      }
      const invisible = (target: Memory.Allocation) => {
        return target.prefix.kind === 'string literal' && !this.state.options.show_string_literals
      }
      return _.reduce(ps, (acc, p) => {
        // points in bounds to an allocation
        const target = _.find(mem.map, alloc => {
          const base = bigInt(alloc.base)
          const size = bigInt(alloc.size)
          return base <= p.addr && p.addr < base.plus(size)
        })
        const single_column = this.state.options.align_allocs ? ',constraint=false' : ''
        if (target) {
          if (invisible(target)) return acc
          const base = bigInt(target.base)
          const offset = p.addr.minus(base)
          acc += `${p.from}v->n${target.id}:${offset}[style="${style(p)}",color="${color(p, target)}"${single_column}];`
          return acc
        } 
        // points to a past one of an allocation
        const pastone = _.find(mem.map, alloc => p.addr.equals(bigInt(alloc.base).plus(alloc.size)))
        if (pastone) {
          if (invisible(pastone)) return acc
          acc += `${p.from}v->n${pastone.id}:${pastone.size}[style="${style(p)}",color="red"${single_column}];`
          return acc
        }
        // dangling pointer
        acc += `dang${p.addr.toString()}[label="0x${p.addr.toString(16)}",color="red"];${p.from}v->dang${p.addr.toString()}[style="${style(p)}",color="red"${single_column}];`
        return acc;
      }, '')
    }
    const forceOrder = () => {
      let init = true
      const order = _.reduce(mem.map, (ns, alloc) => {
        if (!(this.state.options.show_string_literals && alloc.prefix.kind === 'string literal'))
          return ns
        if (init) {
          init = false
          return `n${alloc.id}`
        }
        return `${ns} -> n${alloc.id}`
      }, '')
      if (_.includes(order, '->'))
        return order + '[style=invis,constraint=false];'
      return ''
    }
    const g = 'digraph Memory { node [shape=none, fontsize=12]; rankdir=LR;'
    const ns =  _.reduce(mem.map, (ns, alloc) => ns + createNode(alloc), '')
    const order = this.state.options.show_mem_order ? forceOrder() : ''
    const ps = _.reduce(mem.map, (acc: Pointer[], alloc) => _.concat(acc, getPointersInAlloc(alloc)), [])
    const es = createEdges(ps, mem)
    this.state.interactive.mem = g + ns + order + es + '}' // Save in case another memory tab is open 
    this.getTab('Memory').setActive()
    this.emit('updateMemory')
  }

  private executeInteractiveMode(nID: number, lastCline?: number): Node[] {
    if (this.state.interactive === undefined)
      throw new Error('not in interactive mode')
    const graph = this.state.interactive.steps
    let children = graph.setChildrenVisible(nID, this.state.interactiveMode != InteractiveMode.Tau)
    if (children.length == 1) {
      const active = children[0]
      switch (this.state.interactiveMode) {
        case InteractiveMode.Tau:
          break
        case InteractiveMode.Memory:
          switch (active.info.kind) {
            case 'error':
            case 'done':
              return children
            case 'step':
              switch (active.info.step_kind.kind) {
                case 'action request':
                case 'done':
                  children = graph.setChildrenVisible(active.id, true)
                  break
                default:
                  children = this.executeInteractiveMode(active.id, lastCline)
                  break
              }
              break
            case "init":
              throw new Error ("fatal error: init step")
            case "branch":
              throw new Error ("fatal error: branch step")
            case "unsat":
              throw new Error ("fatal error: unsat step")
          }
          break
        case InteractiveMode.Core:
          // Nothing to do
          break
        case InteractiveMode.CLine:
          switch (active.info.kind) {
            case 'error':
            case 'done':
              return children
            case 'step':
              switch (active.info.step_kind.kind) {
                case 'done':
                  children = graph.setChildrenVisible(active.id, true)
                  break
                default:
                  break
              }
              break
            case "init":
              throw new Error ("fatal error: init step")
            case "branch":
              throw new Error ("fatal error: branch step")
            case "unsat":
              throw new Error ("fatal error: unsat step")
          }
          if (lastCline != undefined && active.loc != undefined && active.loc.c != undefined && lastCline == active.loc.c.begin.line)
            children = this.executeInteractiveMode(active.id, lastCline)
          break
      }
    } 
    return children
  }

  private setActiveInteractiveNode(active: Node) {
    if (this.state.interactive === undefined)
      throw new Error('not in interactive mode')
    this.state.interactive.current = active
    // Arena
    this.state.interactive.arena = `-- Environment:\n${active.env}-- Arena:\n${active.arena}`
    this.emit('updateArena')
    // Memory graph
    this.updateMemory()
    // Locations
    if (active.loc) {
      this.emit('clear')
      this.emit('markInteractive', active.loc)
    }
  }

  /** Update interactive display state and raise event to update DOT */
  private executeInteractiveStep(activeId: number) {
    if (this.state.interactive === undefined)
      throw new Error('not in interactive mode')
    const graph = this.state.interactive.steps
    const active = graph.nodes[activeId]
    const lastCline = (active.loc && active.loc.c ? active.loc.c.begin.line : undefined)
    let children = this.executeInteractiveMode(activeId, lastCline)

    if (children.length == 0) {
      alert ('Internal error: active node has no children')
      throw new Error('active node has no children')
    }

    const firstChoice = children[0]
    const lastNode =
      children.length == 1 && graph.children(firstChoice.id).length == 0

    graph.nodes.map(n => n.selected = false)
    this.state.interactive.history.push(activeId)

    this.state.interactive.counter += 1
    this.state.interactive.next_options = children.map(n => n.id)

    children.map(child => child.can_step = !lastNode)
    firstChoice.selected = !lastNode

    this.setActiveInteractiveNode(firstChoice)
    this.updateExecutionGraph();

    this.state.console = firstChoice.stdout
    if (lastNode) {
      this.state.interactive.next_options = []
      this.getConsole().setActive()
      switch (firstChoice.info.kind) {
        case 'error':
          const loc = firstChoice.info.loc && firstChoice.info.loc.begin ? ` at line ${firstChoice.info.loc.begin.line+1}` : ''
          this.state.console = `Unsuccessful termination of this execution:\n\t${firstChoice.info.reason}${loc}`
          break
        case 'done':
          this.state.console = `Successful termination of this execution:\n\t${firstChoice.info.result}`
          break
        default:
          throw new Error("fatal lastNode")
      }
      this.emit('updateExecution')
    }

    if (children.length > 3) {
      this.getTab('Interactive').setActive()
    }
    this.emit('updateExecution')
    this.emit('updateUI')
  }

  /** Update interactive state mode and update DOT */
  private updateInteractive(activeId: number, tree: GraphFragment) {
    if (this.state.interactive === undefined)
      throw new Error('not in interactive mode')
    // This is a seed to the server
    this.state.interactive.last_node_id = tree.nodes[0].id
    tree.nodes.reverse()
    const graph = this.state.interactive.steps
    // Update current point to become branch
    const active = graph.nodes[activeId]
    if (!active)
      throw new Error('Active point in update Interactive is undefined!')
    active.can_step = false
    delete active.state
    // Add nodes
    tree.nodes.map((n) => {
      n.isTau = n && n.info.kind == 'step' && n.info.step_kind.kind == 'tau' && tree.siblings(n.id).length == 1
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
        const from = graph.getNoTauParent(e.to)
        if (from != undefined)
          graph.edges.push({from: from, to: e.to, isTau: false})
      }
    })
    // Set visible nodes descendent from active
    this.executeInteractiveStep(activeId)
  }

  /** Execute a step (it might call the server to update interactive state) */
  execGraphNodeClick(activeId: number) {
    if (this.state.interactive === undefined)
      throw new Error('not in interactive mode')
    const graph = this.state.interactive.steps
    if (graph.children(activeId).length == 0) {
      // Node has no children, just ask more to the server
      // TODO: should check if it is the end or if there a state to ask
      const node = graph.nodes[activeId]
      if (node.state != null)
        UI.step({id: node.id, state: node.state})
    } else {
      const active = graph.nodes[activeId]
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
    if (this.state.interactive === undefined)
      throw new Error ('not in interactive mode')
    const graph = this.state.interactive.steps
    const activeId = this.state.interactive.history.pop()
    if (activeId == undefined)
      throw new Error('Already in the beginning!')
    this.state.interactive.counter -= 1
    const setChildrenInvisible = (nID: number) => {
      graph.children(nID).map(nID => {
        const n = graph.nodes[nID]
        if (n.isVisible) {
          n.isVisible = false
          setChildrenInvisible(nID)
        }
      })
    }
    setChildrenInvisible(activeId)
    const active = graph.nodes[activeId]
    active.can_step = true
    graph.nodes.map(n => n.selected = false)
    active.selected = true
    this.state.interactive.next_options = graph.siblings(active.id)
    this.setActiveInteractiveNode(active)
    this.updateExecutionGraph();
    this.emit('updateUI')
  }

  stepForward() {
    if (!this.state.interactive)
      UI.step(null)
    else
      this.execGraphNodeClick(this.state.interactive.current.id)
  }

  stepForwardLeft() {
    if (this.state.interactive === undefined)
      throw new Error ('not in interactive mode')
    this.execGraphNodeClick(this.state.interactive.next_options[0])
  }

  stepForwardMiddle() {
    if (this.state.interactive === undefined)
      throw new Error ('not in interactive mode')
    this.execGraphNodeClick(this.state.interactive.next_options[1])
  }

  stepForwardRight() {
    if (this.state.interactive === undefined)
      throw new Error ('not in interactive mode')
    this.execGraphNodeClick(this.state.interactive.next_options[this.state.interactive.next_options.length == 2 ? 1 : 2])
  }

  setInteractiveMode(mode: InteractiveMode) {
    this.state.interactiveMode = mode
  }

  getEncodedState() {
    let miniConfig = GoldenLayout.minifyConfig(this.layout.toConfig())
    miniConfig.title = this.source.title
    miniConfig.source = this.source.getValue()
    return encodeURIComponent(JSON.stringify(miniConfig))
  }

  // Return this first instance (or create a new one)
  getTab(tab_name: string, title?: string, notClosable?: boolean) {
    let tab = this.findTab(tab_name)
    if (tab == null) {
      this.newTab(tab_name, title, notClosable)
      tab = <Tabs.Tab>this.findTab(tab_name)
    }
    return tab
  }

  getSource(): Readonly<Tabs.Source> {
    return this.source
  }

  getConsole() {
    return this.getTab('Console')
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

  updateState(res: ResultRequest) {
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
        this.state.console = ''
        this.startInteractive(res.ranges, res.tagDefs, new GraphFragment(res.steps))
        break;
      case 'stepping':
        this.state.console = ''
        this.updateInteractive(res.activeId, new GraphFragment(res.steps))
        break
      case 'bmc':
        this.state.console = res.result
        this.state.bmc_executions = res.executions
        if (res.executions && res.executions.length > 0) {
          let bmc = this.getTab('BMC')
          if (bmc) bmc.setActive()
        }
        this.emit('updateBMC')
        break;
      case 'failure':
        this.clearState()
        this.state.console = res.console
        this.state.bmc_executions = []
        this.getConsole().setActive()
        break
    }
    this.isHighlighted = false
    this.dirty = false
  }

  on(e: Event, l: any, f: Function) {
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
    switch (e) {
      case 'highlight':
        if (this.isHighlighted || !this.state.options.colour_all || this.dirty) return
        this.isHighlighted = true
        break;
      case 'clear':
        this.isHighlighted = false
        break;
      case 'mark':
        if (!this.state.options.colour_cursor || this.dirty) return
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
