import { find, flatten, union } from 'lodash'

export type ID = string | number

export interface Locations {
  c: Range
  core: Range
  color: number
  arena: string // TODO: this shouldn't be here
}

export interface Node {
  id: ID
  state: string | undefined
  isVisible: boolean
  isTau: boolean
  loc: Locations | undefined
  mem: any
  label: string
  selected: boolean
  can_step: boolean
}

export interface Edge {
  from: ID
  to: ID
  isTau: boolean
}

export class Graph {
  nodes: Node[]
  edges: Edge[]

  constructor (nodes?: Node [], edges?: Edge []) {
    this.nodes = nodes ? nodes : [];
    this.edges = edges ? edges : [];
  }

  isEmpty() {
    return this.nodes.length === 0
  }

  getParentByID(nID: ID): Node | undefined {
    const edgeToParent = find(this.edges, e => e.to == nID)
    if (edgeToParent && edgeToParent.from) 
      return this.nodes[edgeToParent.from]
    return undefined
  }

  isTau(nID: ID): boolean {
    return this.nodes[nID].isTau
  }

  children(nID: ID): ID [] {
    return this.edges.filter(e => e.from == nID).map(e => e.to)
  }

  nonTauChildren(nID: ID): ID [] {
    return this.edges.filter(e => e.from == nID && !e.isTau).map(e => e.to)
  }

  tauChildren(nID: ID): ID [] {
    return this.edges.filter(e => e.from == nID && this.isTau(e.to)).map(e => e.to)
  }

  tauChildrenTransClosure(nID: ID): ID [] {
    const immediateTauChildren = this.tauChildren(nID)
    const transitiveTauChildren =
      flatten(immediateTauChildren.map(nID => this.tauChildrenTransClosure(nID)))
    return union(immediateTauChildren, transitiveTauChildren)
  }

  getChildByID(nID: ID): Node | undefined {
    const edgeToChild = find(this.edges, e => e.from == nID)
    if (edgeToChild && edgeToChild.to)
      return this.nodes[edgeToChild.to]
    return undefined
  }

  clear() {
    this.nodes = []
    this.edges = []
  }
}