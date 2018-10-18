import { find, flatten, union, uniq } from 'lodash'
import { Locations, Range } from './location'
import * as Memory from './memory'

export type Bytes = string | undefined
export type ID = number

export type NodeKind =
    'tau'
  | 'action request'
  | 'done'

export interface NodeInfo {
  kind: NodeKind // Next step kind
  debug: string
  file?: string
  error_loc?: Range
}

export interface Node {
  id: ID
  state: Bytes
  isVisible: boolean
  isTau: boolean
  loc: Locations | undefined
  mem: Memory.Map | undefined
  info: NodeInfo
  env: string
  arena: string
  selected: boolean
  can_step: boolean
  outp: string
}

export interface Edge {
  from: ID
  to: ID
  isTau: boolean
}

export class GraphFragment {
  nodes: Node[]
  edges: Edge[]

  constructor (g ?: { nodes: Node [], edges: Edge []} ) {
    this.nodes = g ? g.nodes : [];
    this.edges = g ? g.edges : [];
  }

  isEmpty() {
    return this.nodes.length === 0
  }

  getSelected() {
    return find(this.nodes, n => n.selected)
  }

  parent(nID: ID): ID | undefined {
    const e = find(this.edges, e => e.to == nID)
    if (e) return e.from
    return undefined
  }

  children(nID: ID): ID [] {
    return uniq(this.edges.filter(e => e.from == nID).map(e => e.to))
  }

  // including nID
  siblings(nID: ID): ID[] {
    const p = this.parent(nID)
    if (p) return this.children(p)
    return [nID]
  } 

  clear() {
    this.nodes = []
    this.edges = []
  }
}

export class Graph extends GraphFragment {
  isTau(nID: ID): boolean {
    return this.nodes[nID].isTau
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

  setChildrenVisible(nID: ID, skip_tau: boolean): Node[] {
    let children
    if (skip_tau) {
      this.tauChildrenTransClosure(nID).map(nID => this.nodes[nID]).map(child => child.isVisible = true)
      children = this.nonTauChildren(nID).map(nID => this.nodes[nID])
      children.map(child => child.isVisible = true)
    } else {
      children = this.tauChildren(nID).map(nID => this.nodes[nID])
      if (children.length > 0) {
        children.map(child => child.isVisible = true)  
      } else {
        children = this.children(nID).map (nID => this.nodes[nID])
        children.map(child => child.isVisible = true)  
      }
    }
    return children
  }
  
  /** Search for a no tau parent */
  getNoTauParent (nId: ID):  ID | undefined {
    const e = find(this.edges, n => n.to == nId)
    if (e == undefined || e.from == undefined)
      throw new Error('Could not find incomming edge!')
    if (this.nodes[e.from].isTau)
      return this.getNoTauParent(e.from)
    return e.from
  }
}