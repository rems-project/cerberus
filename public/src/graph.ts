import { find, flatten, union, uniq } from 'lodash'
import { Locations, Range } from './location'
import * as Memory from './memory'

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
  id: number
  state: string | undefined
  isVisible: boolean
  isTau: boolean
  loc: Locations | undefined
  mem: Memory.State | undefined
  info: NodeInfo
  env: string
  arena: string
  selected: boolean
  can_step: boolean
  stdout: string
  stderr: string
}

export interface Edge {
  from: number
  to: number
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

  parent(nnumber: number): number | undefined {
    const e = find(this.edges, e => e.to == nnumber)
    if (e) return e.from
    return undefined
  }

  children(nnumber: number): number [] {
    return uniq(this.edges.filter(e => e.from == nnumber).map(e => e.to))
  }

  // including nnumber
  siblings(nnumber: number): number[] {
    const p = this.parent(nnumber)
    if (p) return this.children(p)
    return [nnumber]
  } 

  clear() {
    this.nodes = []
    this.edges = []
  }
}

export class Graph extends GraphFragment {
  isTau(nnumber: number): boolean {
    return this.nodes[nnumber].isTau
  }

  nonTauChildren(nnumber: number): number [] {
    return this.edges.filter(e => e.from == nnumber && !e.isTau).map(e => e.to)
  }

  tauChildren(nnumber: number): number [] {
    return this.edges.filter(e => e.from == nnumber && this.isTau(e.to)).map(e => e.to)
  }

  tauChildrenTransClosure(nnumber: number): number [] {
    const immediateTauChildren = this.tauChildren(nnumber)
    const transitiveTauChildren =
      flatten(immediateTauChildren.map(nnumber => this.tauChildrenTransClosure(nnumber)))
    return union(immediateTauChildren, transitiveTauChildren)
  }

  setChildrenVisible(nnumber: number, skip_tau: boolean): Node[] {
    let children
    if (skip_tau) {
      this.tauChildrenTransClosure(nnumber).map(nnumber => this.nodes[nnumber]).map(child => child.isVisible = true)
      children = this.nonTauChildren(nnumber).map(nnumber => this.nodes[nnumber])
      children.map(child => child.isVisible = true)
    } else {
      children = this.tauChildren(nnumber).map(nnumber => this.nodes[nnumber])
      if (children.length > 0) {
        children.map(child => child.isVisible = true)  
      } else {
        children = this.children(nnumber).map (nnumber => this.nodes[nnumber])
        children.map(child => child.isVisible = true)  
      }
    }
    return children
  }
  
  /** Search for a no tau parent */
  getNoTauParent (nId: number):  number | undefined {
    const e = find(this.edges, n => n.to == nId)
    if (e == undefined || e.from == undefined)
      throw new Error('Could not find incomming edge!')
    if (this.nodes[e.from].isTau)
      return this.getNoTauParent(e.from)
    return e.from
  }
}