import _ from 'lodash'
import vis from 'vis'

export type ID = string | number

export interface Node extends vis.Node {
  id: ID
  state: string | undefined
  isVisible: boolean
  isTau: boolean
  loc: any
  mem: any
  label: string
}

export interface Edge extends vis.Edge {
  isTau: boolean
  to: ID
}

export class Graph {
  nodes: vis.DataSet<Node>
  edges: vis.DataSet<Edge>
  constructor (nodes?: Node [], edges?: Edge []) {
    this.nodes = new vis.DataSet(nodes)
    this.edges = new vis.DataSet(edges)
  }

  getParentByID(nID: ID): Node | undefined {
    const edgeToParent = _.find(this.edges.get(), e => e.to == nID)
    if (edgeToParent && edgeToParent.from) 
      return this.nodes.get(edgeToParent.from)
    return undefined
  }

  children(nID: ID): ID [] {
    return this.edges.get().filter(n => n.from == nID && !n.isTau).map(n => n.to)
  }

  tauChildren(nID: ID): ID [] {
    return this.edges.get().filter(n => n.from == nID && n.isTau).map(n => n.to)
  }

  getChildByID(nID: ID): Node | undefined {
    const edgeToChild = _.find(this.edges.get(), e => e.from == nID)
    if (edgeToChild && edgeToChild.to)
      return this.nodes.get(edgeToChild.to)
    return undefined
  }

  clear() {
    this.nodes.clear()
    this.edges.clear()
  }

  // Set visible all tau nodes descendent from active until first non-tau
  setChildrenVisible (nID: ID) {
    const setTauChildrenVisible = (nID: ID) => {
      const tauChildren = this.tauChildren(nID).map((nID: ID) => this.nodes.get(nID)).map(child => {
        child.isVisible = true
        setTauChildrenVisible(child.id)
        return child
      })
      return tauChildren
    }
    const tauChildren = _.flatten(setTauChildrenVisible(nID))
    const children = this.children(nID).map(nID => this.nodes.get(nID)).map(child => {
      child.isVisible = true
      if (this.children(child.id).length > 0)
        child.group = 'leaf'
      return child
    })
    this.nodes.update(_.sortedUniqBy(children.concat(tauChildren), (e) => e.id))
  }

  update(newNodes: Node[], newEdges: Edge[]) {
    this.nodes.update(newNodes)
    this.edges.update(newEdges)
  }
}