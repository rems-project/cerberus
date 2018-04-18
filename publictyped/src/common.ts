namespace Common {
  export type bytes = string

  export type ID = string | number

  export enum Model {
    Concrete,
    Symbolic
  }

  export interface InteractiveRequest {
    lastId: number,
    state: bytes,
    active: ID,
    tagDegs: bytes
  }

  export interface IR {
    cabs: string
    ail: string
    core: string
  }

  // TODO: Use ADTs here!!!
  export interface State {
    title: string
    status: string
    pp: IR
    ast: IR
    locs: any[]
    graph: any
    mem: any
    result: string
    console: string
    lastNodeId: number
    tagDefs?: bytes
    isHighlighted: boolean
    dirty: boolean
  }
}

export default Common