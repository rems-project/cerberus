import { Graph } from './graph'

namespace Common {
  export type bytes = string | undefined

  export type ID = string | number

  export enum ExecutionMode {
    Random,
    Exhaustive
  }

  export type Action =
    { kind: 'elaborate' } |
    { kind: 'execute', mode: ExecutionMode } |
    { kind: 'step' }

  export function string_of_action(a: Action) {
    switch (a.kind) {
      case 'elaborate':
        return "Elaborate"
      case 'execute':
        switch (a.mode) {
          case ExecutionMode.Random:
            return 'Random'
          case ExecutionMode.Exhaustive:
            return 'Exhaustive'
        }
      case 'step':
        return 'Step'
    }
  }

  export function Elaborate() : Action { return { kind: 'elaborate' } }
  export function Execute(m: ExecutionMode) : Action { return { kind: 'execute', mode: m} }
  export function Step() : Action { return { kind: 'step' } }

  export enum Model {
    Concrete,
    Symbolic
  }

  export function string_of_model(m: Model) {
    switch (m) {
      case Model.Concrete:
        return "Concrete"
      case Model.Symbolic:
        return "Symbolic"
    }
  }

  export interface InteractiveRequest {
    lastId: number,
    state: bytes,
    active: ID,
    tagDefs: bytes
  }

  export interface IR {
    cabs: string
    ail: string
    core: string
  }

  export interface Point {
    line: number
    ch: number
  }

  export interface Range {
    begin: Point
    end: Point
  }

  export interface Locations {
    c: Range
    core: Range
    color: number
  }

  export interface State {
    title: () => Readonly<string>
    source: () => Readonly<string>
    status: string
    pp: IR
    ast: IR
    locs: Locations[]
    graph: Graph
    mem: Graph
    result: string
    console: string
    lastNodeId: number
    tagDefs?: bytes
    dirty: boolean
  }

  export interface EventEmitter {
    on: (e: string, l: any, f: Function) => void
    off: (l: any) => void 
    once: (f: ((s: Readonly<Common.State>) => any)) => any
    emit: (e:string, ...args: any[]) => void
  }

  export interface Compiler {
    id: string
    name: string
  }

}

export default Common