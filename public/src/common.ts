import { Node, Edge, Graph } from './graph'

namespace Common {
  export type Bytes = string | undefined

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
        // TODO: how do I tell the type checker that this is unreachable?
        return 'Random'
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
        return 'Concrete'
      case Model.Symbolic:
        return 'Symbolic'
    }
  }

  export function model_of_string(m:string) {
    switch(m) {
      case 'Concrete':
        return Model.Concrete
      case 'Symbolic':
        return Model.Symbolic
    }
    throw `Model ${m} does not exist.`
  }

  export interface InteractiveRequest {
    lastId: ID,
    state: Bytes,
    active: ID,
    tagDefs: Bytes
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
    pp: IR
    ast: IR
    locs: Locations[]
    graph: Graph
    mem: Graph
    result: string
    console: string
    lastNodeId: ID 
    tagDefs?: Bytes
    dirty: boolean
  }

  export interface ResultTree {
    nodes: Node []
    edges: Edge []
  }

  export type ResultRequest =
    { status: 'elaboration', pp: IR, ast: IR, locs: Locations[], console: string } |
    { status: 'execution', console: string, result: string} |
    { status: 'stepping', result: string, tagDefs?: Bytes} |
    { status: 'failure', console: string, result: string }

  export type ResultStep = { state: ResultRequest, steps: ResultTree }

  export type Event =
    'update' |            // Update tab values
    'updateExecution' |   // Update execution result
    'clearGraph'  |       // Clear step graph
    'updateGraph' |       // Update step graph
    'setMemory' |         // Set memory state
    'updateMemory' |      // Update memory graph
    'resetInteractive' |  // Reset interactive mode
    'step' |              // Step interactive mode
    'mark' |              // Mark location
    'markError' |         // Mark error location
    'clear' |             // Clear all markings
    'highlight' |         // Highlight the entire file
    'dirty'               // Fired when file has changed

  export interface EventEmitter {
    on (eventName: 'clear', self: any, f: (locs: Locations) => void): void
    on (eventName: 'mark', self: any, f: (locs: Locations) => void): void
    on (eventName: 'markError', self: any, f: (line: number) => void): void
    on (eventName: 'dirty', self: any, f: () => void): void
    on (eventName: 'step', self: any, f: (active: Node) => void): void
    on (eventName: 'setMemory', self: any, f: (mem: any) => void): void
    on (eventName: Event, self: any, f: ((s: Readonly<State>) => void)): void
    off (self: any): void 
    once (f: ((s: Readonly<State>) => any)): any
    emit (eventName: 'clear'): void
    emit (eventName: 'mark'): void
    emit (eventName: Event, ...args: any[]): void // TODO: take any any out!!
  }

  export interface Compiler {
    id: string
    name: string
  }

}

export default Common