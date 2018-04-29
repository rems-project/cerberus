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

  export type ResultRequest =
    { status: 'elaboration', pp: IR, ast: IR, locs: Locations[], console: string } |
    { status: 'execution', console: string, result: string} |
    { status: 'stepping', result: string, tagDefs?: bytes} |
    { status: 'failure', console: string, result: string }

  export type Event =
    'update' |            // Update tab values
    'updateExecution' |   // Update execution result
    'mark' |              // Mark location
    'clear' |             // Clear all markings
    'highlight' |         // Highlight the entire file
    'dirty'               // Fired when file has changed

  export interface EventEmitter {
    on (eventName: 'clear', self: any, f: (locs: Locations) => void): void
    on (eventName: 'mark', self: any, f: (locs: Locations) => void): void
    on (eventName: 'dirty', self:any, f: () => void): void
    on (eventName: Event, self: any, f: ((s:Readonly<State>) => void)): void
    off (self: any): void 
    once (f: ((s: Readonly<State>) => any)): any
    emit (eventName: Event, ...args: any[]): void
  }

  export interface Compiler {
    id: string
    name: string
  }

}

export default Common