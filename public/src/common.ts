import { Node, Edge, Graph } from './graph'
import { Range, Locations } from './location'

namespace Common {
  export type Bytes = string | undefined
  export type ID = number

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
    Symbolic,
    Twin
  }

  export function string_of_model(m: Model) {
    switch (m) {
      case Model.Concrete:
        return 'Concrete'
      case Model.Symbolic:
        return 'Symbolic'
      case Model.Twin:
        return 'Twin'
    }
  }

  export function model_of_string(m:string) {
    switch(m) {
      case 'Concrete':
        return Model.Concrete
      case 'Symbolic':
        return Model.Symbolic
      case 'Twin':
        return Model.Twin
    }
    throw `Model ${m} does not exist.`
  }

  export type MemoryValueRow = {
    size: number,
    ispadding: boolean,
    path: string[],
    value: string,
    pointsto: number | null
  }

  export type MemoryAllocation = {
    id: number,
    base: number,
    type: string,
    prefix: string | null,
    size: number,
    rows: MemoryValueRow[]
  }

  export type Memory = {[key:string]: MemoryAllocation}

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

  export enum InteractiveMode {
    CLine,  // Step to the next C line
    Memory, // Step to the next memory transition
    Core    // Step each Core transition
  }

  export interface State {
    title: () => Readonly<string>
    source: () => Readonly<string>
    pp: IR
    ast: IR
    locs: Locations[]
    //result: string
    console: string
    lastNodeId: ID 
    tagDefs?: Bytes
    ranges?: Range[]
    dirty: boolean
    switches: string [],
    arena: string
    // Interactive mode
    hide_tau: boolean // Hide tau transition option
    skip_tau: boolean // Skip tau transition
    mode: InteractiveMode
    //lastCline: number | undefined
    history: ID [] // History of execution (allows to go back)
    graph: Graph // Current execution graph
    dotMem: string // DOT representation
    dotExecGraph: string // DOT representation
  }

  export type ResultRequest =
    { status: 'elaboration', pp: IR, ast: IR, locs: Locations[], console: string } |
    { status: 'execution', console: string, result: string} |
    { status: 'interactive', tagDefs: Bytes, ranges: any, steps: {nodes: Node [], edges: Edge[]}} |
    { status: 'stepping', result: string, activeId: number, steps: {nodes: Node [], edges: Edge[]}} |
    { status: 'failure', console: string, result: string }

  export type Event =
    'update' |            // Update tab values
    'updateExecution' |   // Update execution result
    'mark' |              // Mark location
    'markError' |         // Mark error location
    'clear' |             // Clear all markings
    'highlight' |         // Highlight the entire file
    'dirty' |             // Fired when file has changed
    'updateArena' |       // Update arena
    'updateExecutionGraph' | // Update execution graph
    'updateMemory' |      // Update memory graph (calls VIZ)
    'markInteractive'     // Mark source locations when in interactive mode

  export interface EventEmitter {
    on (eventName: 'clear', self: any, f: (locs: Locations) => void): void
    on (eventName: 'mark', self: any, f: (locs: Locations) => void): void
    on (eventName: 'markError', self: any, f: (line: number) => void): void
    on (eventName: 'dirty', self: any, f: () => void): void
    on (eventName: 'markInteractive', self: any, f: ((l:any, s: Readonly<State>) => void)): void
    on (eventName: Event, self: any, f: ((s: Readonly<State>) => void)): void
    off (self: any): void 
    once (f: ((s: Readonly<State>) => any)): any
    emit (eventName: 'clear'): void
    emit (eventName: 'mark'): void
    emit (eventName: Event, ...args: any[]): void
  }

  export interface Compiler {
    id: string
    name: string
  }

}

export default Common