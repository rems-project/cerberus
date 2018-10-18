import { Node, Edge, Graph } from './graph'
import { Range, Locations } from './location'

export type Bytes = string | undefined
export type ID = number

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
  step_counter: number
  stdout: string
  //lastCline: number | undefined
  history: ID [] // History of execution (allows to go back)
  exec_options: ID []
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
  'updateStepButtons' |
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