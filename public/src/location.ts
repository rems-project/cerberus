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

