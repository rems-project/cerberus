type level = BUG | ERROR | WARNING | INFO | DEBUG
type 'a printer = 'a -> string
type t = {
  level : level;
  format : string Lazy.t
}

let make level printer data = {level; format = lazy (printer data)}

let bug printer data = make BUG printer data
let error printer data = make ERROR printer data
let warning printer data = make WARNING printer data
let info printer data = make INFO printer data
let debug printer data = make DEBUG printer data

let to_string {format; _} = Lazy.force format
let level {level; _} = level
