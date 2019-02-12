import _ from 'lodash'
import { Range } from './location'
import * as u from './util'

export type Byte = {
  prov: number | null
  offset: number | null
  value: number | null
}

export type Value = {
  size: number
  path: string[]      // access path in case of struct/unions
  value: string
  prov: number | null
  type: string | null // if no type, then it is padding
  bytes: Byte [] | null
}

export type Prefix = {
  kind: 'source' | 'string literal' | 'arg' | 'malloc',
  name: string,
  scope: string | null,
  loc: Range | null
}

export type Allocation = {
  id: number        // allocation id (provenance)
  base: number      // base address
  prefix: Prefix    // source name with scope order
  type: string      // pretty core ctype
  size: number      // type size
  dyn: boolean      // is dynamic memory (created by malloc)
  values: Value[]   // INV: this should be a singleton in scalar types
}

export type Map = {[key:string]: Allocation}

export type State = {
  map: Map
  last_used: number | null
}

export function ispointer (v: Value): boolean {
  return v.type != null && _.endsWith(v.type, '*')
}

export function isfunptr (v:Value): boolean {
  return isNaN (parseInt(v.value))
}

export function isintptr (v: Value) {
  return v.type != null && (v.type == 'intptr_t' || v.type == 'uintptr_t' || v.type == 'ptrdiff_t')
}

export function ischar (v: Value): boolean {
  return v.type != null && (v.type == 'char' || v.type == 'signed char' || v.type == 'unsigned char')
}

/** Value points to some place in the memory */
export function pointsto (v: Value): boolean {
  return ispointer(v) || isintptr(v)
}

export function ispadding (v: Value) {
  return v.type == null
}

export function isInvalidPointer(pvi: boolean, v: Value) {
  if (v.bytes == null) return false
  if (pvi) return v.prov == null
  return !_.reduce(v.bytes, (acc, b, i) => acc && b.offset != null && b.offset == i, true)

}

function char_code (s:string) {
  const x = parseInt(s)
  // printable characters
  if (32 <= x && x <= 126)
    return String.fromCharCode(x)
  // escaped characters (only ISO ones)
  switch (x) {
    case 7: return "\\a"
    case 8: return "\\b"
    case 9: return "\\t"
    case 10: return "\\n"
    case 11: return "\\v"
    case 13: return "\\r"
    case 14: return "\\f"
  }
  // otherwise
  return ""
}

export function mk_string (values: Value []): string {
  return `"${values.reduce((acc, v) => acc + char_code(v.value), '')}"`
}

/** string of memory value  */
export function string_of_value (v: Value, track_prov: boolean): string {
  const with_prov = () => v.prov != undefined ? `@${v.prov}, ` : `@empty, `
  const value = (x:string) => track_prov ? with_prov() + x : x
  if (v.value === 'unspecified')
    return v.value
  if (ispointer(v) && v.value != 'NULL') {
    let i = parseInt(v.value)
    if (isNaN(i))
      return v.value // function pointers
    return with_prov() + u.toHex(i)  
  }
  if (isintptr(v))
    return value(u.toHex(parseInt(v.value)))
  if (ischar(v)) {
    const char = (s: string) => {
      const c = char_code(s)
      if (c === '') return ''
      return ` '${c}'`
    }
    return u.toHex(parseInt(v.value)) + char(v.value)
  }
  return v.value
}

export function unique (v: Prefix, m: Map):  'unique' |'unique-in-scope' | 'non-unique'  {
  const pres = _.map(m, a => a.prefix)
                .filter(p => p.kind === 'source' && p.name === v.name)
  if (pres.length == 1)
    return 'unique'
  if (pres.filter(p => p.kind === 'source' && p.scope === v.scope).length == 1)
    return 'unique-in-scope'
  return 'non-unique'
}