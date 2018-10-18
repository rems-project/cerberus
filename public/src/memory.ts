import _ from 'lodash'
import { Range } from './location'
import * as u from './util'

export type Value = {
  size: number
  path: string[]      // access path in case of struct/unions
  value: string
  prov: number | null
  type: string | null // if no type, then it is padding
}

export type Prefix =
  { kind: 'source', name: string, scope: string | null, loc: Range | null } |
  { kind: 'other', name: string }

export type Allocation = {
  id: number        // allocation id (provenance)
  base: number      // base address
  prefix: Prefix    // source name with scope order
  type: string      // pretty core ctype
  size: number      // type size
  values: Value[]   // INV: this should be a singleton in scalar types
}

export type Map = {[key:string]: Allocation}

export type State = {
  map: Map
  last_modified: number | null
  last_read: number | null
}

export function ispointer (v: Value): boolean {
  return v.type != null && _.endsWith(v.type, '*')
}

export function isintptr (v: Value) {
  return v.type != null && (v.type == 'intptr_t' || v.type == 'uintptr_t' || v.type == 'ptrdiff_t')
}

/** Value points to some place in the memory */
export function pointsto (v: Value): boolean {
  return ispointer(v) || isintptr(v)
}

export function ispadding (v: Value) {
  return v.type == null
}

/** string of memory value  */
export function string_of_value (v: Value): string {
  if (v.value === 'unspecified')
    return v.value
  if (pointsto(v))
    return u.toHex(parseInt(v.value))
  return v.value
}

export function unique (v: Prefix, m: Map):  'unique' |'unique-in-scope' | 'non-unique'  {
  switch (v.kind) {
    case 'other':
      return 'non-unique'
    case 'source':
      const pres = _.map(m, a => a.prefix)
                    .filter(p => p.kind === 'source' && p.name === v.name)
      if (pres.length == 1)
        return 'unique'
      if (pres.filter(p => p.kind === 'source' && p.scope === v.scope).length == 1)
        return 'unique-in-scope'
      return 'non-unique'
  }
}