import _ from 'lodash'
import { Range } from './location'
import * as u from './util'
import bigInt from 'big-integer'

export type Provenance =
  { kind: 'prov', value: number } |
  { kind: 'iota', value: number, iota: number[] } |
  { kind: 'empty' }

export type Byte = {
  prov: Provenance
  offset: number | null
  value: number | null
}

export type Value = {
  kind: 'unspecified'
      | 'basic'
      | 'pointer'
      | 'intptr'
      | 'funptr'
      | 'unspecptr'
      | 'char'
      | 'padding'
  size: number
  path: string[]      // access path in case of struct/unions
  value: string
  prov: Provenance
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
  base: string      // base address (bigint)
  prefix: Prefix    // source name with scope order
  type: string      // pretty core ctype
  size: number      // type size
  dyn: boolean      // is dynamic memory (created by malloc)
  values: Value[]   // INV: this should be a singleton in scalar types
  exposed: boolean  // exposed mechanism
}

export type Map = {[key:string]: Allocation}

export type State = {
  map: Map
  last_used: number | null
}

/** Value points to some place in the memory */
export function pointsto (v: Value): boolean {
  return v.value != 'NULL' && (v.kind == 'pointer' || v.kind == 'intptr')
}

export function ispadding (v: Value) {
  return v.kind == 'padding'
}

export function isInvalidPointer(pvi: boolean, v: Value) {
  if (v.bytes == null) return false
  if (pvi) return v.prov.kind == 'empty'
  return !_.reduce(v.bytes, (acc, b, i) => acc && b.offset != null && b.offset == i, true)
}

function hasSpecifiedBytes(v: Value) {
  if (v.bytes == null) return false
  return _.reduce(v.bytes, (acc, b) => acc || (b != null && b.value != null), false)
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

export function string_of_provenance (p: Provenance): string {
  const idOf = (i: number): string => {
    return (i >= 26 ? idOf((i / 26 >> 0) - 1) : '') + 'abcdefghijklmnopqrstuvwxyz'[i % 26 >> 0];
  }
  switch (p.kind) {
    case 'prov': return `@${p.value}`
    case 'iota': return `@${idOf(p.value)}={${p.iota}}`
    case 'empty': return '@empty'
  }
}

/** string of memory value  */
export function string_of_value (v: Value, pvi: boolean, show_pointer_bytes: boolean): [string, boolean] /* value * multirow */ {
  const with_prov = () => string_of_provenance(v.prov) + ', '
  const value = (x:string) => pvi ? with_prov() + x : x
  function multirow_pointer(): [string, boolean] {
    const mk_value = (i: number) => {
      if (v.bytes == null || v.bytes[i] == null)
        return 'unspecified'
      else if (pvi)
        return string_of_provenance(v.bytes[i].prov) + ', ' + v.bytes[i].value == null ? "unspecified" : u.toHex(v.bytes[i].value)
      else
        return (v.bytes[i].offset != null ? v.bytes[i].offset : '-') + ': ' + u.toHex(v.bytes[i].value) + string_of_provenance(v.bytes[i].prov)
    }
    if (v.bytes == null)
      return [v.value, false]
    let value
    value = `<table cellpadding="0" cellspacing="0" border="0">
                <tr border="1">
                  <td align="left">${mk_value(0)}</td>
                  <td align="center" vspan="${v.bytes.length}">${string_of_provenance(v.prov)}, 0x${bigInt(v.value).toString(16)}</td>
                </tr>`
    for (let j = 1; j < v.bytes.length; j++) {
      value += `<tr><td align="left" border="1" sides="t">${mk_value(j)}</td></tr>`
    }
    value += '</table>'
    return [value, true]
  }
  switch(v.kind) {
    case 'unspecified':
      if (v.bytes != null && hasSpecifiedBytes(v)) {
        let value;
        value = `<table cellpadding="0" cellspacing="0" border="0">
                   <tr border="1">
                    <td align="left">${v.bytes[0].value != null ? v.bytes[0].value : "unspecified"}</td>
                    <td align="center" rowspan="${v.bytes.length}">unspecified</td>
                   </tr>`
        for (let j = 1; j < v.bytes.length; j++)
          value += `<tr><td align="left" border="1" sides="t">${v.bytes[j].value != null ? v.bytes[j].value : "unspecified"}</td></tr>`
        value += '</table>'
        return [value, true]
      } else {
        return ['unspecified', false]
      }
    case 'basic':
      return [v.value, false]
    case 'pointer':
      if (v.value == 'NULL')
        return ['NULL', false]
      else if (show_pointer_bytes || isInvalidPointer(pvi, v))
        return multirow_pointer()
      else
      return [with_prov() + "0x"+bigInt(v.value).toString(16), false]
    case 'funptr':
      return [v.value, false]
    case 'intptr':
      return [value("0x"+bigInt(v.value).toString(16)), false]
    case 'unspecptr':
      if (hasSpecifiedBytes(v))
        return multirow_pointer ()
      else
        return [v.value, false]
    case 'char':
      const char = (s: string) => {
        const c = char_code(s)
        if (c === '') return ''
        return ` '${c}'`
      }
      return [v.value + char(v.value), false]
    case 'padding':
      return ["", false] // TODO: should I show something for paddings?
  }
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