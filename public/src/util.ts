import $ from "jquery"
import { State } from "./common"
import { Range } from './location'

export function option(x: any, y: any) {
  if (x) return x
  return y
}

export function toHex(n: number | null): string {
  if (n == null)
    return '' // TODO: not sure of this!
  return "0x" + ("00" + n.toString(16)).substr(2)
}

export namespace Cursor {
  let waitCounter = 0
  export function wait () {
    if (waitCounter == 0)
      $('body').addClass('wait')
    waitCounter++
  }

  export function done () {
    if (waitCounter > 0)
      waitCounter--
    if (waitCounter == 0)
      $('body').removeClass('wait')
  }
}

export function get(url: string, done: Function, fail?: Function) {
  Cursor.wait()
  $.get(url).done(data => {
    done(data)
    Cursor.done()
  }).fail(() => {
    console.log(`Error downloading ${url}.`)
    if (fail) fail()
    Cursor.done()
  })
}

export function fadeOut(tooltip: HTMLElement) {
    function remove(node: HTMLElement) {
      var p = node && node.parentNode;
      if (p) p.removeChild(node);
    }
    tooltip.style.opacity = "0";
    setTimeout(function() { remove(tooltip); }, 1100);
  }

export function getColor(i: number): string {
  return 'color' + (i % 100)
}

export function getColorByLocC(state: Readonly<State>, cur: Readonly<Range>): string {
  for (let i = 0; i < state.locs.length; i ++) {
    const loc = state.locs[i].c
    if ((loc.begin.line < cur.begin.line
        || (loc.begin.line == cur.begin.line && loc.begin.ch <= cur.begin.ch))
    && (loc.end.line > cur.end.line)
        || (loc.end.line == cur.end.line && loc.end.ch >= cur.end.ch)) {
      return 'color' + state.locs[i].color;
    }
  }
  return 'no-color'
  //throw new Error ('getColorByLoC: Location not found!')
}

export function createStyle() {
  let style = document.createElement('style')
  style.type = 'text/css'
  // @ts-ignore
  document.head.appendChild(style)
  return style
}

export function checkOverflow(elem: JQuery<HTMLElement>, container: JQuery<HTMLElement>): string {
  if (elem.length != 1 || container.length != 1)
    throw new Error('checkOverflow expects only 1 element and 1 container.')
  const elemMetrics = elem[0].getBoundingClientRect()
  const elemRight = Math.floor(elemMetrics.right)
  const elemLeft  = Math.floor(elemMetrics.left)
  const containerMetrics = container[0].getBoundingClientRect()
  const containerRight = Math.floor(containerMetrics.right)
  const containerLeft  = Math.floor(containerMetrics.left)
  if (containerLeft > elemLeft && containerRight < elemRight)
    return 'both'
  else if (elemLeft < containerLeft)
    return 'left'
  else if (elemRight > containerRight)
    return 'right'
  else
    return 'none'
}

// WARNING: Unused function
// @ts-ignore
function getSTDSentence(std: any, section: string) {
  let ns = section.match(/\d+/g)
  if (!ns) return
  //let title = '§'
  let p = std
  let content = ""
  for (let i = 0; i < ns.length - 1; i++) {
    p = p[ns[i]]
  }
  content += p['P'+ns[ns.length-1]]
  return content
}

export function triggerClick(elem: HTMLElement): void {
  var clickEvent = document.createEvent ('MouseEvents');
  clickEvent.initEvent ('mousedown', true, true);
  elem.dispatchEvent (clickEvent);
  clickEvent.initEvent ('mouseup', true, true);
  elem.dispatchEvent (clickEvent);
}