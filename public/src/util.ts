import $ from "jquery"
import Common from "./common"

namespace Util {

const gapikey = 'AIzaSyDYrDNMlaTvfLxNX_cJ8EH_qrLq7aKeFJc'

export function option(x: any, y: any) {
  if (x) return x
  return y
}

export function shortURL(url: string, f: (_:string) => void) {
  $.ajax({
    type: 'POST',
    url: 'https://www.googleapis.com/urlshortener/v1/url?key=' + gapikey,
    contentType: 'application/json',
    data: JSON.stringify ({longUrl: url}),
    success: (data) => f (data.id)
  })
}

export function longURL(url: string) {
  $.ajax({
    type: 'GET',
    url: 'https://www.googleapis.com/urlshortener/v1/url?key=' + gapikey
          +'&shortUrl=http://goo.gl/' + url,
    success: (data) => {
      console.log(data)
    }
  })
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

// WARNING: Unused function
// @ts-ignore
function generateColor(style: HTMLElement) {
  function basicColor (mix: number) {
    return Math.floor((Math.floor(Math.random()*256)+mix)/2)
  }
  let r = basicColor(255)
  let g = basicColor(255)
  let b = basicColor(255)
  let className = 'color'+r+g+b
  style.innerHTML +=
    '.' + className +' { background-color: rgba('+r+','+g+','+b+',1); }\n'
  return className
}

export function getColor(i: number): string {
  return 'color' + (i % 100)
}

export function getColorByLocC(state: Readonly<Common.State>, cur: Readonly<Common.Range>): string {
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
  document.head.appendChild(style)
  return style
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

} // end namespace


export default Util