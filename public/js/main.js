'use_strict'

function generateColor() {
  function basicColor (mix) {
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


function createStyle() {
  let style = document.createElement('style')
  style.type = 'text/css'
  document.head.appendChild(style)
  return style
}

function getSTDSection(section) {
  let ns = section.match(/\d+/g)
  let title = '§'
  let p = std
  let content = ""
  for (let i = 0; i < ns.length - 1; i++) {
    p = p[ns[i]]
    title += ns[i] + '.'
    if (p['title'])
      content += '<h'+(i+1)+'>'+ns[i]+'. '+p['title']+'</h'+(i+1)+'>'
  }
  title = title.slice(0,-1) + '#' + ns[ns.length-1]
  content += p['P'+ns[ns.length-1]]
  let div = $('<div class="std">'+content+'</div>')
  // Create footnotes
  div.append('<hr/>')
  div.children('foot').each(function(i) {
    let n = '['+(i+1)+']'
    $(this).replaceWith(n)
    div.append('<div>'+n+'. '+ $(this).text()+'</div>')
  })
  return {title: title, data: div}
}

function parseCerberusResult(res) {
  function countLines(str) {
    return str.split(/\r\n|\r|\n/).length - 1
  }

  let bits = res.split(/{-#(\d*:\d*-\d*:\d*:|E...)#-}/g)
  let core = ""
  let locs = [], stkLoc = [], stkLine0 = []
  let l0 = 0, l = 0
  for (let i = 0; i < bits.length; i++) {
    if (bits[i] == 'ELOC') {
      // finish last location
      let cloc = stkLoc.pop().toString().match(/\d+/g)
      locs.push({
        c: {
          begin: {line: cloc[0]-1, ch: cloc[1]-1},
          end: {line: cloc[2]-1, ch: cloc[3]-1}
        },
        core: {
          begin: {line: l0, ch: 0},
          end: {line: l, ch: 0}
        }
      })
      l0 = stkLine0.pop()
      continue;
    }
    if (/\d*:\d*-\d*:\d*:/g.test(bits[i])) {
      stkLine0.push(l0)
      stkLoc.push(bits[i])
      l0 = l
      continue;
    }
    // a bit of core source
    core += bits[i]
    l += countLines(bits[i])
  }

  locs.sort((a, b) => {
    return (a.core.end.line - a.core.begin.line)
      < (b.core.end.line - b.core.begin.line) ? 1:-1
  })

  return {
    success: true,
    locations: locs,
    core: core,
    console: '',
    batch: ''
  }
}

const ui = new UI()
const style = createStyle()
let std = null

$.getJSON('std.json').done((res) => std = res).fail(() => {
  console.log('Failing when trying to download "std.json"')
})

$.get('buffer.c').done((data) => {
  $(window).ready(() => {
    ui.activePane = new Pane()
    ui.addPane(ui.activePane)
    ui.activePane.addTab(new TabSource())
    ui.setup()
    let tab = ui.activePane.activeTab;
    tab.setTitle('hello.c')
    tab.editor.setValue(data)
    tab.setActive()
    tab.refresh()
  })
}).fail(() => {
  console.log('Failing when trying to download "buffer.c"')
})
