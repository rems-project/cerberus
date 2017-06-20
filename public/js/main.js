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
  let p = std
  let content = ""
  for (let i = 0; i < ns.length - 1; i++) {
    p = p[ns[i]]
    if (p['title'])
      content += '<h'+(i+1)+'>'+ns[i]+'. '+p['title']+'</h'+(i+1)+'>'
  }
  content += p['P'+ns[ns.length-1]]
  let div = $('<div class="std">'+content+'</div>')
  // Create footnotes
  div.append('<hr/>')
  div.children('foot').each(function(i) {
    let n = '['+(i+1)+']'
    $(this).replaceWith(n)
    div.append('<div>'+n+'. '+ $(this).text()+'</div>')
  })
  return div
}


const ui = new UI()
const style = createStyle()
let std = null

// Get STD file
$.getJSON('std.json').done((res) => std = res).fail(() => {
  console.log('Failing when trying to download "std.json"')
})

$(window).ready(() => {
  ui.activePane = new Pane()
  ui.addPane(ui.activePane)
  ui.activePane.addTab(new TabSource())
  ui.activePane.activeTab.setTitle('hello.c')
  // Wait buffer.c to be downloaded by worker
  ui.worker.postMessage(JSON.stringify({type: 'read'}))
  ui.setup()
})
