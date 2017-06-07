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
  let p = std[ns[0]][ns[1]][ns[2]]
  return section + '\n' + p['title'] + '\n' + p[ns[3]]
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
  ui.worker.postMessage({type: 'read'})
  ui.setup()
})
