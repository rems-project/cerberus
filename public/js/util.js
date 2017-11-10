'use_strict'

function fadeOut(tooltip) {
    function remove(node) {
      var p = node && node.parentNode;
      if (p) p.removeChild(node);
    }
    tooltip.style.opacity = "0";
    setTimeout(function() { remove(tooltip); }, 1100);
  }

// WARNING: Unused function
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

function getColor(i) {
  return 'color' + (i % 100)
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
  let i = 0
  for (; i < ns.length - 1; i++) {
    p = p[ns[i]]
    title += ns[i] + '.'
    if (p['title'])
      content += '<h3>'+ns[i]+'. '+p['title']+'</h3>'
  }
  // if has a paragraph
  if (p['P'+ns[i]]) {
    title = title.slice(0,-1) + '#' + ns[i]
    content += p['P'+ns[i]]
  } else {
    p = p[ns[i]]
    title += ns[i]
    if (p['title'])
      content += '<h3>'+ns[i]+'. '+p['title']+'</h3>'
    let j = 1
    while (p['P'+j]) {
      content += p['P'+j] + '</br>'
      j++
    }
  }
  let div = $('<div class="std">'+content+'</div>')
  // Create footnotes
  div.append('<hr/>')
  div.children('foot').each(function(i) {
    let n = '['+(i+1)+']'
    $(this).replaceWith(n)
    div.append('<div style="margin-top: 5px;">'+n+'. '+ $(this).html()+'</div>')
  })
  div.append('<br>')
  return {title: title, data: div}
}

function getSTDSentence(section) {
  let ns = section.match(/\d+/g)
  let title = '§'
  let p = std
  let content = ""
  for (let i = 0; i < ns.length - 1; i++) {
    p = p[ns[i]]
  }
  content += p['P'+ns[ns.length-1]]
  return content
}

// TODO: function not being used anymore
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
    locations: locs,
    ast: core,
  }
}

function json_to_dot(data) {
  function aux (i, d) {
    switch (d.label) {
      case "active":
        return {
          index: i+1,
          nodes: [parseInt(i) + '[label="' + d.arena + '"]'],
          edges: []
        }
      case "killed":
        return {
          index: i+1,
          nodes: [parseInt(i) + '[label="killed"]'],
          edges: []
        }
      case "nd":
        let nd = { index: i, nodes: [], edges: [] }
        for (let j = 0; j < d.children.length; j++) {
          let c = aux(nd.index+1, d.children[j])
          nd.nodes = nd.nodes.concat(c.nodes)
          nd.edges = nd.edges.concat(c.edges)
          nd.edges.push(parseInt(i) + " -> " + parseInt(nd.index+1))
          nd.index = c.index
        }
        nd.nodes.push(parseInt(i) + '[label="nd('+ d.debug + ')"]')
        return nd
      case "guard":
        let c = aux(i+1, d.child)
        c.nodes.push(parseInt(i) + '[label="guard(' + d.debug + ')"]')
        c.nodes.push(parseInt(i) + " -> " + parseInt(i+1))
        return c
      case "branch":
        let c1 = aux(i+1, d.child1)
        let c2 = aux(c1.index+1, d.child2)
        let ns = c2.nodes.concat(c1.nodes)
        let es = c2.edges.concat(c1.edges)
        ns.push(parseInt(i) + '[label="branch(' + d.debug + ')"]')
        es.push(parseInt(i) + " -> " + parseInt(i+1))
        es.push(parseInt(i) + " -> " + parseInt(c1.index+1))
        return {
          index: c2.index,
          nodes: ns,
          edges: es
        }
    }
    alert ('json_to_dot: fatal error')
  }
  let x = aux(1, data)
  let dot = "digraph G {node[shape=box];"
  for (let i = 0; i < x.nodes.length; i++)
    dot += x.nodes[i] + ";"
  for (let i = 0; i < x.edges.length; i++)
    dot += x.edges[i] + ";"
  dot += "}"

  return dot
}

function clone(data) {
  return JSON.parse(JSON.stringify(data))
}

/* Extend jQuery */
jQuery.fn.extend({
  disable: function(state) {
    return this.each(function() {
      var $this = $(this);
      $this.prop('disabled', state);
    });
  }
});
