let gapikey = 'AIzaSyDYrDNMlaTvfLxNX_cJ8EH_qrLq7aKeFJc'

function assert(x) {
  if (!x) console.log ('assertion failed: ' + x)
}

function option(x, y) {
  if (x) return x
  return y
}

function shortURL(url, f) {
  $.ajax({
    type: 'POST',
    url: 'https://www.googleapis.com/urlshortener/v1/url?key=' + gapikey,
    contentType: 'application/json',
    data: JSON.stringify ({longUrl: url}),
    success: (data) => f (data.id)
  })
}

function longURL(url) {
  $.ajax({
    type: 'GET',
    url: 'https://www.googleapis.com/urlshortener/v1/url?key=' + gapikey
          +'&shortUrl=http://goo.gl/' + url,
    success: (data) => {
      console.log(data)
    }
  })
}

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
  let loc = section.match(/\d(\.\d)*(#\d)?/)[0].split(/#/)
  let ns = loc[0].match(/\d+/g)
  let title = '§'
  let p = std
  let content = ""
  for (let i = 0; i < ns.length; i++) {
    p = p[ns[i]]
    title += ns[i] + '.'
    if (p['title'])
      content += '<h3>'+ns[i]+'. '+p['title']+'</h3>'
  }
  // if has a paragraph
  if (loc[1] && p['P'+loc[1]]) {
    title = title.slice(0,-1) + '#' + loc[1]
    content += p['P'+loc[1]]
  } else {
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

function clone(data) {
  return JSON.parse(JSON.stringify(data))
}

function triggerClick(elem) {
  var clickEvent = document.createEvent ('MouseEvents');
  clickEvent.initEvent ('mousedown', true, true);
  elem.dispatchEvent (clickEvent);
  clickEvent.initEvent ('mouseup', true, true);
  elem.dispatchEvent (clickEvent);
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
