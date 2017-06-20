self.importScripts('../lib/mcpp.js', 'cerberus.js')

// All the files where correctly downloaded
let cerberusLoaded = false
let nbAttempts = 0

function handleMessage(msg) {
  // If Cerberus is not yet downloaded, try again in a few milliseconds
  if (!cerberusLoaded) {
    console.log('Waiting for cerberus...')
    if (nbAttempts > 10) {
      // Cannot finish downloading Ceberus
      sendMessage({type: 'close'})
      self.close()
      return // shouldn't be able to reach here
    }
    nbAttempts++
    setTimeout(() => handleMessage(msg), 10)
    return
  }

  switch (msg.type) {
    // Return current buffer
    case 'read':
      sendMessage({
        type: 'load',
        data: cerberus.buffer().toString()
      })
      break
    // Run Cerberus and return result
    case 'run':
      let exec = false, exhaustive = false
      switch (msg.mode) {
        case 'exhaustive':
          exhaustive = true
          exec = true
          break
        case 'random':
          exec = true
          break
        case 'core':
        default:
          break
      }
      sendMessage({
        type: 'result',
        data: parseCerberusResult(cerberus.run(msg.source, exec, exhaustive))
      })
      break
  }
}

function parseCerberusResult(res) {
  function countLines(str) {
    return str.split(/\r\n|\r|\n/).length - 1
  }

  // Fail
  if (res[0] != 0) {
    return {
      success: false,
      locations: [],
      core: "",
      console: res[1].toString(),
      batch: ""
    }
  }

  // Success
  let bits = res[1][1].toString().split(/{-#(\d*:\d*-\d*:\d*:|E...)#-}/g)
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
    batch: res[1][2][1].toString()
  }
}


function onLoadCerberus() {
  cerberusLoaded = true
  console.log('Cerberus loaded')
}

function sendMessage (msg) {
  self.postMessage(JSON.stringify(msg))
}

onmessage = (e) => handleMessage(JSON.parse(e.data))
