import $ from 'jquery'
import _ from 'lodash'
import './css/scheme.css'
import './css/goldenlayout-base.css'
import './css/goldenlayout-light-theme.css'
import './css/codemirror.css'
import './css/style.css'
import './js/gas.js'
import './js/clike.js'
import './js/ast.js'
import './js/core.js'
import './js/ocaml.js'
import './js/placeholder.js'
import './js/panzoom.js'
import GoldenLayout from 'golden-layout'
import UI from './ui'
import { get } from './util'

type StartupMode =
  { kind: 'default' } |
  { kind: 'permalink', config: any } |
  { kind: 'fixedlink', file: string }

function getStartupMode(): StartupMode {
  try {
    // First try a permanent link
    let uri = document.URL.split('#')
    if (uri && uri.length == 2 && uri[1] !== '') {
      const config = GoldenLayout.unminifyConfig(JSON.parse(decodeURIComponent(uri[1])))
      return { kind: 'permalink',
              config: config,
            }
    }
    // Try fixed links
    uri = document.URL.split('?')
    if (uri && uri.length == 2 && uri[1] !== '') {
      const file = uri[1]
      return { kind: 'fixedlink',
              file: file,
              //settings: settings
            }
    }
    // Default
    return { kind: 'default'}
  } catch (e) {
    console.log(`Startup error: ${e}`)
    return { kind: 'default'}
  }
}

function defaultStart() {
  get('buffer.c', (source: string) => {
    UI.addView('example.c', source)
    UI.elab()
  }, () => {
    console.log('Error when trying to download "buffer.c"... Using an empty file.')
    UI.addView('example.c', '')
  })
}

export function onLoad() {
  const mode = getStartupMode()
  switch (mode.kind) {
    case 'default':
      defaultStart()
      break
    case 'permalink':
      UI.addView(mode.config.title, mode.config.source, mode.config)
      break
    case 'fixedlink':
      get(mode.file, (source: string) => {
        const explode = mode.file.split('/')
        const name = _.startsWith(mode.file, 'short/') ? 'example.c' : explode[explode.length-1]
        UI.addView(name, source)
      }, () => {
        console.log(`Error when trying to download ${mode.file}`)
        alert(`Error downloading ${mode.file}...`)
        defaultStart()
      })
      break
  }
}

$(window).ready(onLoad)