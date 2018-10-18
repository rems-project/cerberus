import $ from 'jquery'
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
import { Settings, Model } from './ui'

function getDefaultSettings(): Settings {
    return { rewrite: false,
             sequentialise: false,
             auto_refresh: true,
             colour: false,
             colour_cursor: true,
             short_share: false,
             model: 'concrete',
           }
}

type StartupMode =
  { kind: 'default', settings: Settings } |
  { kind: 'permalink', config: any, settings: Settings } |
  { kind: 'fixedlink', file: string, settings: Settings }

function model_of_string(m:string): Model {
  if (m != 'concrete' && m != 'symbolic' && m != 'twin')
    throw `Model ${m} does not exist.`
  return m
}

function getStartupMode(): StartupMode {
  function parsedFixedArguments(args: string []): [string, Settings] {
    let file: string | undefined
    const settings = getDefaultSettings()
    function updateSettings(param: string, value: string) {
      const toBool = (b: string) => b === 'true'
      switch(param) {
        case 'rewrite':
          settings.rewrite = toBool(value)
          break
        case 'sequentialise':
          settings.sequentialise = toBool(value)
          break
        case 'auto_refresh':
          settings.auto_refresh = toBool(value)
          break
        case 'color':
        case 'colour':
          settings.colour = toBool(value)
          break
        case 'color_cursor':
        case 'colour_cursor':
          settings.colour_cursor = toBool(value)
          break
        case 'short_share':
          settings.short_share = toBool(value)
          break
        case 'model':
          settings.model = model_of_string(value)
          break
        default:
          throw `Unknown argument ${param}`
      }
    }
    args.map(arg => {
      const params = arg.split('=')
      if (params[0] && params[1]) {
        updateSettings(params[0], params[1])
      } else {
        file = params[0]
      }
    })
    if (file !== undefined)
      return [file, settings]
    throw 'Missing filename in fixed link'
  }
  try {
    // First try a permanent link
    let uri = document.URL.split('#')
    if (uri && uri.length == 2 && uri[1] !== '') {
      const config = GoldenLayout.unminifyConfig(JSON.parse(decodeURIComponent(uri[1])))
      return { kind: 'permalink',
              config: config,
              settings: getDefaultSettings()
            }
    }
    // Try fixed links
    uri = document.URL.split('?')
    if (uri && uri.length == 2 && uri[1] !== '') {
      const [file, settings] = parsedFixedArguments(uri[1].split('&'))
      return { kind: 'fixedlink',
              file: file,
              settings: settings
            }
    }
    // Default
    return { kind: 'default', settings: getDefaultSettings() }
  } catch (e) {
    console.log(`Startup error: ${e}`)
    return { kind: 'default', settings: getDefaultSettings() }
  }
}

function defaultStart() {
  get('buffer.c', (source: string) => {
    UI.addView('example.c', source)
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
        UI.addView(mode.file, source)
      }, () => {
        console.log(`Error when trying to download ${mode.file}`)
        alert(`Error downloading ${mode.file}...`)
        defaultStart()
      })
      break
  }
  UI.setSettings(mode.settings)
}

$(window).ready(onLoad)