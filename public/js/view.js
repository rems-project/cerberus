'use_strict'

class View {
  constructor (title, data) {
    let source = new TabSource(title, data)

    this.tabs = []
    this.title  = title
    this.source = source
    this.tabs.push(source)
    this.dom = $('<div class="view"></div>')
    $('#views').append(this.dom)

    let config = {
      settings:{
          hasHeaders: true,
          constrainDragToContainer: true,
          reorderEnabled: true,
          selectionEnabled: false,
          popoutWholeStack: false,
          blockedPopoutsThrowError: true,
          closePopoutsOnUnload: true,
          showPopoutIcon: false,
          showMaximiseIcon: true,
          showCloseIcon: true
      },
      dimensions: {
          borderWidth: 5,
          minItemHeight: 10,
          minItemWidth: 10,
          headerHeight: 20,
          dragProxyWidth: 300,
          dragProxyHeight: 200
      },
      labels: {
          close: 'Close',
          maximise: 'Maximise',
          minimise: 'Minimise'
      },
      content: [{
        type: 'row',
        content: [{
          type: 'component',
          title: title,
          componentName: 'source',
          isClosable: false
        }]
      }]
    }
    this.layout = new GoldenLayout (config, this.dom);

    // Activate source tab
    this.source.setActive()

    // Empty data
    this.data = {
      pp: {
        cabs: "",
        ail:  "",
        core: ""
      },
      ast: {
        cabs: "",
        ail:  "",
        core: ""
      },
      locs: [],
      stdout: "",
      stderr: "",
      steps: [],
      console: ""
    }

    this.content = {}

    this.isHighlighted = false;
    this.dirty = true;

    // WARN: GoldLayout does not support arrow functions when registering
    // a component
    this.layout.registerComponent('source',
      function (container, state) {
        $(container.getElement()).append(source.dom.content)
      }
    )
    this.layout.registerComponent('tab',
      function (container, state) {
        $(container.getElement()).append(state.tab.dom.content)
      }
    )
    this.layout.on('itemDestroyed', (c) => {
      if (c.componentName == 'tab') {
        let tab = c.config.componentState.tab
        for (let i = 0; i < this.tabs.length; i++) {
          if (this.tabs[i] === tab) {
            this.tabs.splice(i, 1)
            break
          }
        }
      }
    })
    this.layout.init()
  }

  getValue() {
    return this.source.getValue()
  }

  add (tab) {
    this.tabs.push(tab)
    tab.alive = true
    this.layout.root.contentItems[ 0 ].addChild({
      type: 'component',
      componentName: 'tab',
      title: tab.title,
      componentState: { tab: tab }
    });
    tab.addEventListener()
    tab.refresh()
  }

  get exec() {
    if (!this._execTab)
      this._execTab = new TabReadOnly('Execution')
    this.add(this._execTab)
    return this._execTab
  }

  get cabs() {
    let tab = new TabCabs()
    this.add(tab)
    return tab
  }

  get ail() {
    let tab = new TabAil()
    this.add(tab)
    return tab
  }

  get ail_ast() {
    let tab = new TabAil()
    this.add(tab)
    return tab
  }


  get core() {
    let tab = new TabCore()
    this.add(tab)
    return tab
  }

  get console() {
    if (!this._consoleTab)
      this._consoleTab = new TabReadOnly('Console')
    this.add(this._consoleTab)
    return this._consoleTab;
  }

  get graph() {
    if (!this._graphTab)
      this._graphTab = new TabGraph('Graph')
    this.add(this._graphTab)
    return this._graphTab;
  }

  forEachTab(f) {
    for (let i = 0; i < this.tabs.length; i++)
      f(this.tabs[i])
  }

  mark(loc) {
    if (loc) {
      this.forEachTab((tab) => tab.mark(loc))
    }
  }

  clear() {
    this.forEachTab((tab) => tab.clear())
  }

  markSelection(loc) {
    if (!this.dirty && loc) {
      this.isHighlighted = false
      this.clear()
      this.mark(loc)
    }
  }

  highlight() {
    if (!ui.colour) {
      this.clear()
      return;
    }
    if (this.isHighlighted||this.dirty)
      return;
    this.clear()
    this.forEachTab((tab) => tab.highlight())
    this.isHighlighted = true
  }

  show() {
    this.dom.show()
  }

  hide() {
    this.dom.hide()
  }

  update(data) {
    Object.assign(this.data, data)
    this.dirty = false
    this.isHighlighted = false
    this.forEachTab((tab) => tab.update())
    this.isHighlighted = false
  }

  newTab(mode, lang) {
    let tab = this[lang];
    tab.setValue(this.data[mode][lang])
    if (ui.colour) tab.highlight()
  }

  refresh () {
    this.layout.updateSize()
  }
}
