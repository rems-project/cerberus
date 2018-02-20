'use_strict'

class View {
  constructor (title, data) {
    this.tabs = []
    this.title  = title
    this.source = new TabSource(title, data)
    this.source.setActive() // TODO: see if i'm using active
    this.tabs.push(this.source)

    // GUI
    this.dom = $('<div class="view"></div>')
    $('#views').append(this.dom)
    this.initLayout()

    // State
    this.setStateEmpty()
    this.isHighlighted = false;
    this.dirty = true;
  }

  initLayout() {
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
      content: []
    }
    this.layout = new GoldenLayout (config, this.dom);
    this.layout.registerComponent('tab',
      function (container, state) {
        $(container.getElement()).append(state.tab.dom)
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
    this.layout.on( 'tabCreated', function( tabHeader ){
      if (tabHeader.contentItem.isComponent) {
        let tab = tabHeader.contentItem.config.componentState.tab
        tabHeader.element.on('mousedown', function () {
          tab.refresh()
        })
      }
    })
    this.layout.init()
  }

  setStateEmpty() {
    this.state = {
      status: 'failure',
      pp: {
        cabs: '',
        ail:  '',
        core: ''
      },
      ast: {
        cabs: '',
        ail:  '',
        core: ''
      },
      locs: [],
      steps: [],
      result: '',
      console: ''
    }
  }

  makeGrid() {
    let core = new TabCore()
    this.tabs.push(core)

    let execution = new TabExecution()
    this.tabs.push(execution)

    let console = new TabConsole()
    this.tabs.push(console)

    let grid = {
      type: 'row',
      content: [{
        type: 'column',
        content: [
          this.source.component(), {
            type: 'stack',
            content: [
              console.component(),
              execution.component()
            ]}
        ]},
        core.component()
      ]}
    this.layout.root.addChild(grid)
  }

  getValue() {
    return this.source.getValue()
  }

  add (tab) {
    this.tabs.push(tab)
    tab.alive = true
    let content = (this.layout.root.contentItems.length > 0) ?
      this.layout.root.contentItems[0] : this.layout.root
    content.addChild({
      type: 'component',
      componentName: 'tab',
      title: tab.title,
      componentState: { tab: tab }
    });
    tab.refresh()
  }

  forEachTab(f) {
    for (let i = 0; i < this.tabs.length; i++)
      f(this.tabs[i])
  }

  findTab(aClass) {
    for (let i = 0; i < this.tabs.length; i++) {
      if (this.tabs[i] instanceof aClass) {
        return this.tabs[i]
      }
    }
    return null
  }

  newTab(aClass) {
    let tab = new aClass(title)
    this.add(tab)
    tab.update(this.state)
    tab.highlight(this.state)
    return tab
  }

  getTab(aClass, title) {
    let tab = this.findTab(aClass)
    if (tab == null)
      tab = this.newTab(aClass, title)
    return tab
  }

  // Return this first instance (or create a new one)
  get exec()    { return this.getTab(TabExecution) }
  get cabs()    { return this.getTab(TabCabs) }
  get ail()     { return this.getTab(TabAil) }
  get core()    { return this.getTab(TabCore) }
  get console() { return this.getTab(TabConsole) }
  get graph()   { return this.getTab(TabGraph) }

  mark(loc) {
    if (loc) this.forEachTab((tab) => tab.mark(loc))
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
    if (this.isHighlighted||this.dirty) return;
    this.clear()
    this.forEachTab((tab) => tab.highlight(this.state))
    this.isHighlighted = true
  }

  show() {
    this.dom.show()
  }

  hide() {
    this.dom.hide()
  }

  update() {
    this.forEachTab((tab) => tab.update(this.state))
    this.highlight()
  }

  setState (s) {
    if (s.status == 'failure') this.setStateEmpty()
    Object.assign(this.state, s) // merge states
    this.dirty = false
    this.isHighlighted = false
    this.update()
  }

  refresh () {
    this.forEachTab((tab) => tab.refresh())
    this.layout.updateSize()
  }
}
