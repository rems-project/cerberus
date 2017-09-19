'use_strict'

class View {
  constructor (title, data) {
    // Dom
    this.panes = []
    this.dom = $('<div class="view"></div>')

    // Create source tab
    this.title  = title
    this.source = new TabSource(title, data)

    // Create an active pane
    this.activePane = new Pane()
    this.activePane.add(this.source)
    this.add(this.activePane)

    // Activate source tab
    this.source.setActive()

    // Global view variables
    this.draggedTab = null
    this.locations  = null
  }

  setActivePane(pane) {
    if (this.activePane)
      this.activePane.setInactive()
    this.activePane = pane
  }

  getValue() {
    return this.source.getValue()
  }

  get firstPane () {
    if (this.panes.length > 0)
      return this.panes[0]
    let pane = new Pane()
    this.add(pane)
    this.setup()
    return pane
  }

  get secondaryPane () {
    if (this.panes.length < 2 || !this.activePane) {
      let pane = new Pane()
      this.add(pane)
      this.setup()
      return pane
    }
    for (let i = 1; i < this.panes.length - 1; i++) {
      if (this.panes[i-1] == this.activePane)
        return this.panes[i]
    }
    return this.panes[this.panes.length - 1]
  }

  add (pane) {
    if (this.panes.length > 0) {
      $('<div class="pane-separator vertical"></div>').appendTo(this.dom)
    }
    this.panes.push(pane)
    this.dom.append(pane.dom)
    pane.parent = this
    pane.refresh()
    this.setup()
  }

  remove (pane) {
    let sep = null
    if (this.panes[0] === pane)
      sep = pane.dom.next('.pane-separator')
    else
      sep = pane.dom.prev('.pane-separator')
    sep.remove()
    pane.dom.remove()

    for (let i = 0; i < this.panes.length; i++) {
      if (this.panes[i] === pane) {
        this.panes.splice(i, 1)
      }
    }
    this.setup()
  }

  getSource() {
    if (!this.source.parent)
      this.firstPane.add(this.source)
    return this.source;
  }

  get exec() {
    if (!this._execTab)
      this._execTab = new TabReadOnly(this.title + ' [exec]')
    if (!this._execTab.parent)
      this.secondaryPane.add(this._execTab)
    return this._execTab
  }

  get cabs() {
    if (!this._cabsTab)
      this._cabsTab = new TabCore(this.title + ' [cabs]')
    if (!this._cabsTab.parent)
      this.secondaryPane.add(this._cabsTab)
    return this._cabsTab;
  }

  get ail() {
    if (!this._ailTab)
      this._ailTab = new TabCore(this.title + ' [ail]')
    if (!this._ailTab.parent)
      this.secondaryPane.add(this._ailTab)
    return this._ailTab;
  }

  get core() {
    if (!this._coreTab)
      this._coreTab = new TabCore(this.title + ' [core]')
    if (!this._coreTab.parent)
      this.secondaryPane.add(this._coreTab)
    return this._coreTab;
  }

  get console() {
    if (!this._consoleTab)
      this._consoleTab = new TabReadOnly(this.title + ' [console]')
    if (!this._consoleTab.parent)
      this.secondaryPane.add(this._consoleTab)
    return this._consoleTab;
  }

  get graph() {
    if (!this._graphTab)
      this._graphTab = new TabGraph(this.title + ' [graph]')
    if (!this._graphTab.parent)
      this.secondaryPane.add(this._graphTab)
    return this._graphTab;
  }

  setup () {
    let w = window.innerWidth/this.panes.length + 'px'
    for (let i = 0; i < this.panes.length; i++) {
      this.panes[i].dom.width(w)
    }
    $('.pane-separator').on('mousedown', e => this.onresize(e))
  }

  unsplit() {
    let tabs = []
    for (let i = 1; i < this.panes.length; i++) {
      let pane = this.panes[i]
      for (let j = 0; j < pane.tabs.length; j++) {
        tabs.push(pane.tabs[j]);
      }
    }
    for (let i = 0; i < tabs.length; i++) {
      let tab = tabs[i]
      tab.parent.remove(tab)
      this.firstPane.add(tab)
      tab.setActive()
      tab.addEventListener()
      tab.refresh()
    }
    for (let i = 1; i < this.panes.length; i++) {
      this.remove(this.panes[i])
    }
  }

  mark(loc) {
    this.source.markText (loc.c.begin, loc.c.end, {className: loc.color})
    this._coreTab.colorLines (loc.core.begin.line, loc.core.end.line, loc.color)
  }

  markSelection(loc) {
    if (!this.source.dirty) {
      this.isHighlighted = false
      this.clear()
      this.mark(loc)
    }
  }

  highlight() {
    if (!this._coreTab||!this.locations||this.isHighlighted||this.source.dirty)
      return;
    this.clear()
    for (let i = 0; i < this.locations.length; i++) {
      this.mark(this.locations[i])
    }
    this.isHighlighted = true
  }

  clear() {
    this.source.clear()
    if (this._coreTab)
      this._coreTab.clear()
  }

  show() {
    this.dom.show()
  }

  hide() {
    this.dom.hide()
  }

  refresh () {
    let factor = window.innerWidth / window.prevWidth
    for (let i = 0; i < this.panes.length; i++) {
      let w = parseFloat(this.panes[i].dom[0].style.width.slice(0, -2))
      this.panes[i].dom[0].style.width = (w * factor)+'px'
    }
    window.prevWidth = window.innerWidth
  }

  onresize (evt) {
    let x0 = evt.clientX
    let sep = $(evt.currentTarget)
    let pane = sep.prev()
    let paneWidth = pane.width()
    let nextPane = sep.next()
    let nextPaneWidth = nextPane.width()
    let minX = pane.position().left
    let maxX = nextPane.position().left + nextPaneWidth

    function resize (evt) {
      if (minX < evt.clientX && evt.clientX < maxX) {
        let delta = evt.clientX - x0
        pane.width(paneWidth+delta)
        nextPane.width(nextPaneWidth-delta)
      }
    }

    function stop (evt) {
      sep.removeClass('resize')
      $('div').each((i, e) => e.style.pointerEvents = '')
      $(document).off('mousemove');
      $(document).off('mouseup');
    }

    $(sep).addClass('resize')
    $('div').each((i, e) => e.style.pointerEvents = 'none')
    $(document).on('mousemove', e => resize(e));
    $(document).on('mouseup', e => stop(e));
  }

}
