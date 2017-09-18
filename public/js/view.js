'use_strict'

class View {
  constructor (title, data) {
    // Dom
    this.panes = []
    this.dom = $('<div class="view"></div>')
    this.draggedTab = null

    // Create source tab
    this.title  = title
    this.source = new TabSource(title, data)

    // Create an active pane
    this.activePane = new Pane()
    this.activePane.add(this.source)
    this.add(this.activePane)

    // Activate source tab
    this.source.setActive()
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
    return this.panes[0]
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
    // Last pane, don't remove it, add a blank tab instead
    if (this.panes.length == 1) {
      let tab = new TabSource()
      pane.add(tab)
      tab.setActive()
      this.setup()
      return
    }

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

  get exec() {
    if (this._execTab && this._execTab.alive)
      return this._execTab
    this._execTab = new TabReadOnly(this.title + ' [exec]')
    this.secondaryPane.add(this._execTab)
    return this._execTab;
  }

  get cabs() {
    if (this._cabsTab && this._cabsTab.alive)
      return this._cabsTab
    this._cabsTab = new TabCore(this.title + ' [cabs]')
    this.secondaryPane.add(this._cabsTab)
    return this._cabsTab;
  }

  get ail() {
    if (this._ailTab && this._ailTab.alive)
      return this._ailTab
    this._ailTab = new TabCore(this.title + ' [ail]')
    this.secondaryPane.add(this._ailTab)
    return this._ailTab;
  }

  get core() {
    if (this._coreTab && this._coreTab.alive)
      return this._coreTab
    this._coreTab = new TabCore(this.title + ' [core]')
    this.secondaryPane.add(this._coreTab)
    return this._coreTab;
  }

  get console() {
    if (this._consoleTab && this._consoleTab.alive)
      return this._consoleTab
    if (!ui) return null;
    this._consoleTab = new TabReadOnly(this.title + ' [console]')
    this.secondaryPane.add(this._consoleTab)
    return this._consoleTab;
  }

  get graph() {
    if (this._graphTab && this._graphTab.alive)
      return this._graphTab
    this._graphTab = new TabGraph(this.title + ' [graph]')
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
      this.firstPane.add(tab);
      tab.setActive()
      tab.addEventListener()
      tab.refresh()
    }
  }

  show() {
    this.dom.show()
  }

  hide() {
    this.dom.hide()
  }

  refresh () {
    // TODO: this should redimension the panes according to a new
    // width
    console.warn('TODO: redinemension pane')
    return;
    let factor = window.innerWidth / window.prevWidth
    for (let i = 0; i < this.panes.length; i++) {
      let w = parseFloat(this.panes[i].dom.siblings()[0].style.width.slice(0, -2))
      this.panes[i].dom.siblings()[0].style.width = (w * factor)+'px'
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
