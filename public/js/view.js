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

    // Empty data
    this.data = {
      cabs: "",
      ail:  "",
      core: "",
      locs: [],
      stdout: "",
      stderr: ""
    }

    this.content = {}

    this.isHighlighted = false;
    this.dirty = true;
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

  get newPane () {
    let pane = new Pane()
    this.add(pane)
    return pane
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
      this.newPane.add(this.source)
    return this.source;
  }

  get exec() {
    if (!this._execTab)
      this._execTab = new TabReadOnly('Execution')
    if (!this._execTab.parent)
      this.newPane.add(this._execTab)
    return this._execTab
  }

  get cabs() {
    let tab = new TabCabs()
    this.newPane.add(tab)
    return tab
  }

  get ail() {
    let tab = new TabAil()
    this.newPane.add(tab)
    return tab
  }

  get core() {
    let tab = new TabCore()
    this.newPane.add(tab)
    return tab
  }

  get console() {
    if (!this._consoleTab)
      this._consoleTab = new TabReadOnly('Console')
    if (!this._consoleTab.parent)
      this.newPane.add(this._consoleTab)
    return this._consoleTab;
  }

  get graph() {
    if (!this._graphTab)
      this._graphTab = new TabGraph('Graph')
    if (!this._graphTab.parent)
      this.newPane.add(this._graphTab)
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

  forEachTab(f) {
    for (let i = 0; i < this.panes.length; i++)
      for (let j = 0; j < this.panes[i].tabs.length; j++)
        f(this.panes[i].tabs[j])
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
    this.dirty = false
    this.isHighlighted = false
    this.data = data
    this.forEachTab((tab) => tab.update())
    this.isHighlighted = false
  }

  newTab(mode) {
    let tab = this[mode];
    tab.setValue(this.data[mode])
    tab.highlight()
  }


  refresh () {
    let factor = window.innerWidth / window.prevWidth
    for (let i = 0; i < this.panes.length; i++) {
      let w = parseFloat(this.panes[i].dom[0].style.width.slice(0, -2))
      this.panes[i].dom[0].style.width = (w * factor)+'px'
      this.panes[i].refresh();
    }
    window.prevWidth = window.innerWidth
  }

/*
  onresize (evt) {
    let x0 = evt.clientX
    let sep = $(evt.currentTarget)
    let prevPanes = sep.prevAll('.pane')
    let prevPanesWidth = []
    for (let i = 0; i < prevPanes.length; i++)
      prevPanesWidth.push(parseInt(prevPanes[i].style.width.slice(0, -2)))
    let nextPanes = sep.nextAll('.pane')
    let nextPanesWidth = []
    for (let i = 0; i < nextPanes.length; i++)
      nextPanesWidth.push(parseInt(nextPanes[i].style.width.slice(0, -2)))
    let minX = 60;
    let maxX = window.innerWidth-60;

    function resize (evt) {
      if (minX < evt.clientX && evt.clientX < maxX) {
        let xn = x0;
        for (let i = 0; i < prevPanes.length; i++) {
          let delta = evt.clientX - xn;
          if (prevPanesWidth[i]+delta >= 60) {
            prevPanes[i].style.width = (prevPanesWidth[i]+delta)+'px'
            break;
          } else {
            prevPanes[i].style.width = '60px'
            xn -= (prevPanesWidth[i]-60+3)
          }
        }
        xn = x0;
        for (let i = 0; i < nextPanes.length; i++) {
          console.log("pane " + i + ": " + nextPanes[i].style.width);
          let delta = evt.clientX - xn;
          if (nextPanesWidth[i]-delta >= 60) {
            nextPanes[i].style.width = (nextPanesWidth[i]-delta)+'px'
            break;
          } else {
            nextPanes[i].style.width = '60px'
            xn += 63;
          }
          console.log("delta: " + delta)
          console.log("after pane " + i + ": " + nextPanes[i].style.width);
        }
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
*/

  onresize (evt) {
    let x0 = evt.clientX
    let sep = $(evt.currentTarget)
    let pane = sep.prev()
    let paneWidth = pane.width()
    let nextPane = sep.next()
    let nextPaneWidth = nextPane.width()
    let minX = pane.position().left + 60
    let maxX = nextPane.position().left + nextPaneWidth - 60

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
