'use_strict'

class Pane {
  constructor () {
    this.tabs = []

    this.parent = null

    this.dom          = $('<div class="pane"></div>')
    let tabswrapper   = $('<div class="tablinks-wrapper"></div>')
    this.dom.tabs     = $('<div class="tablinks"></div>')
    this.dom.content  = $('<div class="pane-content"></div>')
    tabswrapper.append(this.dom.tabs)
    this.dom.append(tabswrapper)
    this.dom.append(this.dom.content)

    this.activeTab = null

    // Event listeners
    this.dom.content.on('click', () => {
      this.setActive()
    })

    this.dom.on('drop', (evt) => {
      if (this.parent && this.parent.draggedTab) {
        let tab = this.parent.draggedTab
        this.parent.draggedTab = null
        if (tab.parent === this) return;
        tab.parent.remove(tab)
        let elem = $(document.elementFromPoint(evt.clientX, evt.clientY))
        if (!elem.hasClass('tablink')) elem = null
        this.add(tab, elem)
        tab.setActive()
        tab.addEventListener()
        tab.refresh()
      }
    })

    // Allows dragging over
    this.dom.on('dragover', (evt) => evt.preventDefault())
  }

  get firstTab () {
    return this.tabs[0]
  }

  prevTab (tab) {
    for (let i = 1; i < this.tabs.length; i++)
      if (this.tabs[i] === tab)
        return this.tabs[i-1]
    return null
  }

  add (tab, beforeThisTab) {
    // Push tab to array
    this.tabs.push(tab)

    if (beforeThisTab)
      beforeThisTab.before(tab.dom)
    else
      this.dom.tabs.append(tab.dom);

    // Attach UI
    this.dom.content.append(tab.dom.content)

    tab.parent = this
    tab.alive = true
    if (!this.activeTab)
      this.activeTab = tab

    tab.addEventListener()
    tab.refresh()

    return tab
  }

  remove (tab) {
    // If removing active tab, then activate previous one
    if (tab === this.activeTab) {
      let prev = this.prevTab(tab)
      if (prev)
        prev.setActive()
      else if (this.tabs.length > 0)
        this.firstTab.setActive()
    }

    if (tab.dom instanceof Element)
      this.dom.tabs.css(this.dom.tabs.css('min-width')-tab.dom.width())

    // Remove from UI
    tab.dom.remove()
    tab.dom.content.remove()

    // Tab is not alive anymore
    //tab.alive = false
    tab.parent = null

    // Remove from list of tabs
    for(let i = 0; i < this.tabs.length; i++) {
      if (this.tabs[i] === tab) {
        this.tabs.splice(i, 1)
      }
    }

    // Remove pane if this was the last tab
    if (this.tabs.length == 0)
      this.parent.remove(this)
  }

  setActive() {
    if (this.parent)
      this.parent.setActivePane(this)
    this.dom.addClass('active')
  }

  setInactive() {
    this.dom.removeClass('active')
  }

  setActiveTab(tab) {
    this.activeTab = tab
    this.setActive()
  }

  clearSelection() {
    if (this.activeTab)
      this.activeTab.clearSelection()
  }

  refresh () {
    if (this.activeTab)
      this.activeTab.refresh()
  }
}
