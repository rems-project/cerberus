'use_strict'

class Pane {
  constructor (div) {
    this.tabs = []

    // UI
    this.parent = null
    this.div = $('#pane-template').clone().contents()

    this.tabadder = this.div.find('.tabadder')
    this.tablinks = this.div.find('.tablinks')
    this.content = this.div.find('.content')
    this.activeTab = null

    // Event listeners
    this.tabadder.on('click', () => {
      let tab = new TabSource()
      this.addTab(tab)
      tab.setActive()
      this.setActive()
    })

    this.content.on('click', () => {
      this.setActive()
    })

    this.div.on('drop', (evt) => {
      if (this.parent && this.parent.draggedTab) {
        let tab = this.parent.draggedTab
        this.parent.draggedTab = null
        if (tab.parent === this) return;
        tab.parent.removeTab(tab)
        let elem = $(document.elementFromPoint(evt.clientX, evt.clientY))
        if (!elem.hasClass('tablink')) elem = null
        this.addTab(tab, elem)
        tab.setActive()
        tab.addEventListener()
        tab.refresh()
      }
    })

    this.tablinks.on('dragover', (evt) => {
      // Allows dropping over tablinks
      evt.preventDefault()
    })

    this.tablinks.on('drop', (evt) => {

    })
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

  addTab (tab, beforeThisTab) {
    // Push tab to array
    this.tabs.push(tab)

    if (beforeThisTab)
      beforeThisTab.before(tab.tablink)
    else
      this.tabadder.before(tab.tablink)

    // Attach UI
    this.content.append(tab.content)

    tab.parent = this
    tab.alive = true
    if (!this.activeTab)
      this.activeTab = tab

    tab.refresh()
  }

  removeTab (tab, doNotRemovePane) {
    // If removing active tab, then activate previous one
    if (tab === this.activeTab) {
      let prev = this.prevTab(tab)
      if (prev)
        prev.setActive()
      else if (this.tabs.length > 0)
        this.firstTab.setActive()
    }

    // Remove from UI
    tab.tablink.remove()
    tab.content.remove()

    // Tab is not alive anymore
    tab.alive = false

    // Remove from list of tabs
    for(let i = 0; i < this.tabs.length; i++) {
      if (this.tabs[i] === tab) {
        this.tabs.splice(i, 1)
      }
    }

    // Remove pane if this was the last tab
    if (this.tabs.length == 0 && !doNotRemovePane)
      this.parent.removePane(this)
  }

  setActive() {
    if (this.parent)
      this.parent.setActivePane(this)
    this.div.addClass('active')
  }

  setInactive() {
    this.div.removeClass('active')
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
