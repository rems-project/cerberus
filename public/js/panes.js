'use_strict'

class Pane {
  constructor () {
    this.tabs = []

    // UI
    this.parent = null

    this.dom = $('<div class="pane"></div>')
    this.tablinks = $('<div class="tablinks"></div>')
    this.content  = $('<div class="content"></div>')
    this.dom.append(this.tablinks)
    this.dom.append(this.content)

    //this.dom = $('#pane-template').clone().contents()

    //this.tabadder = this.dom.find('.tabadder')
    //this.tablinks = this.dom.find('.tablinks')
    //this.content =  this.dom.find('.content')
    this.activeTab = null

    // Event listeners
     /*
    this.tabadder.on('click', () => {
      let tab = new TabSource()
      this.addTab(tab)
      tab.setActive()
      this.setActive()
    })
    */

    this.content.on('click', () => {
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

  add (tab, beforeThisTab) {
    // Push tab to array
    this.tabs.push(tab)

    if (beforeThisTab)
      beforeThisTab.before(tab.tablink)
    else
      this.tablinks.append(tab.tablink);

      //this.tabadder.before(tab.tablink)

    // Attach UI
    this.content.append(tab.content)

    tab.parent = this
    tab.alive = true
    if (!this.activeTab)
      this.activeTab = tab

    tab.refresh()
  }

  remove (tab, doNotRemovePane) {
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
