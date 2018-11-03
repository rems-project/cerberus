import $ from 'jquery'
import * as util from './util'
import UI from './ui'

export namespace Widget {

export abstract class Widget {
  dom: JQuery<HTMLElement>
  body: JQuery<HTMLElement>
  constructor (title: string) {
    const cancel = $('<div class="menu-item btn">Cancel</div></li>')
    cancel.on('click', () => this.hide ())
    const headerContent = $('<ul class="menu x-fill">')
    headerContent.append($(`<li><div class="title">${title}</div></li>`))
    headerContent.append($('<li class="right">').append(cancel))
    const header = $('<div class="header">')
    header.append(headerContent)

    this.body = $('<div class="widget_body">')
    this.dom = $('<div class="widget invisible">')
    this.dom.append(header)
    this.dom.append(this.body)
    $(document.body).append(this.dom)
  }
  fetch_test(name: string) {
    util.get(name, (data: string) => {
      this.hide()
      UI.addView(name, data)
    })
  }
  show() {
    this.dom.removeClass('invisible')
  }
  hide() {
    this.dom.addClass('invisible')
  }
}

export class Defacto extends Widget {
  constructor () {
    super('Load defacto tests...')
    util.get('defacto_tests.json', (data: any) => {
      for (let i = 0; i < data.length; i++) {
        const questions = $('<div class="questions"></div>')
        for (let j = 0; j < data[i].questions.length; j++) {
          const q = data[i].questions[j]
          const tests = $('<ul class="tests"></ul>')
          for (let k = 0; q.tests && k < q.tests.length; k++) {
            const name = q.tests[k]
            const test = $('<li><a href="#">'+name+'</a></li>')
            test.on('click', () => this.fetch_test('defacto/'+name))
            tests.append(test)
          }
          questions.append(q.question)
          questions.append(tests)
        }
        this.body.append($('<h3>'+data[i].section+'</h3>'))
        this.body.append(questions)
      }
      this.show()
    })
  }
}

export class POPL19 extends Widget {
  constructor () {
    super('Load POPL 2019 pointer provenace tests...')
    util.get('popl19_tests.json', (data: any) => {
      for (let i = 0; i < data.length; i++) {
        const tests = $('<ul class="tests"></ul>')
        for (let k = 0; data[i].tests && k < data[i].tests.length; k++) {
          const name = data[i].tests[k]
          const experimental = $('<a href="#">experimental data</a>')
          experimental.on('click', () => {
            util.get('defacto/'+name, (data: string) => {
              this.hide()
              UI.addView(name, data)
              UI.openExperimentalTab()
            })
          })
          const link = $(`<a href="#">${name}</a>`)
          link.on('click', () => this.fetch_test('defacto/'+name))
          const test = $('<li>')
          test.append(link)
          test.append($('<br>'))
          test.append(experimental)
          tests.append(test)
        }
        this.body.append($('<h3>'+data[i].section+'</h3>'))
        this.body.append(tests)
      }
      this.show()
    })
  }
}


export class GCC2018 extends Widget {
  constructor() {
    super('Load GCC Cauldron 2018 demo tests...')
    this.body.append($(`
      <h3>GCC Tools Cauldron 2018</h3>
      <h4>Original versions</h2>
      <ul class="tests">
        <li><a href="#">demo1.c</a></li>
        <li><a href="#">provenance_basic_global_xy.c</a></li>
        <li><a href="#">provenance_roundtrip_via_intptr_t.c</a></li>
        <li><a href="#">pointer_offset_from_subtraction_1_global.c</a></li>
        <li><a href="#">provenance_tag_bits_via_uintptr_t_1.c</a></li>
        <li><a href="#">pointer_copy_user_dataflow_direct_bytewise.c</a></li>
        <li><a href="#">provenance_lost_escape_1.c</a></li>
        <li><a href="#">provenance_intra_object_1.c</a></li>
        <li><a href="#">cast_struct_and_first_member_2.c</a></li>
        <li><a href="#">unspecified_value_struct_copy.c</a></li>
        <li><a href="#">cheri_03_ii.c</a></li>
        <li><a href="#">pointer_comparison_eq_zombie_1.c</a></li>
      </ul>
      <h4>Simplified (no printf, memcpy, memcmp, ....)</h4>
      <ul class="tests">
        <li><a href="#">provenance_basic_global_xy_nolibc.c</a></li>
        <li><a href="#">provenance_roundtrip_via_intptr_t_nolibc.c</a></li>
        <li><a href="#">pointer_offset_from_subtraction_1_global_nolibc.c</a></li>
        <li><a href="#">provenance_tag_bits_via_uintptr_t_1_nolibc.c</a></li>
        <li><a href="#">provenance_lost_escape_1_nolibc.c</a></li>
        <li><a href="#">provenance_intra_object_1_nolibc.c</a></li>
        <li><a href="#">unspecified_value_struct_copy_nolibc.c</a></li>
        <li><a href="#">cheri_03_ii_nolibc.c</a></li>
      </ul>`))
    this.dom.find('.tests a').on('click', (e) => {
      const name = e.target.textContent as string
      this.fetch_test('demo/'+name)
    })
    this.show()
  }
}

}

export default Widget