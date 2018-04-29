//@ts-check
const puppeteer = require('puppeteer');
let browser, page

// Help functions

const click = async (sel) =>
  await page.$eval(sel, (e) => e.click())

const tabSelector = (tabName) => 'li[title="'+tabName+'"]'

const waitForTab = async (tabName) =>
  await page.waitForSelector(tabSelector(tabName))

const waitForRequest = async () => {
  await page.waitForFunction('document.body.classList.contains("wait") === true')
  await page.waitForFunction('document.body.classList.contains("wait") === false')
}

const closeTab = async (tabName) =>
  await page.$eval(tabSelector(tabName)+' > .lm_close_tab', (e) => e.click())

const tabValue = async (tabName) =>
  await page.evaluate('UI.getView().findTab("'+tabName+'").getValue()')

const predTab = async (tabName, pred, res) =>
  expect(await page.$eval(tabSelector(tabName), pred)).toBe(res)

const predTabs = async (tabName, pred, res) =>
  expect(await page.$$eval(tabSelector(tabName), pred)).toBe(res)

const hasTab = (tabName, n) =>
  predTabs(tabName, es => es.length, n)

// Start

beforeAll(async () => {
  browser = await puppeteer.launch({headless: true /*, slowMo: 10 */})
  page = await browser.newPage()
  page.on('requestfailed', request => {
    console.log(request.url() + ' ' + request.failure().errorText);
  }); 
  await Promise.all([ // Enable both JavaScript and CSS coverage
    page.coverage.startJSCoverage(),
    page.coverage.startCSSCoverage()
  ]);
  await page.goto('http://localhost:8080')
  await waitForTab('example.c')
  await page.waitForSelector('.color1') // example has been colorised

})
// Check opening tests

it('check initial tabs', async () => {
  await hasTab('Console', 1)
  await hasTab('Execution', 1)
  await hasTab('Core', 1)
})

it('open cabs tab', async () => {
  await click('#cabs')
  await hasTab('Cabs', 1)
})

it('open ail tab', async () => {
  await click('#ail')
  await hasTab('Ail', 1)
})

it('open ail ast tab', async () => {
  await click('#ail-ast')
  await hasTab('Ail_AST', 1)
})

it('close core tab', async() => {
  await closeTab('Core')
  await hasTab('Core', 0)
})

it('open core tab', async () => {
  await click('#core')
  await hasTab('Core', 1)
})

it('open compile', async () => {
  await click('#compile')
  await hasTab('Asm', 1)
})

// Check execution

const resultExhaustive =
`BEGIN EXEC[0-0]
Defined {value: "Specified(0)", stdout: "", blocked: "false"}
END EXEC[0-0]
BEGIN EXEC[1-1]
Defined {value: "Specified(42)", stdout: "", blocked: "false"}
END EXEC[1-1]
`

it('run random', async () => {
  await predTab('Execution', e => e.classList.contains('lm_active'), false)
  await click('#random')
  await waitForRequest()
  await predTab('Execution', e => e.classList.contains('lm_active'), true)
  expect(await tabValue('Execution')).toMatch(/Specified/)
})

it('run exhaustive', async () => {
  await click('#exhaustive')
  await waitForRequest()
  expect(await tabValue('Execution')).toBe(resultExhaustive)
})

// Check error (console)

it('error console', async () => {
  expect(await tabValue('Console')).toBe('')
  await page.focus('textarea')
  await page.keyboard.type('something')
  await waitForRequest()
  expect(await tabValue('Console')).not.toBe('')
  expect(await tabValue('Cabs')).toBe('')
  expect(await tabValue('Ail')).toBe('')
  expect(await tabValue('Ail_AST')).toBe('')
  expect(await tabValue('Execution')).toBe('')
  //expect(await tabValue('Asm')).toBe('') // needs to wait for Godlbolt
})

// Clean

it('close tabs', async () => {
  await closeTab('Cabs')
  await closeTab('Ail')
  await closeTab('Ail_AST')
  await closeTab('Asm')
  expect(await page.$$eval('.lm_tab', es => es.length)).toBe(5)
})

afterAll(async () => {
  const pti = require('puppeteer-to-istanbul')
  // Disable both JavaScript and CSS coverage
  const [jsCoverage, cssCoverage] = await Promise.all([
    page.coverage.stopJSCoverage(),
    page.coverage.stopCSSCoverage(),
  ]);
  const coverage = [...jsCoverage, ...cssCoverage];
  pti.write(jsCoverage)
  for (const entry of coverage) {
    let usedBytes = 0
    for (const range of entry.ranges)
      usedBytes += range.end - range.start - 1
    console.log(`${entry.url} : ${(usedBytes / entry.text.length * 100).toFixed(2)}%`)
  }
  await page.screenshot({path: 'end_result.png'})
  await browser.close()
})


