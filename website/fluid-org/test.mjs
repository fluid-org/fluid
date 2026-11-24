import {
   checkAlignment, checkCount, checkWidthApprox, getBoundingBox,
   testMobile, testURL, waitFor
} from "@fluid-org/fluid/script/webtest-lib.mjs"

function testOutcome(pass, msg) {
   const sym = pass ? "\x1b[32m ✔\x1b[0m" : "\x1b[31m ✖\x1b[0m"
   console.log(`${sym} ${msg}`)
   if (!pass) throw new Error("Test failed")
}

async function checkHeaderAlignment(page) {
   await waitFor(page, ".site-header")
   await waitFor(page, ".grid-container")
   await checkAlignment(page, ".header-nav", ".grid-container .flex-left-align", "left")
}

async function checkWithinViewport(page, selector) {
   const box = await getBoundingBox(page, selector)
   const viewport = await page.evaluate(() => ({ width: window.innerWidth }))
   const pass = box.right <= viewport.width + 5 && box.left >= -5
   testOutcome(pass, `${selector}: within viewport${pass ? "" : ` (left=${Math.round(box.left)}, right=${Math.round(box.right)}, viewport=${viewport.width})`}`)
}

async function checkVerticalStack(page, selector) {
   const boxes = await page.$$eval(selector, els =>
      els.map(el => {
         const r = el.getBoundingClientRect()
         return { top: r.top, bottom: r.bottom }
      })
   )
   let pass = true
   for (let i = 1; i < boxes.length; i++) {
      if (boxes[i].top < boxes[i - 1].bottom - 1) {
         pass = false
         break
      }
   }
   testOutcome(pass, `${selector}: vertically stacked (${boxes.length} items)`)
}

export const main = async () => {
   // Desktop
   await testURL("", [
      async page => {
         await checkHeaderAlignment(page)
         await waitFor(page, "h3.title")
         await checkWidthApprox(page, ".grid-container .flex-left-align", 800)
         await waitFor(page, ".code-examples .cm-editor")
         await checkCount(page, ".code-examples .cm-editor", 5)
      }
   ])

   // Mobile
   await testMobile("", [
      async page => {
         await checkHeaderAlignment(page)
         await checkWithinViewport(page, ".header-logo")
         await checkVerticalStack(page, ".header-nav nav ul li")
      }
   ])

   await testURL("faq", [
      async page => await waitFor(page, ".grid-container")
   ])

   await testURL("research", [
      async page => await waitFor(page, ".grid-container")
   ])

   await testURL("supporters", [
      async page => await waitFor(page, ".grid-container")
   ])
}
