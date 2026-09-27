import {
   checkAttribute, checkAttributeContains, checkComputedStyle, checkCount, checkCountAtLeast,
   checkTextContent, click, clickToggle, dispatchMouseDown, testURL, waitFor
} from "@fluid-org/fluid/script/webtest-lib.mjs"

export const main = async () => {
   // Convolution: 5×5 output matrix
   const rows = 5, cols = 5
   await testURL("convolution", [
      async page => {
         await waitFor(page, "svg#fig-output")
         await checkCount(page, "#fig-output .matrix-cell", rows * cols)
         await checkCount(page, "#fig-output .matrix-cell-text", rows * cols)
         await checkCount(page, "#fig-output .matrix-cell-hBorder", (rows + 1) * cols)
         await checkCount(page, "#fig-output .matrix-cell-vBorder", rows * (cols + 1))
         await waitFor(page, "#fig-output .title-text")

         const cell = "#fig-output .matrix-cell"
         await checkCount(page, "#fig-output .matrix-cell[class*='selected']", 0)
         await page.hover(cell)
         await checkAttributeContains(page, cell, "class", "selected-primary-transient")
         await click(page, cell)
         await checkAttributeContains(page, cell, "class", "selected-primary-persistent")
      },
      async page => {
         await waitFor(page, "svg#fig-output")
         await clickToggle(page)
         await waitFor(page, "#fig-input .matrix-cell")
         await checkCount(page, "#fig-input .matrix-cell[class*='selected']", 0)
         await dispatchMouseDown(page, "#fig-output .matrix-cell")
         await checkCountAtLeast(page, "#fig-input .matrix-cell.selected-primary-persistent", 1)
      }
   ])

   await testURL("energy-scatter", [
      async page => {
         await waitFor(page, "svg")
         const point = "#fig .scatterplot-point"
         await waitFor(page, point)
         await checkCount(page, point, 10)
         await checkAttribute(page, point, "r", "2.0")
         await waitFor(page, "#fig .title-text")
      },
      async page => {
         await waitFor(page, "svg")
         await clickToggle(page)

         const point = "#fig .scatterplot-point"
         await waitFor(page, point)
         await checkCount(page, "#fig .scatterplot-point[class*='selected']", 0)
         await page.hover(point)
         await checkAttributeContains(page, point, "class", "selected-primary-transient")
         await click(page, point)
         await checkAttributeContains(page, point, "class", "selected-primary-persistent")
         await checkAttribute(page, point, "r", "3.2")

         const caption = "div#fig-input-renewables > div.table-caption"
         await checkTextContent(page, caption, "renewables (40 of 240 × 5 of 5)")
      },
      async page => {
         await waitFor(page, "svg")
         const point = "#fig .scatterplot-point"
         await waitFor(page, point)
         await dispatchMouseDown(page, point, 2)
         await checkCount(page, "#fig .scatterplot-point.selected-primary-persistent", 0)
      }
   ])

   await testURL("methane", [
      async page => await waitFor(page, "#fig svg:nth-of-type(1)")
   ])

   await testURL("moving-average", [
      async page => await waitFor(page, "#fig .linechart-point")
   ])

   await testURL("non-renewables", [
      async page => await waitFor(page, "#fig-output > svg:nth-of-type(1)"),
      async page => await waitFor(page, "#fig-output > svg:nth-of-type(2)"),
   ])

   await testURL("renewables-linked", [
      async page => {
         const barChart = "#fig-output > :nth-child(1)"
         const lineChart = "#fig-output > :nth-child(2)"

         await waitFor(page, barChart)
         await waitFor(page, lineChart)
         await waitFor(page, `${lineChart} g.x-axis`)

         const point = `${lineChart} circle.linechart-point`
         await waitFor(page, point)
         await checkAttribute(page, point, "r", "2.0")

         await clickToggle(page)

         const bar = `${barChart} rect.bar`
         await waitFor(page, bar)
         await click(page, bar)
         await checkAttribute(page, bar, "fill", "#57a157")

         const selectedCell = "#fig-input .table-cell.selected-primary-persistent"
         await waitFor(page, selectedCell)
         await checkComputedStyle(page, selectedCell, "backgroundColor", "rgb(147, 233, 190)")
      }
   ])

   await testURL("scigen-1805.02474v1-10", [
      async page => await waitFor(page, "div#fig-output")
   ])
}
