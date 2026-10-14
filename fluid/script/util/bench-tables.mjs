#!/usr/bin/env node
// Turn a benchmark CSV (as emitted by Test.Benchmark.Intermediate, one row per fixture, paired
// columns X and X<suffix>) into LaTeX for a report. Two shapes:
//
//   default   one narrow table per metric: example, each arm, ratio
//   --grouped a single table, metrics grouped under each arm, means +- standard error
//
//    node script/util/bench-tables.mjs ../docs/reports/intermediate-contracted.csv \
//         ../docs/reports/intermediate-contracted-tables.tex Uncontracted Contracted contracted
//
//    node script/util/bench-tables.mjs ../docs/reports/intermediate-doc.csv \
//         ../docs/reports/intermediate-doc-table.tex '\texttt{@doc}' Stripped doc \
//         --grouped --metrics Eval,Demands,Suffices --runs 10

import { readFileSync, writeFileSync } from "node:fs"

const argv = process.argv.slice(2)
const flag = name => {
   const i = argv.indexOf(name)
   return i < 0 ? null : argv[i + 1]
}
const positional = argv.filter((a, i) => !a.startsWith("--") && !(i > 0 && argv[i - 1].startsWith("--")))

const [csvPath, outPath, lhs, rhs, tag] = positional
const grouped = argv.includes("--grouped")
const chosen = (flag("--metrics") ?? "").split(",").filter(m => m !== "")
const runs = flag("--runs")

if (!csvPath || !outPath || !lhs || !rhs || !tag) {
   console.error("usage: bench-tables.mjs <csv> <out.tex> <lhs-label> <rhs-label> <label-tag>" +
      " [--grouped] [--metrics A,B,C] [--runs N]")
   process.exit(1)
}

const lines = readFileSync(csvPath, "utf8").split("\n").map(l => l.trim()).filter(l => l !== "")
const header = lines[0].split(",")
const dataRows = lines.slice(1)

// The suffix is whatever non-ASCII character distinguishes the second arm's columns.
const suffix = (header.find(c => /[^\x00-\x7F]/.test(c)) ?? "").slice(-1)
if (!suffix) {
   console.error(`no paired columns found in ${csvPath}`)
   process.exit(1)
}

const metric = base => base.replace(/^G-/, "")
const slug = base => metric(base).toLowerCase().replace(/[^a-z0-9]+/g, "-")
const unit = base => (base.includes("Nodes") ? "vertices" : "ms")
const plain = s => s.replace(/\\texttt\{|\}/g, "")

const paired = header.filter(c => !c.includes(suffix) && header.includes(c + suffix))
const bases = chosen.length === 0
   ? paired
   : chosen.map(m => paired.find(b => metric(b) === m)).filter(b => b !== undefined)
if (bases.length === 0) {
   console.error(`none of the requested metrics found in ${csvPath}`)
   process.exit(1)
}

// Cells look like "(212.93333 : 10.60296 : Nil)": the mean, then the standard error.
const stats = cell => {
   const ns = (cell ?? "").match(/-?\d+(?:\.\d+)?/g) ?? []
   return { mean: Number(ns[0] ?? 0), err: Number(ns[1] ?? 0) }
}

const rows = dataRows.map(line => {
   const cells = line.split(",")
   const byName = Object.fromEntries(header.map((h, i) => [h, cells[i]]))
   return { name: cells[0], stats: base => stats(byName[base]) }
})

// slicing/intermediates/edge_detect.fld -> \texttt{edge\_detect}
const example = name =>
   "\\texttt{" + name.replace(/^.*\//, "").replace(/\.fld$/, "").replace(/_/g, "\\_") + "}"

const ratio = (a, b) => (b === 0 ? "--" : (a / b).toFixed(3))

// Counts print as integers, timings to one decimal place.
const formatter = base => {
   const vs = rows.flatMap(r => [r.stats(base).mean, r.stats(base + suffix).mean])
   return vs.every(v => Number.isInteger(v)) ? (v => String(v)) : (v => v.toFixed(1))
}

// "212.9 \pm 10.6", keeping a significant digit on errors that would round away to 0.0.
const withError = (base, { mean, err }) =>
   `$${formatter(base)(mean)} \\pm ${err.toFixed(err < 0.1 ? 2 : 1)}$`

const wrap = (body, cols, caption, label) =>
   [
      "\\begin{table}[htbp]",
      "\\centering",
      "\\small",
      `\\begin{tabular}{l ${"r ".repeat(cols).trim()}}`,
      "\\toprule",
      ...body,
      "\\bottomrule",
      "\\end{tabular}",
      `\\caption{${caption}}`,
      `\\label{tab:${label}}`,
      "\\end{table}",
   ].join("\n")

// One table per metric.
const perMetric = base => {
   const fmt = formatter(base)
   const body = rows.map(r => {
      const a = r.stats(base).mean
      const b = r.stats(base + suffix).mean
      return `${example(r.name)} & ${fmt(a)} & ${fmt(b)} & ${ratio(a, b)} \\\\`
   })
   return wrap(
      [`Example & ${lhs} & ${rhs} & Ratio \\\\`, "\\midrule", ...body],
      3,
      `\\texttt{${metric(base)}} (${unit(base)}), ${plain(lhs)} vs ${plain(rhs)}. ` +
      `Ratio is ${plain(lhs)} / ${plain(rhs)}.`,
      `${tag}-${slug(base)}`,
   )
}

// The three tables the ESOP paper's presentation calls for: one per phase, each metric
// contributing an (uncontracted, contracted, ratio) triple. Eval reports a slowdown
// (contracted / uncontracted), the slicing phases a speedup (uncontracted / contracted).
const esopTables = () => {
   const find = m => paired.find(b => metric(b) === m)

   const phase = ({ metrics, ratioHead, invert, caption, label }) => {
      const bs = metrics.map(find).filter(b => b !== undefined)
      if (bs.length === 0) return null
      const many = bs.length > 1

      const heads = many
         ? [
            " & " + bs.map(b => `\\multicolumn{3}{c}{\\texttt{${metric(b)}}}`).join(" & ") + " \\\\",
            bs.map((_, i) => `\\cmidrule(lr){${2 + i * 3}-${4 + i * 3}}`).join(" "),
            "Example & " + bs.map(() => `${lhs} & ${rhs} & ${ratioHead}`).join(" & ") + " \\\\",
         ]
         : [`Example & ${lhs} & ${rhs} & ${ratioHead} \\\\`]

      const body = rows.map(r => {
         const cells = bs.flatMap(b => {
            const a = r.stats(b)
            const c = r.stats(b + suffix)
            return [withError(b, a), withError(b, c), invert ? ratio(c.mean, a.mean) : ratio(a.mean, c.mean)]
         })
         return [example(r.name), ...cells].join(" & ") + " \\\\"
      })

      return wrap([...heads, "\\midrule", ...body], bs.length * 3, caption, `${tag}-${label}`)
   }

   const over = runs ? `over ${runs} runs` : "over the benchmark's runs"
   return [
      phase({
         metrics: ["Eval"],
         ratioHead: "Slowdown",
         invert: true,
         caption: `Evaluation time (ms), ${over}. Slowdown is ${plain(rhs)} / ${plain(lhs)}: ` +
            `contraction does extra bookkeeping at every retained allocation.`,
         label: "eval",
      }),
      phase({
         metrics: ["Demands"],
         ratioHead: "Speedup",
         invert: false,
         caption: `Backward slicing time (ms), ${over}. Speedup is ${plain(lhs)} / ${plain(rhs)}.`,
         label: "demands",
      }),
      phase({
         metrics: ["DemBy-Dir", "DemBy-Suff"],
         ratioHead: "Speedup",
         invert: false,
         caption: `Demanded-by time (ms), ${over}, computed directly and as the dual of ` +
            `sufficiency. Speedup is ${plain(lhs)} / ${plain(rhs)}.`,
         label: "demby",
      }),
   ].filter(t => t !== null).join("\n\n")
}

// All metrics in one table, grouped under each arm, in the style of the paper's tables.
const groupedTable = () => {
   const n = bases.length
   const group = (label, from) =>
      `\\multicolumn{${n}}{c}{${label}}`
   const cmidrules = [0, 1, 2]
      .map(g => `\\cmidrule(lr){${2 + g * n}-${1 + (g + 1) * n}}`)
      .join(" ")
   const subHeads = arm =>
      bases.map(b => `{${metric(b)}${arm ? ` (${unit(b)})` : ""}}`).join(" & ")

   const cell = (r, base, arm) => withError(base, r.stats(arm ? base : base + suffix))

   const body = rows.map(r => {
      const withArm = bases.map(b => cell(r, b, true))
      const without = bases.map(b => cell(r, b, false))
      const ratios = bases.map(b => ratio(r.stats(b).mean, r.stats(b + suffix).mean))
      return [example(r.name), ...withArm, ...without, ...ratios].join(" & ") + " \\\\"
   })

   return wrap(
      [
         ` & ${group(lhs)} & ${group(rhs)} & ${group(`Ratio (${plain(lhs)} / ${plain(rhs)})`)} \\\\`,
         cmidrules,
         `Example & ${subHeads(true)} & ${subHeads(true)} & ${subHeads(false)} \\\\`,
         "\\midrule",
         ...body,
      ],
      n * 3,
      `Slicing performance with and without \\texttt{@doc}-annotated intermediate values. ` +
      `Each figure is a mean $\\pm$ standard error over ${runs ?? "the benchmark's"} runs. ` +
      `Ratio $> 1$ means the annotated version is slower.`,
      `${tag}-summary`,
   )
}

const out = argv.includes("--esop")
   ? esopTables()
   : grouped
      ? groupedTable()
      : bases.map(perMetric).join("\n\n")
writeFileSync(outPath, out + "\n")
console.log(`${outPath}: ${(out.match(/\\begin\{table\}/g) ?? []).length} table(s)`)
