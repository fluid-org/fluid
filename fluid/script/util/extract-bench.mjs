#!/usr/bin/env node
// Split a Karma run log into the benchmark tables it emitted. The suite runs in headless
// Chrome and so can only report via console.log; Test.Benchmark.Intermediate delimits each
// table with ==== BENCH BEGIN <name> ==== / ==== BENCH END <name> ====, and Karma wraps each
// console.log in LOG: '...'.
//
//    yarn test > run.log; node script/util/extract-bench.mjs run.log ../docs/reports

import { readFileSync, writeFileSync } from "node:fs"
import { join } from "node:path"

const [logPath, outDir] = process.argv.slice(2)
if (!logPath || !outDir) {
   console.error("usage: extract-bench.mjs <run.log> <out-dir>")
   process.exit(1)
}

const lines = readFileSync(logPath, "utf8").split("\n")
const begin = /==== BENCH BEGIN (\S+) ====/
const end = /==== BENCH END (\S+) ====/

let name = null
let block = []
let written = 0

for (const line of lines) {
   const opened = line.match(begin)
   const closed = line.match(end)
   if (opened) {
      name = opened[1]
      block = []
   } else if (closed && name === closed[1]) {
      // Karma quotes the whole (multi-line) log entry: unwrap the opening LOG: ' and closing '.
      block[0] = block[0]?.replace(/^LOG: '/, "")
      const last = block.length - 1
      block[last] = block[last]?.replace(/'$/, "")
      writeFileSync(join(outDir, name), block.join("\n") + "\n")
      console.log(`${name}: ${block.length} lines`)
      name = null
      written++
   } else if (name !== null) {
      block.push(line)
   }
}

if (written === 0) {
   console.error(`no BENCH blocks found in ${logPath}`)
   process.exit(1)
}
