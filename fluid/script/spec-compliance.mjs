#!/usr/bin/env node
// Run the pure-py-spec corpus under `fluid check` and compare each verdict with the spec's. Cases whose verdicts
// differ must be listed in DIFFERENCES; an unlisted or stale difference fails the run. Usage:
//   node script/spec-compliance.mjs [--update]
// --update rewrites DIFFERENCES from this run.

import { execFileSync, spawn } from "node:child_process"
import { existsSync, mkdirSync, readdirSync, readFileSync, rmSync, writeFileSync, cpSync } from "node:fs"
import { join, relative, dirname, basename } from "node:path"

const TAG = "v0.18.0"
const REPO = "https://github.com/pure-py/pure-py-spec.git"
const SPEC = ".spec/pure-py-spec"
const CORPUS = ".spec/corpus"
const DIFFERENCES = "test/spec-differences.txt"
const FLUID = "dist/fluid/shared/fluid.mjs"
const LIB = "lib"
const CONCURRENCY = 8

// Exit code of `fluid check` expected for each verdict and stage of the corpus; null for cases not run.
const EXPECTED = {
   "semantically-valid": 0,
   "semantically-valid/pending": null,
   "excluded/syntactic": 1,
   "excluded/static": 3,
   "excluded/dynamic": 0,
   "python-error/syntactic": 1,
   "python-error/static": 3,
   "python-error/dynamic": 5,
   "python-error/syntactic-only": null,
}

const checkout = () => {
   if (!existsSync(SPEC) || execFileSync("git", ["-C", SPEC, "describe", "--tags"]).toString().trim() !== TAG) {
      rmSync(SPEC, { recursive: true, force: true })
      mkdirSync(dirname(SPEC), { recursive: true })
      execFileSync("git", ["clone", "--quiet", "--depth", "1", "--branch", TAG, REPO, SPEC], { stdio: "inherit" })
   }
}

// Copy of the corpus with .py files renamed .fld, a package pkg/__init__.py becoming pkg.fld.
const materialise = () => {
   rmSync(CORPUS, { recursive: true, force: true })
   const copy = (dir) => {
      for (const entry of readdirSync(dir, { withFileTypes: true })) {
         const src = join(dir, entry.name)
         if (entry.isDirectory()) {
            if (entry.name !== "__pycache__") copy(src)
         } else if (entry.name.endsWith(".py")) {
            const rel = relative(join(SPEC, "test"), src)
            const dest = join(CORPUS, entry.name === "__init__.py" ? dirname(rel) + ".fld" : rel.replace(/\.py$/, ".fld"))
            mkdirSync(dirname(dest), { recursive: true })
            cpSync(src, dest)
         }
      }
   }
   copy(join(SPEC, "test"))
}

// Cases as { name, root, file, expected }: a module-level case is a file checked with its directory as root, a
// program-level case is main.py checked with the case directory as root.
const cases = () => {
   const result = []
   for (const tier of ["module-level", "program-level"]) {
      const walk = (dir) => {
         for (const entry of readdirSync(dir, { withFileTypes: true })) {
            const path = join(dir, entry.name)
            if (entry.isDirectory()) {
               if (entry.name === "helpers" || entry.name === "__pycache__") continue
               if (tier === "program-level" && existsSync(join(path, "main.py"))) add(path, "main.py")
               else walk(path)
            } else if (tier === "module-level" && entry.name.endsWith(".py")) add(dir, entry.name)
         }
      }
      const add = (dir, file) => {
         const rel = relative(join(SPEC, "test", tier), dir).split("/")
         const stage = rel.length > 1 && rel[1] in STAGES ? rel[0] + "/" + rel[1] : rel[0]
         if (!(stage in EXPECTED)) throw new Error("unknown verdict " + stage + " for " + dir)
         const expected = EXPECTED[stage]
         if (expected === null) return
         const name = relative(join(SPEC, "test"), join(dir, file))
         const root = join(CORPUS, relative(join(SPEC, "test"), dir))
         result.push({ name, root, file: file.replace(/\.py$/, ".fld"), expected })
      }
      walk(join(SPEC, "test", tier))
   }
   return result
}
const STAGES = { syntactic: 1, static: 1, dynamic: 1, "syntactic-only": 1, pending: 1 }

const check = ({ root, file }) =>
   new Promise((resolve) => {
      const proc = spawn("node", [FLUID, "check", "--module", "-p", LIB, "-p", root, "-f", file])
      let output = ""
      proc.stdout.on("data", (d) => (output += d))
      proc.stderr.on("data", (d) => (output += d))
      proc.on("close", (code) => resolve({ code, output: output.split("\n")[0] }))
   })

const main = async () => {
   checkout()
   materialise()
   const all = cases()
   const differences = []
   let next = 0
   const worker = async () => {
      while (next < all.length) {
         const c = all[next++]
         const { code, output } = await check(c)
         if (code !== c.expected) differences.push(`${c.name}: exit ${code}, expected ${c.expected}; ${output}`)
      }
   }
   await Promise.all(Array.from({ length: CONCURRENCY }, worker))
   differences.sort()
   const actual = differences.join("\n") + (differences.length ? "\n" : "")
   if (process.argv.includes("--update")) {
      writeFileSync(DIFFERENCES, actual)
      console.log(`${all.length} cases, ${differences.length} differences written to ${DIFFERENCES}`)
      return
   }
   const known = existsSync(DIFFERENCES) ? readFileSync(DIFFERENCES, "utf8") : ""
   if (actual === known) {
      console.log(`${all.length} cases, ${differences.length} known differences`)
      return
   }
   const knownLines = new Set(known.split("\n").filter(Boolean))
   const actualLines = new Set(differences)
   for (const line of differences) if (!knownLines.has(line)) console.log("new: " + line)
   for (const line of knownLines) if (!actualLines.has(line)) console.log("gone: " + line)
   console.log(`${DIFFERENCES} out of date; rerun with --update`)
   process.exit(1)
}

main()
