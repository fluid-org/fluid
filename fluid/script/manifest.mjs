#!/usr/bin/env node
// Write manifest.json into every directory under the given paths with .fld files beneath it, listing those
// files relative to the directory.
import { readdirSync, statSync, writeFileSync } from "node:fs";
import { join, relative } from "node:path";

function fldFiles(dir) {
   return readdirSync(dir, { withFileTypes: true }).flatMap((entry) => {
      const path = join(dir, entry.name);
      const stats = entry.isSymbolicLink() ? statSync(path) : entry;
      if (stats.isDirectory()) return fldFiles(path);
      return entry.name.endsWith(".fld") ? [path] : [];
   });
}

function subdirectories(dir) {
   return readdirSync(dir, { withFileTypes: true }).flatMap((entry) => {
      const path = join(dir, entry.name);
      const stats = entry.isSymbolicLink() ? statSync(path) : entry;
      return stats.isDirectory() ? [path, ...subdirectories(path)] : [];
   });
}

for (const root of process.argv.slice(2)) {
   for (const dir of [root, ...subdirectories(root)]) {
      const files = fldFiles(dir).map((path) => relative(dir, path)).sort();
      if (files.length > 0) writeFileSync(join(dir, "manifest.json"), JSON.stringify(files, null, 2) + "\n");
   }
}
