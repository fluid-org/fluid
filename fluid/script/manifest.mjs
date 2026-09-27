#!/usr/bin/env node
// Write <root>/manifest.json listing the .fld files under each given source root, relative to the root.
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

for (const root of process.argv.slice(2)) {
   const files = fldFiles(root).map((path) => relative(root, path)).sort();
   writeFileSync(join(root, "manifest.json"), JSON.stringify(files, null, 2) + "\n");
}
