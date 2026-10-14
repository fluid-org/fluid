# Intermediate-value benchmarks

Notes for issue #964. Companion to the generated tables in this directory:

| File | What it measures |
|---|---|
| `intermediate-doc.csv` / `.tex` | each fixture with and without its `@doc` annotations (`°` = stripped) |
| `intermediate-contracted.csv` / `.tex` | each fixture evaluated uncontracted and contracted (`ᶜ` = contracted) |
| `intermediate-doc-table.tex` | report-ready: one table, Eval/Demands/Suffices grouped under each arm, mean ± standard error |
| `intermediate-contracted-tables.tex` | report-ready: three tables (eval slowdown, demands speedup, demanded-by speedup), following the ESOP 2025 paper's presentation |

All were last generated 2026-08-12 at n = 10 over the ten fixtures in
`Test.Specs.BwdIntermediate.bwdIntermediate_cases`. The CSVs give mean and standard
error per cell. The bare `.tex` files are raw one-row-per-fixture fragments, all metrics
side by side (22 columns for the contracted arm) with `°`/`ᶜ` in the column names, which
pdfLaTeX will not typeset without a Unicode-aware engine — they are an intermediate
form, not for inclusion. The report-ready files are what a paper should `\input`: complete
`table` environments with booktabs rules, caption and label, ASCII throughout, and fixture
names escaped for LaTeX. The `°`/`ᶜ` error figure in a CSV cell is the **standard error**
(`stdErr = stdDev / √n`, `Test/Benchmark/Util.purs`), which is what the ± in the grouped
table reports.

The two tables are not comparable column for column. `intermediate-doc` times the Fig
path (`intermediateTest` → `loadFigWith`), which records no graph size;
`intermediate-contracted` times the graph path (`testContracted` → `testProperties`),
which additionally slices `DemBy-Dir`/`DemBy-Suff` and records `Graph-Nodes` and
`Intermediate-Nodes`.

## Regenerating

The suite runs in headless Chrome under Karma and can only report through the console,
so a run is captured and split afterwards:

```bash
# in fluid/: set tests = scratchpad in test/Test.purs first
yarn build-prod
yarn test > run.log 2>&1
node script/util/extract-bench.mjs run.log ../docs/reports

# then the report-ready tables (pure post-processing of the CSVs, no re-run needed)
node script/util/bench-tables.mjs ../docs/reports/intermediate-contracted.csv \
     ../docs/reports/intermediate-contracted-tables.tex Uncontracted Contracted contracted \
     --esop --runs 10
node script/util/bench-tables.mjs ../docs/reports/intermediate-doc.csv \
     ../docs/reports/intermediate-doc-table.tex '\texttt{@doc}' Stripped doc \
     --grouped --metrics Eval,Demands,Suffices --runs 10
```

`Test.Benchmark.Intermediate` brackets each fixture with `---- BENCH FIXTURE start|done`
lines carrying that fixture's row, so a run that dies partway still says where it stopped
and what the completed fixtures measured. The tables themselves are delimited with
`==== BENCH BEGIN <name> ====`, which is what the extractor looks for.

Karma's `client.mocha.timeout` is 600000ms. The contracted arm takes ~3m10s at n = 10;
raise the timeout if adding fixtures or iterations. One n = 10 run of both arms in the
same browser page stalled indefinitely after the doc arm completed — zero CPU for 29
minutes, no mocha timeout — and has not been diagnosed or reproduced since.

## Results, 2026-08-12

- Contraction retains **every** `@doc` intermediate: `Intermediate-Nodes` is identical
  in both arms for all ten fixtures, while `Graph-Nodes` falls by 2.2×–45.8×.
- Slicing gains track the node collapse: `DemBy-Suff` 1.3×–57.6×, `DemBy-Dir`
  1.1×–19.1×. dtw's uncontracted `DemBy-Dir` is the most expensive operation measured
  (2.48s), cut to 331ms.
- **Eval is slower contracted in 9 of 10 fixtures** (0.69–1.005). This contradicts the
  1.38× eval speedup measured across the main suite and is unresolved.
- `@doc` annotation cost itself is small: eval overhead 1–12%, backward slicing within
  noise. The exception is dtw, whose forward step is 4× slower with annotations
  (38.8ms vs 9.7ms) — its `@doc` sites are inside the inner loop.

## Fixture census

`@doc` fixtures on the test path (`fluid`, `test/fluid`), by intermediate vertices
(distinct `@doc`-annotated values reaching the graph) / total vertices. Measured
2026-07-12 via `probeIntermediates` (`Test.Benchmark.Intermediate`).

| Fixture | Intermediate | Total |
|---|---|---|
| `slicing/intermediates/conv.fld` | **9** | 8737 |
| `comments/list_comp.fld` | 1 | 300 |
| `comments/app_arg.fld` | 1 | 110 |
| `comments/dicts.fld` | 1 | 88 |
| `comments/app.fld` | 1 | 64 |
| `comments/nested_constr.fld` | 2 | 50 |
| `comments/projection.fld` | **0** | 41 |
| `comments/int.fld` | 1 | 18 |
| `not_parens_op.fld` | 1 | 4 |

- The count is how many times a `@doc` expression is evaluated, not the size of
  the annotated value. `conv.fld` scores 9 (its `@doc` runs once per 3×3 cell);
  the rest are single top-level `@doc`s.
- **Perf: only `conv.fld` is viable** among these; the `comments/*` fixtures are too
  small for a meaningful with/without delta. The nine other fixtures in
  `slicing/intermediates/` were added since for this reason.
- **Correctness: `comments/*` give cheap coverage** across value shapes.
- `projection.fld` = 0 (Fluid discards `@doc` on projections); negative case,
  keep out of the perf harness.
