# Intermediate-value benchmark: fixture census

Notes for issue #964. Companion to `intermediate-perf.tex`.

`@doc` fixtures on the test path (`fluid`, `test/fluid`), by intermediate
vertices (distinct `@doc`-annotated values reaching the graph) / total vertices.
Measured 2026-07-12 via `probeIntermediates` (`Test.Benchmark.Intermediate`).

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
- **Perf: only `conv.fld` is viable** (multi-vertex and large); others are too
  small for a meaningful with/without delta. Broaden by adding `@doc` inside
  loops, or making the website `convolution.fld`/`figure1.fld` loadable.
- **Correctness: `comments/*` give cheap coverage** across value shapes.
- `projection.fld` = 0 (Fluid discards `@doc` on projections); negative case,
  keep out of the perf harness.
