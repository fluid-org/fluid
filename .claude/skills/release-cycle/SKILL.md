---
name: release-cycle
description: Fluid's branching model, milestone lifecycle, deployment and npm publishing. Use when branching for an issue, merging a milestone, populating a milestone, deploying the website or publishing the package.
---

# Fluid release cycle

## Branching

All issues belong to a milestone. Milestones named `<repo> <major>.<minor>` (e.g. `fluid 1.0`).

```
issue branch → milestone branch → develop → staging → release
```

- **Milestone branches**: named to match milestone (e.g. `fluid-1.0`).
- **Issue branches**: named `<issue-number>-<short-description>`, branched from milestone branch; PRs target milestone branch.
- **PRs to develop**: developer decides when to merge. [Milestone report](../../../docs/workflow/milestone-report.md) generated at this point.
- **Release notes**: one line per closed issue of the milestone, giving its title; omit issues that only aggregate others (e.g. a sync to a PurePy version). Classify an issue only as its issue states; otherwise Other.

## Issue lifecycle

Select issue from current milestone; branch, implement, test ([CONTRIBUTING.md](../../../CONTRIBUTING.md#testing)), PR, review and merge per `conventions:github` skill. After merging: update milestone report if issue is complete. State machine and invariants: [issue-lifecycle.md](../../../docs/workflow/issue-lifecycle.md).

## Milestone population

When all issues in milestone are done, paused, or awaiting decision, populate with 3–8 new issues:

1. **Planned issues first** — already prioritised by developer.
2. **Proposed issues** — prefer low-hanging fruit, thematic fit, test coverage.

Adding to milestone bumps Proposed → Planned. Can be done autonomously. Afterwards run the project integrity check (`script/check-project-integrity.sh`) to verify invariants.

## Deployment

```
develop → staging → release
```

Managed manually by developer:
1. Merge `develop` to `staging` — triggers deploy to GitHub Pages (f.luid.org).
2. Test live site.
3. If good: merge `staging` to `release`.
4. If broken: reset `staging` to `release`.

## NPM publishing

Package version tracks milestone (e.g. `fluid 1.0` → `1.0.x`). Before publishing: run `./script/test-website-all.sh`; working tree clean (publish script commits the version bump). Publish per [CONTRIBUTING.md](../../../CONTRIBUTING.md#publishing-to-npm).
