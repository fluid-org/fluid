# Development Process

## Checklists

### After every push
- [ ] Check GitHub Actions for pushed branch — confirm run passes or diagnose failures

### After every commit
- [ ] Review what was done before proceeding

### After merging issue branch
- [ ] Delete issue branch (local and remote)
- [ ] Update milestone report if issue is complete

### After populating milestone
- [ ] Run `./script/check-project-integrity.sh` to verify invariants

### After any change to project board state
- [ ] Verify project view at https://github.com/orgs/fluid-org/projects/1

### Before npm publish
- [ ] Run full test suite: `./script/test-website-all.sh`
- [ ] Working tree clean (publish script commits the version bump)

## Principles

- Write concisely: omit articles unless needed for clarity. Applies everywhere — docs, issue titles, commit messages, comments, this file.
- Avoid comments. Add only to justify an unusual implementation. No historical, restatement-of-code, or "what changed" commentary. Same for test fixtures.
- Comments: single line; wrap at ~110; no mini-paragraphs.
- Avoid weasel-words and jargon: e.g. "land", "honest"/"honestly", "ceremony".
- Before writing code: scan codebase for naming conventions and existing helpers; build from existing behaviours rather than reinventing.
- Pause, review, and commit after every non-trivial step.
- Minor docs, process changes, and trivial fixes can be committed directly to current milestone branch.

## Branching

All issues belong to a milestone. Milestones named `<repo> <major>.<minor>` (e.g. `fluid 0.12`).

```
issue branch → milestone branch → develop → staging → release
```

- **Milestone branches**: named to match milestone (e.g. `fluid-0.12`).
- **Issue branches**: named `<issue-number>-<short-description>`, branched from milestone branch.
- **PRs to milestone branches**: Claude can merge directly once CI passes.
- **PRs to develop**: developer decides when to merge. [Milestone report](milestone-report.md) generated at this point.

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

Package version tracks milestone (e.g. `fluid 0.12` → `0.12.x`). Publish via `yarn workspace @fluid-org/fluid build-publish` (from any directory). Script bumps patch version, commits, tags `vX.Y.Z`, builds, stages website, and publishes to npm. After it succeeds, push manually: `git push && git push --tags`.

Auth: needs an npm automation token in `~/.npmrc` (`//registry.npmjs.org/:_authToken=...`) — bypasses 2FA.

## Issue lifecycle

1. **Select** issue from current milestone.
2. **Branch** from milestone branch.
3. **Implement** incrementally, committing after each step.
4. **Test**: run `./script/test-website-all.sh` and any other relevant tests.
5. **Push and create PR** targeting milestone branch.
6. **Merge** once CI passes. Delete branch. Update milestone report.

See [issue-lifecycle.md](issue-lifecycle.md) for state machine and invariants.

## Milestone population

When all issues in milestone are done, paused, or awaiting decision, populate with 3–8 new issues:

1. **Planned issues first** — already prioritised by developer.
2. **Proposed issues** — prefer low-hanging fruit, thematic fit, test coverage.

Adding to milestone bumps Proposed → Planned. Can be done autonomously.

## Escalation

When best approach isn't obvious, Claude should not guess:

1. Comment on GitHub issue with options and recommendation.
2. Move issue to "Awaiting Decision" on project board.
3. Move to other work.

**Destructive or organisation-wide changes require explicit approval.** This includes modifying project board fields, branch protection, org settings, or any mutation that replaces rather than appends data. See [incidents.md](incidents.md).

No undo for GitHub Projects v2 field mutations.

## Tracking

- Commits by Claude are authored by the `rolyp-claude-bot` GitHub account; no `Co-Authored-By` trailer is added (it would produce a duplicate avatar on GitHub).
- Searchable via `git log --author=rolyp-claude-bot`.
- Issue comments record design decisions.
- PRs link to issues and summarise what was done.

## GitHub conventions

- **Issue titles**: noun phrase describing goal. "Fluid" is redundant in titles (repo is Fluid) — omit it.
- **Issue bodies**: do not hard-wrap paragraphs; GitHub markdown flows them, hard wraps render as ragged short lines. Code fences: omit language tag rather than guess.
- **See also footer**: when an issue references other issues or external resources, end with a `## See also` paragraph listing them as bullets. Bare `#N` links render the issue title inline.
- **New issues**: add to [project board](https://github.com/orgs/fluid-org/projects/1) and populate **Status** (usually `Proposed` for new work) and **Aspect**. Also set Type, labels, and milestone when appropriate.
- **Board Status**: read with `script/issue-status.sh <issue>`, set with `script/issue-status.sh <issue> <Status>` (adds the issue to the board if absent). Never `gh project item-list`, which fetches the whole board and trips the GraphQL rate limit. Closing an issue does not change its Status: set `Done` or `Rejected` explicitly.
- **Labels**: use existing labels (`implementation`, `testing`, `setup`, `documentation`).
- **Milestones**: all issues must belong to milestone.
- **Issue bodies**: keep checklist items updated.

## Testing

Repo is a Yarn monorepo.

`yarn workspace @fluid-org/fluid test` runs the unit test suite via `fluid/test/Test.purs`'s `tests`, which defaults to `allTests`. To run a focused subset:

1. Edit `fluid/test/Test.purs`: change `tests = allTests` to `tests = scratchpad`.
2. Edit `scratchpad` to select cases. Whole suite: `scratchpad = second void <$> suite misc_cases (1 × false)`. Specific files: `scratchpad = filterSuite [ "lambda.fld", "self.fld" ] misc_cases suite` (use `illFormed_cases` and `illFormedSuite` for ill-formed).
3. `yarn workspace @fluid-org/fluid build && yarn workspace @fluid-org/fluid test`.
4. When done, revert `tests = allTests`. Leave `scratchpad` as-is; it's a working area.

Do not invent ad hoc CLI invocations of `fluid.mjs` to run individual `.fld` files — the test harness sets up paths, prelude, and reports errors in the same form tests assert against.

`yarn workspace @fluid-org/fluid test` doesn't exercise website fixtures. Run `./script/test-website-all.sh` from the repo root after changes that touch parsing, desugaring, evaluation, or well-formedness; before pushing a commit that completes a meaningful chunk of work; or whenever in doubt about wider impact. Don't run it on every change — it's slow (a few minutes per website).

## Token setup

Set `GH_TOKEN` per repo via `.claude/settings.local.json` (gitignored):

```json
{"env": {"GH_TOKEN": "<fine-grained-pat>"}}
```

Avoids keyring conflicts across multiple GitHub organisations. Token needs:
- **Pull requests, Issues**: Read and write
- **Organisation projects**: Read, Write, Admin

## Manual setup requirements

When Claude encounters missing permission or setting:
1. Document in pending tasks section.
2. Note specific change needed.
3. Continue with available work.

## Pending manual tasks

None.

Completed tasks recorded in [docs/reports/completed-manual-tasks.md](../reports/completed-manual-tasks.md).
