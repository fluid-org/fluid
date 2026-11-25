# Contributing to Fluid

## Development setup

### Prerequisites

- [Node.js](https://nodejs.org/) >= 22
- Enable Yarn via [Corepack](https://nodejs.org/api/corepack.html): `corepack enable`
- git
- (Windows only) [Ubuntu WSL](https://ubuntu.com/desktop/wsl)

### Initial configuration

```bash
git clone git@github.com:fluid-org/fluid.git
cd fluid
./script/setup/dev-setup.sh
yarn install
```

## Building

```bash
yarn workspace @fluid-org/fluid build
```

This compiles PureScript, bundles the Fluid runtime, and produces `output-es/` (ES module output).

## Running websites locally

The websites are SvelteKit apps under `website/`. To run one in dev mode:

```bash
cd website/article
yarn dev
```

For a production-like preview:

```bash
yarn build && yarn preview
```

## Testing

Before pushing, `yarn workspace @fluid-org/fluid build-strict` (fails on unused imports) and `yarn workspace @fluid-org/fluid tidy` (formats in place); the pre-push hook runs both.

### PureScript unit tests

```bash
yarn workspace @fluid-org/fluid build-test
```

Runs `tests` in `fluid/test/Test.purs`, by default `allTests`, then the PurePy conformance suite. For a subset, set `tests = scratchpad` and select cases in `scratchpad` (`filterSuite [ "lambda.fld" ] misc_cases suite`; `illFormedSuite` for ill-formed cases); revert to `allTests` afterwards. Do not run `.fld` files through `fluid.mjs` by hand: the harness sets up paths and reports errors in the form the tests assert against.

### PurePy compliance

```bash
yarn workspace @fluid-org/fluid bundle-fluid
yarn workspace @fluid-org/fluid spec-compliance
```

Runs the PurePy conformance suite, from the `purepy` release named in `fluid/purepy-version` and installed with [uv](https://docs.astral.sh/uv/), with Fluid as checker. Gaps, corpus programs Fluid gets wrong, are listed in `fluid/test/spec-gaps.txt`, and extensions, corpus programs Fluid accepts by design ahead of or beyond the spec, in `fluid/test/spec-extensions.txt` under comment lines naming the PurePy issue; `spec-compliance --update` rewrites the gaps list and the badge in `fluid/test/spec-compliance.json`.

### Website tests (Puppeteer)

Tests all SvelteKit websites with Puppeteer (Chrome and Firefox). Slow (a few minutes per website), so run after changes to parsing, desugaring, evaluation or well-formedness, before pushing a completed piece of work, or when in doubt about wider impact:

```bash
./script/test-website-all.sh
```

Or test a single website:

```bash
cd website/article
yarn test
```

### Browser tests

```bash
yarn workspace @fluid-org/fluid test-browser
```

Opens a browser window; check the JavaScript console for test results.

## Publishing to npm

On creating a milestone branch, set the version in `fluid/package.json` to `X.Y.Z-next.0`, where `X.Y.Z` is the release of the milestone once complete (e.g. `1.2.0-next.0` for milestone `fluid 1.2`). The `publish-npm` job of the build workflow publishes a pre-release of `X.Y.Z` on every push to the milestone branch, once the tests pass. The pre-releases are numbered `1.2.0-next.1`, `1.2.0-next.2` and so on, and carry the dist-tag `next`, so `npm install @fluid-org/fluid@next` installs the most recent pre-release. The job builds in production mode and stages the `article` website. Publishing a pre-release doesn't change `fluid/package.json` or create a tag.

To release a completed milestone, run the build workflow on the milestone branch with `release` selected. Once the tests pass, the job publishes `X.Y.Z` under the dist-tag `latest`, commits that version to the milestone branch and tags the commit `vX.Y.Z`. Later pushes to the branch publish nothing until the version is set to the next pre-release (e.g. `1.2.1-next.0` for a patch release).

Authentication is by [trusted publishing](https://docs.npmjs.com/trusted-publishers), which is configured on npmjs.com for the workflow `build.yml` and doesn't need a token.

## VS Code

- Install the [PureScript IDE](https://marketplace.visualstudio.com/items?itemName=nwolverson.ide-purescript) extension
- In extension settings, select `Add Npm Path`
- Avoid having PureScript installed globally

Windows users:
- Launch VS Code from the Ubuntu (WSL) terminal
- Install the WSL extension

## Workflow

Branching strategy, issue lifecycle, milestone management and deployment: [release-cycle skill](.claude/skills/release-cycle/SKILL.md). Commit, issue and pull request conventions: `conventions:github` skill ([fluid-org/claude-plugins](https://github.com/fluid-org/claude-plugins)).
