## Fluid

A pure functional dialect of Python, based on [PurePy](https://github.com/pure-py/pure-py-spec), with a dependency-tracking runtime for creating interactive outputs linked to data.

[![build](https://github.com/fluid-org/fluid/actions/workflows/build.yml/badge.svg)](https://github.com/fluid-org/fluid/actions/workflows/build.yml)
[![version](https://img.shields.io/github/package-json/v/fluid-org/fluid/release?filename=fluid%2Fpackage.json&label=version)](https://github.com/fluid-org/fluid/blob/release/fluid/package.json)
[![PurePy](https://img.shields.io/endpoint?url=https%3A%2F%2Fraw.githubusercontent.com%2Ffluid-org%2Ffluid%2Frelease%2Ffluid%2Ftest%2Fspec-compliance.json)](https://github.com/fluid-org/fluid/blob/release/fluid/test/spec-gaps.txt)

## Getting started

Requires [Node.js](https://nodejs.org/) >= 22. In a new project directory:

```bash
curl -fsSL https://raw.githubusercontent.com/fluid-org/fluid/release/script/setup/install.sh | bash
```

### VS Code

To get Python syntax highlighting for `.fld` files, add to `settings.json`:

```json
"files.associations": {
    "*.fld": "python"
}
```

## Contributing

See [CONTRIBUTING.md](https://github.com/fluid-org/fluid/blob/release/CONTRIBUTING.md) for developer setup, building, testing, and the development workflow.
