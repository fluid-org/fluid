## Fluid

A pure functional dialect of Python, based on [PurePy](https://github.com/pure-py/pure-py-spec), with a dependency-tracking runtime for creating interactive outputs linked to data.

[![build](https://github.com/fluid-org/fluid/actions/workflows/build.yml/badge.svg)](https://github.com/fluid-org/fluid/actions/workflows/build.yml)
[![spec-compliance](https://github.com/fluid-org/fluid/actions/workflows/spec-compliance.yml/badge.svg)](https://github.com/fluid-org/fluid/actions/workflows/spec-compliance.yml)
[![PurePy](https://img.shields.io/endpoint?url=https://raw.githubusercontent.com/fluid-org/fluid/fluid-1.0/fluid/test/spec-compliance.json)](https://github.com/fluid-org/fluid/blob/fluid-1.0/fluid/test/spec-differences.txt)

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

See [CONTRIBUTING.md](CONTRIBUTING.md) for developer setup, building, testing, and the development workflow.
