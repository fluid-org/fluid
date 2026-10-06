#!/usr/bin/env bash
# Checker for the pure-py-spec runner: check the test at the given path as a module, with its directory as root.
set -e
path=$(cd "$(dirname "$1")" && pwd)/$(basename "$1")
cd "$(dirname "$0")/.."
exec node dist/fluid/shared/fluid.mjs check --module -p lib -p "$(dirname "$path")" -f "$(basename "$path")"
