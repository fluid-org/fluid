#!/usr/bin/env bash
# Checker for PurePy runner: check test at given path as module, with its directory as root.
set -e
path=$(cd "$(dirname "$1")" && pwd)/$(basename "$1")
cd "$(dirname "$0")/.."
exec node dist/fluid/shared/fluid.mjs check --module -p lib -p "$(dirname "$path")" -f "$(basename "$path")"
