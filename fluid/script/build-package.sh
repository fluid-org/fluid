#!/usr/bin/env bash
# Build and stage npm package without publishing
set -xe
cd "$(dirname "$0")/.."

yarn build-prod
./script/stage-website.sh article
npm pack --dry-run --workspaces=false
