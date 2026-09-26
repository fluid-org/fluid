#!/usr/bin/env bash
# Build and stage npm package without publishing. Run from fluid/.
set -xe

yarn build-prod
./script/stage-website.sh article
npm pack --dry-run --workspaces=false
