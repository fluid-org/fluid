#!/usr/bin/env bash
# Build and stage the npm package without publishing it. Run from fluid/.
set -xe

yarn build-prod
./script/stage-website.sh article
npm pack --dry-run --workspaces=false
