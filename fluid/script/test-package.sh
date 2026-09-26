#!/usr/bin/env bash
# Pack npm package, install into scratch project, install bundled website from
# it, and build site. Requires build-package.sh to have run.
set -xe
cd "$(dirname "$0")/.."

SCRATCH=$(mktemp -d)
trap 'rm -rf "$SCRATCH"' EXIT

TARBALL="$SCRATCH/$(npm pack --workspaces=false --pack-destination "$SCRATCH" | tail -n 1)"

cd "$SCRATCH"
npm init -y > /dev/null
npm install "$TARBALL"
./node_modules/@fluid-org/fluid/script/install-website.sh article

cd website/article
# Depend on packed version, not published one
npm install "$TARBALL"
npm run build
