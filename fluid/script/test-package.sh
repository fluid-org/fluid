#!/usr/bin/env bash
# Pack npm package, install into scratch project, install bundled website from
# it, build site. Run from fluid/ after build-package.sh.
set -xe

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
