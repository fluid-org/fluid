#!/usr/bin/env bash
# Pack the npm package, install it into a scratch project, install the bundled
# website from it and build the site. Run from fluid/ after build-package.sh.
set -xe

SCRATCH=$(mktemp -d)
trap 'rm -rf "$SCRATCH"' EXIT

TARBALL="$SCRATCH/$(npm pack --workspaces=false --pack-destination "$SCRATCH" | tail -n 1)"

cd "$SCRATCH"
npm init -y > /dev/null
npm install "$TARBALL"
./node_modules/@fluid-org/fluid/script/install-website.sh article

cd website/article
# Depend on the packed version rather than the published one
npm install "$TARBALL"
npm run build
