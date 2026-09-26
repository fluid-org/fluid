#!/usr/bin/env bash
# Copy website/article into fluid/ for npm packaging.
# Run from fluid/ directory before `npm publish`.
set -e

WEBSITE="${1:-article}"
SRC="../website/$WEBSITE"
DEST="website/$WEBSITE"

if [ ! -d "$SRC" ]; then
   echo "Error: $SRC does not exist" >&2
   exit 1
fi

rm -rf "$DEST"
mkdir -p "$DEST"

rsync -a --exclude=node_modules --exclude=.svelte-kit --exclude=build "$SRC/" "$DEST/"

# Rewrite workspace:* dependency on @fluid-org/fluid to the published version
# (npm publish on the wrapping tarball doesn't tolerate workspace: in nested package.json).
FLUID_VERSION=$(node -p "require('./package.json').version")
sed -i.bak "s|\"@fluid-org/fluid\": \"workspace:\\*\"|\"@fluid-org/fluid\": \"^$FLUID_VERSION\"|g" "$DEST/package.json"
rm -f "$DEST/package.json.bak"

# Replace symlinks with copies from the source tree
# static/fluid/fluid → fluid standard library
rm -f "$DEST/static/fluid/fluid"
cp -r fluid/fluid "$DEST/static/fluid/fluid"

# src/lib/assets/css/styles.css → shared CSS
rm -f "$DEST/src/lib/assets/css/styles.css"
cp ../website/src/lib/assets/css/styles.css "$DEST/src/lib/assets/css/styles.css"

echo "Staged $WEBSITE for npm packaging."
