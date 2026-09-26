#!/usr/bin/env bash
# Copy website and shared components into the package for npm publishing
set -e
cd "$(dirname "$0")/.."
. script/util/paths.sh

WEBSITE="${1:-article}"
SRC="../website/$WEBSITE"
DEST="website/$WEBSITE"

if [ ! -d "$SRC" ]; then
   echo "Error: $SRC does not exist" >&2
   exit 1
fi

rm -rf "$DEST"
trap 'rm -rf "$DEST" website/src/lib' ERR
mkdir -p "$DEST"

rsync -a --exclude=node_modules --exclude=.svelte-kit --exclude=build "$SRC/" "$DEST/"

# Rewrite workspace:* dependency on @fluid-org/fluid to the published version
# (npm publish on the wrapping tarball doesn't tolerate workspace: in nested package.json).
FLUID_VERSION=$(node -p "require('./package.json').version")
sed -i.bak "s|\"@fluid-org/fluid\": \"workspace:\\*\"|\"@fluid-org/fluid\": \"^$FLUID_VERSION\"|g" "$DEST/package.json"
rm -f "$DEST/package.json.bak"

# Replace symlinks with copies from the source tree
# fluid standard library
rm -f "$DEST/$WEBSITE_LIB_ROOT/fluid"
cp -r "$LIB_PACKAGE" "$DEST/$WEBSITE_LIB_ROOT/fluid"

rm -rf "$WEBSITE_SHARED"
mkdir -p "$(dirname "$WEBSITE_SHARED")"
cp -r "../$WEBSITE_SHARED" "$WEBSITE_SHARED"

echo "Staged $WEBSITE for npm packaging."
