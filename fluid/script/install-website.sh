#!/usr/bin/env bash
set -e

WEBSITE="${1:-article}"
NPM_ROOT="node_modules/@fluid-org/fluid"
SRC="$NPM_ROOT/website/$WEBSITE"
DEST="website/$WEBSITE"

if [ ! -d "$SRC" ]; then
   echo "Error: website '$WEBSITE' not found in $NPM_ROOT" >&2
   echo "Available websites:"
   ls "$NPM_ROOT/website/" 2>/dev/null || echo "  (none)"
   exit 1
fi

if [ -e "$DEST" ]; then
   echo "Error: $DEST already exists. Remove it first to reinstall." >&2
   exit 1
fi

# Get the installed version of @fluid-org/fluid
VERSION=$(node -e "console.log(require('./$NPM_ROOT/package.json').version)")

echo "Installing $WEBSITE from @fluid-org/fluid@$VERSION..."
mkdir -p "$(dirname "$DEST")"
cp -r "$SRC" "$DEST"

# Rewrite monorepo-relative paths for standalone use
sed -i.bak \
  -e "s/\"workspace:\*\"/\"$VERSION\"/" \
  -e "s|../../fluid/script/|../../$NPM_ROOT/script/|" \
  "$DEST/package.json"
rm -f "$DEST/package.json.bak"

# Recreate symlinks pointing into node_modules
rm -rf "$DEST/static/lib/fluid"
ln -s "../../../../$NPM_ROOT/dist/fluid/lib/fluid" "$DEST/static/lib/fluid"

echo ""
echo "Installed to $DEST. To run:"
echo "  cd $DEST"
echo "  yarn install"
echo "  yarn dev"
