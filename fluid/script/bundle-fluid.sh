#!/usr/bin/env bash
set -xe
. "$(dirname "$0")/util/paths.sh"

FLUID_EXECUTABLE="dist/fluid/shared/fluid.mjs"
SHEBANG="#!/usr/bin/env node"

yarn purs-backend-es bundle-app --no-build --main Fluid --to $FLUID_EXECUTABLE --platform=node

if [[ ! -f "$FLUID_EXECUTABLE" ]]; then
  echo "Error: File $FLUID_EXECUTABLE not found."
  exit 1
fi

if [[ $(head -n 1 "$FLUID_EXECUTABLE") != "$SHEBANG" ]]; then
  { echo "$SHEBANG"; cat "$FLUID_EXECUTABLE"; } > "$FLUID_EXECUTABLE.tmp" && mv "$FLUID_EXECUTABLE.tmp" "$FLUID_EXECUTABLE"
fi

chmod +x "$FLUID_EXECUTABLE"
cp -r "$LIB_ROOT" "$(dirname "$DIST_LIB_ROOT")"
