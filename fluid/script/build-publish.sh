#!/usr/bin/env bash
# Publish next patch version of milestone to npm, then push version tag; run by publish-npm job of build workflow
set -xe
cd "$(dirname "$0")/.."

MILESTONE=$(node -p "require('./package.json').version.split('.').slice(0, 2).join('.')")
if [ "$GITHUB_REF_NAME" != "fluid-$MILESTONE" ]; then
   echo "Branch $GITHUB_REF_NAME is not milestone branch of version $MILESTONE" >&2
   exit 1
fi

LATEST=$(git tag --list "v$MILESTONE.*" --sort=-v:refname | head -n 1)
if [ -z "$LATEST" ]; then
   VERSION="$MILESTONE.0"
else
   VERSION="$MILESTONE.$((${LATEST##*.} + 1))"
fi

npm version "$VERSION" --no-git-tag-version --workspaces-update=false --allow-same-version
./script/build-package.sh
./script/test-package.sh
npm publish --workspaces=false --access public

git tag "v$VERSION"
git push origin "v$VERSION"
