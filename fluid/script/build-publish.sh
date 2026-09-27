#!/usr/bin/env bash
set -xe
cd "$(dirname "$0")/.."

npm version patch --no-git-tag-version --workspaces-update=false
VERSION=$(node -p "require('./package.json').version")
./script/build-package.sh
./script/test-package.sh

git commit -am "v$VERSION"
git tag "v$VERSION"
npm publish --workspaces=false --access public
