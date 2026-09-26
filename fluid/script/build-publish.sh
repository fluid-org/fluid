#!/usr/bin/env bash
set -xe

npm version patch --no-git-tag-version --workspaces-update=false
VERSION=$(node -p "require('./package.json').version")
./script/build-package.sh
./script/test-package.sh

git commit -am "v$VERSION"
git tag "v$VERSION"
npm publish --workspaces=false --access public
