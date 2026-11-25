#!/usr/bin/env bash
# Publish next pre-release of milestone to npm under next dist-tag; run by build workflow
set -xe
cd "$(dirname "$0")/.."

VERSION=$(node -p "require('./package.json').version")
RELEASE=${VERSION%-next.0}
if [ "$GITHUB_REF_NAME" != "fluid-${RELEASE%.*}" ]; then
   echo "Branch $GITHUB_REF_NAME is not milestone branch of version $RELEASE" >&2
   exit 1
fi

N=$(npm view @fluid-org/fluid versions --json | python3 -c '
import json, sys
release = sys.argv[1]
prefix = release + "-next."
versions = json.load(sys.stdin)
if release in versions:
    sys.exit("Version " + release + " already published")
print(max([0] + [int(v[len(prefix):]) for v in versions if v.startswith(prefix)]) + 1)
' "$RELEASE")

npm version "$RELEASE-next.$N" --no-git-tag-version --workspaces-update=false
./script/build-package.sh
./script/test-package.sh
npm publish --workspaces=false --access public --tag next
