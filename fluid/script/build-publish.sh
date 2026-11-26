#!/usr/bin/env bash
# Publish milestone to npm with its release notes, then announce in Slack; run by build workflow
# Without argument: publish next pre-release under dist-tag "next"
# With argument "release": publish completed milestone, then commit and tag its version and create GitHub release
set -xe
cd "$(dirname "$0")/.."

VERSION=$(node -p "require('./package.json').version")
RELEASE=${VERSION%-next.0}
if [ "$GITHUB_REF_NAME" != "fluid-${RELEASE%.*}" ]; then
   echo "Branch $GITHUB_REF_NAME is not milestone branch of version $RELEASE" >&2
   exit 1
fi
if [ "$VERSION" = "$RELEASE" ]; then
   echo "Version $RELEASE already released" >&2
   [ "$1" = release ] && exit 1
   exit 0
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

# Publish as version $1, with remaining arguments as options of npm publish
publish() {
   npm version "$1" --no-git-tag-version --workspaces-update=false
   python3 script/release-notes.py > CHANGELOG.md
   ./script/build-package.sh
   ./script/test-package.sh
   npm publish --workspaces=false --access public "${@:2}"
}

if [ "$1" = release ]; then
   publish "$RELEASE"
   NOTES="../docs/releases/fluid-${RELEASE%.*}.md"
   cp CHANGELOG.md "$NOTES"
   git add "$NOTES"
   git -c user.name="github-actions[bot]" -c user.email="41898282+github-actions[bot]@users.noreply.github.com" \
      commit -m "Release $RELEASE" package.json "$NOTES"
   git tag "v$RELEASE"
   git push --atomic origin "HEAD:refs/heads/$GITHUB_REF_NAME" "v$RELEASE"
   python3 script/release-notes.py --latest |
      gh release create "v$RELEASE" --verify-tag --title "fluid $RELEASE" --notes-file -
else
   publish "$RELEASE-next.$N" --tag next
fi
python3 script/notify-slack.py
