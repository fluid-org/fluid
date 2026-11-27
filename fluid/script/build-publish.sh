#!/usr/bin/env bash
# Publish package to npm with its release notes; run by build workflow
# On milestone branch: publish next pre-release under dist-tag "next"
# On release branch: publish milestone unless already published
# After publishing milestone: tag commit, create GitHub release, close milestone, announce in Slack
set -xe
cd "$(dirname "$0")/.."

VERSION=$(node -p "require('./package.json').version")
RELEASE=${VERSION%-next.0}
MILESTONE="fluid ${RELEASE%.*}"
VERSIONS=$(npm view --workspaces=false @fluid-org/fluid versions --json)

# Whether version $1 is on npm
published() {
   python3 -c 'import json, sys; sys.exit(sys.argv[1] not in json.loads(sys.argv[2]))' "$1" "$VERSIONS"
}

# Field $1 of milestone
milestone() {
   gh api "repos/{owner}/{repo}/milestones?state=all&per_page=100" \
      --jq ".[] | select(.title == \"$MILESTONE\") | .$1"
}

# Publish as version $1, with remaining arguments as options of npm publish
publish() {
   npm version "$1" --no-git-tag-version --workspaces-update=false
   python3 script/release-notes.py > CHANGELOG.md
   ./script/build-package.sh
   ./script/test-package.sh
   npm publish --workspaces=false --access public "${@:2}"
}

if [ "$GITHUB_REF_NAME" = release ]; then
   if published "$RELEASE"; then
      echo "Version $RELEASE already published" >&2
      exit 0
   fi
   OPEN=$(milestone open_issues)
   if [ "$OPEN" != 0 ]; then
      echo "Milestone $MILESTONE has $OPEN open issues" >&2
      exit 1
   fi
   publish "$RELEASE"
   git tag "v$RELEASE"
   git push origin "v$RELEASE"
   tail -n +3 CHANGELOG.md | gh release create "v$RELEASE" --verify-tag --title "fluid $RELEASE" --notes-file -
   gh api -X PATCH "repos/{owner}/{repo}/milestones/$(milestone number)" -f state=closed
   python3 script/notify-slack.py
elif [ "$GITHUB_REF_NAME" = "fluid-${RELEASE%.*}" ]; then
   if published "$RELEASE"; then
      echo "Version $RELEASE already published" >&2
      exit 1
   fi
   N=$(python3 -c '
import json, sys
prefix = sys.argv[1] + "-next."
print(max([0] + [int(v[len(prefix):]) for v in json.loads(sys.argv[2]) if v.startswith(prefix)]) + 1)
' "$RELEASE" "$VERSIONS")
   publish "$RELEASE-next.$N" --tag next
else
   echo "Branch $GITHUB_REF_NAME is neither release nor milestone branch of version $RELEASE" >&2
   exit 1
fi
