#!/usr/bin/env bash
# Publish package to npm with its release notes; run by build workflow
# On milestone branch: publish next pre-release under dist-tag "next"
# On release branch: publish milestone
# After publishing milestone: tag commit, create GitHub release, close milestone, announce in Slack
set -xe
cd "$(dirname "$0")/.."

VERSION=$(node -p "require('./package.json').version")
RELEASE=${VERSION%-*}
PRERELEASE="$RELEASE-next."
MINOR=${RELEASE%.*}
VERSIONS=$(npm view --workspaces=false @fluid-org/fluid versions --json)

if jq -e --arg v "$RELEASE" 'index($v)' <<< "$VERSIONS" > /dev/null; then
   echo "Version $RELEASE already published"
   exit 0
fi

# Field $1 of milestone
milestone() {
   gh api "repos/{owner}/{repo}/milestones?state=all&per_page=100" \
      --jq ".[] | select(.title == \"fluid $MINOR\") | .$1"
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
   OPEN=$(milestone open_issues)
   if [ "$OPEN" != 0 ]; then
      echo "Milestone fluid $MINOR has $OPEN open issues" >&2
      exit 1
   fi
   if [ -z "$SLACK_WEBHOOK_URL" ]; then
      echo "SLACK_WEBHOOK_URL not set" >&2
      exit 1
   fi
   publish "$RELEASE"
   git tag "v$RELEASE"
   git push origin "v$RELEASE"
   tail -n +3 CHANGELOG.md | gh release create "v$RELEASE" --verify-tag --title "fluid $RELEASE" --notes-file -
   gh api -X PATCH "repos/{owner}/{repo}/milestones/$(milestone number)" -f state=closed
   python3 script/notify-slack.py
elif [ "$GITHUB_REF_NAME" = "fluid-$MINOR" ]; then
   N=$(jq --arg p "$PRERELEASE" '[.[] | select(startswith($p)) | ltrimstr($p) | tonumber] | max + 1' \
      <<< "$VERSIONS")
   publish "$PRERELEASE$N" --tag next
else
   echo "Branch $GITHUB_REF_NAME is neither release nor milestone branch of version $RELEASE" >&2
   exit 1
fi
