#!/usr/bin/env bash
set -e

ORG="${1:?organisation}"
REPO="${2:?repository}"
PROJECT="${3:?project number}"
ACTIVE="${4:?comma-separated Statuses whose issues must have a milestone}"
ERRORS=0

echo "Checking project integrity for $ORG/$REPO (project $PROJECT)..."

ALL_ITEMS=$(gh api graphql --paginate -f org="$ORG" -F project="$PROJECT" -f query='
  query($endCursor: String, $org: String!, $project: Int!) {
    organization(login: $org) {
      projectV2(number: $project) {
        items(first: 100, after: $endCursor) {
          pageInfo { hasNextPage endCursor }
          nodes {
            fieldValueByName(name: "Status") {
              ... on ProjectV2ItemFieldSingleSelectValue { name }
            }
            content {
              ... on Issue {
                number
                title
                state
                milestone { title }
                repository { name }
              }
            }
          }
        }
      }
    }
  }
' --jq '[.data.organization.projectV2.items.nodes[] | select(.content != null and .content.repository.name == "'"$REPO"'")]')

CLOSED_ISSUES=$(gh api graphql --paginate -f org="$ORG" -f repo="$REPO" -f query='
  query($endCursor: String, $org: String!, $repo: String!) {
    repository(owner: $org, name: $repo) {
      issues(first: 100, states: CLOSED, after: $endCursor) {
        pageInfo { hasNextPage endCursor }
        nodes {
          number
          title
          subIssues(first: 100) { nodes { number state } }
        }
      }
    }
  }
' --jq '[.data.repository.issues.nodes[]]')

CLOSED_MILESTONES=$(gh api "repos/$ORG/$REPO/milestones?state=closed" --jq '[.[].title]')
ACTIVE_STATUSES=$(jq -cn --arg s "$ACTIVE" '$s | split(",") | map(ltrimstr(" ") | rtrimstr(" "))')

check() {
  local rule="$1"
  local items="$2"
  local filter="$3"
  local fmt="$4"

  echo ""
  echo "=== $rule ==="
  while IFS= read -r line; do
    [ -z "$line" ] && continue
    echo "  FAIL: $line"
    ERRORS=$((ERRORS + 1))
  done < <(echo "$items" | jq -r ".[] | $filter | $fmt")
}

check "Every open issue has a Status" "$ALL_ITEMS" \
  'select(.content.state == "OPEN" and .fieldValueByName == null)' \
  '"#\(.content.number) (\(.content.title)): no Status"'

check "Milestoned issues are not Proposed" "$ALL_ITEMS" \
  'select(.content.state == "OPEN" and .content.milestone != null and .fieldValueByName.name == "Proposed")' \
  '"#\(.content.number) (\(.content.title)): Proposed but in milestone \(.content.milestone.title)"'

check "Active issues have a milestone" "$ALL_ITEMS" \
  'select(.content.state == "OPEN" and .content.milestone == null and (.fieldValueByName.name as $s | '"$ACTIVE_STATUSES"' | index($s)))' \
  '"#\(.content.number) (\(.content.title)): \(.fieldValueByName.name) but no milestone"'

check "Closed milestones contain only Done or Rejected issues" "$ALL_ITEMS" \
  'select(.content.milestone != null and (.content.milestone.title as $m | '"$CLOSED_MILESTONES"' | index($m)) and (.fieldValueByName.name != "Done" and .fieldValueByName.name != "Rejected"))' \
  '"#\(.content.number) (\(.content.title)): \(.fieldValueByName.name // "no Status") in closed milestone \(.content.milestone.title)"'

check "Sub-issues of closed issues are closed" "$CLOSED_ISSUES" \
  'select(any(.subIssues.nodes[]; .state == "OPEN"))' \
  '"#\(.number) (\(.title)): open sub-issues \([.subIssues.nodes[] | select(.state == "OPEN") | "#\(.number)"] | join(", "))"'

echo ""
if [ "$ERRORS" -eq 0 ]; then
  echo "All checks passed."
else
  echo "$ERRORS issue(s) found."
  exit 1
fi
