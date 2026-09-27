#!/usr/bin/env bash
# Print or set board Status: issue-status.sh <issue> [Status]. Avoids listing the board, which trips the GraphQL rate limit.
set -e

ISSUE="$1"
STATUS="$2"
ORG=fluid-org
REPO=fluid
PROJECT=1

if [[ -z "$ISSUE" ]]; then
  echo "usage: $0 <issue> [Status]"
  exit 1
fi

ITEM=$(gh api graphql -f query='
  query {
    repository(owner: "'"$ORG"'", name: "'"$REPO"'") {
      issue(number: '"$ISSUE"') {
        projectItems(first: 10) {
          nodes {
            id
            project { number }
            fieldValueByName(name: "Status") {
              ... on ProjectV2ItemFieldSingleSelectValue { name }
            }
          }
        }
      }
    }
  }' --jq '.data.repository.issue.projectItems.nodes[] | select(.project.number == '"$PROJECT"')')

if [[ -z "$STATUS" ]]; then
  if [[ -z "$ITEM" ]]; then
    echo "#$ISSUE: not on project board"
  else
    echo "#$ISSUE: $(jq -r '.fieldValueByName.name // "no Status"' <<< "$ITEM")"
  fi
  exit 0
fi

FIELD=$(gh api graphql -f query='
  query {
    organization(login: "'"$ORG"'") {
      projectV2(number: '"$PROJECT"') {
        id
        field(name: "Status") {
          ... on ProjectV2SingleSelectField { id options { id name } }
        }
      }
    }
  }' --jq '.data.organization.projectV2')
PROJECT_ID=$(jq -r '.id' <<< "$FIELD")
FIELD_ID=$(jq -r '.field.id' <<< "$FIELD")
OPTION_ID=$(jq -r --arg s "$STATUS" '.field.options[] | select(.name == $s) | .id' <<< "$FIELD")

if [[ -z "$OPTION_ID" ]]; then
  echo "No Status option '$STATUS'; options: $(jq -r '[.field.options[].name] | join(", ")' <<< "$FIELD")"
  exit 1
fi

if [[ -z "$ITEM" ]]; then
  ITEM_ID=$(gh project item-add "$PROJECT" --owner "$ORG" --url "https://github.com/$ORG/$REPO/issues/$ISSUE" --format json --jq .id)
else
  ITEM_ID=$(jq -r '.id' <<< "$ITEM")
fi

gh project item-edit --project-id "$PROJECT_ID" --id "$ITEM_ID" --field-id "$FIELD_ID" --single-select-option-id "$OPTION_ID" > /dev/null
echo "#$ISSUE: $STATUS"
