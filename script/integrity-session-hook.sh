#!/usr/bin/env bash
set -u

dir="${CLAUDE_PROJECT_DIR:-$(pwd)}"
state="${TMPDIR:-/tmp}/claude-statusline"
key=$(printf '%s' "$dir" | shasum | cut -c1-12)
file="$state/integrity-$key"
mkdir -p "$state"
: > "$file"

( (
  trap '' HUP TERM
  cd "$dir" 2>/dev/null || exit 0
  OUT=$(./script/check-project-integrity.sh fluid-org fluid 1 "In Progress,Paused,Awaiting Decision" 2>&1)
  RC=$?
  if [ "$RC" -eq 0 ]; then
    : > "$file"
  else
    FAILS=$(printf '%s\n' "$OUT" | grep 'FAIL:')
    if [ -n "$FAILS" ]; then
      N=$(printf '%s\n' "$FAILS" | grep -c 'FAIL:')
      printf '\033[31mintegrity: %s issue(s)\033[0m' "$N" > "$file"
    else
      printf '\033[31mintegrity: could not run\033[0m' > "$file"
    fi
  fi
) >/dev/null 2>&1 & )

exit 0
