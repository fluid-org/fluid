#!/usr/bin/env bash
# Run the pure-py-spec suite with Fluid as the checker, at the revision in purepy-version. Failures expected are
# listed in test/spec-differences.txt; `--update` rewrites the list from this run and the badge in
# test/spec-compliance.json.
set -e
cd "$(dirname "$0")/.."

REF=$(cat purepy-version)
SPEC=.spec/pure-py-spec
DIFFERENCES=test/spec-differences.txt

if [ "$(cat $SPEC.ref 2>/dev/null)" != "$REF" ]; then
  rm -rf $SPEC
  git clone --quiet --depth 1 --branch "$REF" https://github.com/pure-py/pure-py-spec.git $SPEC
  echo "$REF" > $SPEC.ref
fi

python3 $SPEC/test/run-all.py --checker "$PWD/script/spec-checker.sh" --no-run --no-mypy \
  --known-failures "$PWD/$DIFFERENCES" "$@"

if [[ " $* " == *" --update "* ]]; then
  n=$(wc -l < $DIFFERENCES | tr -d ' ')
  if [ "$n" = 0 ]; then message=compatible; colour=brightgreen; else message="$n incompatibilities"; colour=orange; fi
  printf '{ "schemaVersion": 1, "label": "PurePy %s", "message": "%s", "color": "%s" }\n' "$REF" "$message" "$colour" \
    > test/spec-compliance.json
fi
