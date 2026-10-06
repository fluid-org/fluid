#!/usr/bin/env bash
# Run the pure-py-spec suite with Fluid as the checker. Failures expected are listed in test/spec-differences.txt;
# `--update` rewrites the list from this run.
set -e
cd "$(dirname "$0")/.."

REF=run-all-checker # revision of pure-py/pure-py-spec; a tag once pure-py/pure-py-spec#217 is released
SPEC=.spec/pure-py-spec

if [ "$(cat $SPEC.ref 2>/dev/null)" != "$REF" ]; then
  rm -rf $SPEC
  git clone --quiet --depth 1 --branch $REF https://github.com/pure-py/pure-py-spec.git $SPEC
  echo "$REF" > $SPEC.ref
fi

python3 $SPEC/test/run-all.py --checker "$PWD/script/spec-checker.sh" --no-run --no-mypy \
  --known-failures "$PWD/test/spec-differences.txt" "$@"
