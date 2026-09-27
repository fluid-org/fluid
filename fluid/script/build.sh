#!/usr/bin/env bash
set -xe

rm -rf dist/
./script/util/compile.sh
node script/manifest.mjs lib test
. script/util/clean.sh test
. script/util/bundle.sh test Test.Test
./script/bundle-fluid.sh
