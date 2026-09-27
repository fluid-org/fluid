#!/usr/bin/env bash
set -xe

rm -rf dist/
./script/util/compile.sh
. script/util/clean.sh test
. script/util/bundle.sh test Test.Test
./script/bundle-fluid.sh
yarn fluid manifest lib test
