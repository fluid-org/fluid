#!/usr/bin/env bash
set -xe

yarn fluid manifest lib test
karma start karma.conf.test.js $@
