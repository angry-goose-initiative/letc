#!/usr/bin/env bash

REPO_ROOT=`git rev-parse --show-toplevel`
FILELIST_DIR="${REPO_ROOT}/filelists"

gcc -x c -E -w -P -I $FILELIST_DIR $@ | xargs
