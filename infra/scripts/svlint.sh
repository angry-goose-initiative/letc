#!/bin/bash
# Copyright (C) 2024-2025 John Jekel
# See the LICENSE file at the root of the project for licensing info.
#
# Lint All The Things!
#
# Should be run from the lint directory

# Exit on error immediately
set -e

REPO_ROOT=`git rev-parse --show-toplevel`
FILELIST_DIR=${REPO_ROOT}/filelists
ALL_FILELISTS=$(find $FILELIST_DIR -name "*.f" -not -path "$FILELIST_DIR/regression/*")
ALL_SV_FILES=$(echo $ALL_FILELISTS | xargs -n 1 ${REPO_ROOT}/infra/scripts/resolve_filelist.sh | tr ' ' '\n' | sort -u | xargs)

echo "Linting: $ALL_SV_FILES"

cd $REPO_ROOT
svlint -D SIMULATION $ALL_SV_FILES
