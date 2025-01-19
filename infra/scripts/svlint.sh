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
ALL_SV_FILES=$(find $REPO_ROOT -path "build/*" -prune -o -path "*legacy*" -prune -o -name "*.sv" | xargs)

echo "Linting: $ALL_SV_FILES"

cd ..
#svlint -D SIMULATION $ALL_SV_FILES
