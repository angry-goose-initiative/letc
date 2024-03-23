#!/bin/bash
# Copyright (C) 2024 John Jekel
# See the LICENSE file at the root of the project for licensing info.
#
# Lint All The Things!
#
# Should be run from the lint directory

# Exit on error immediately
set -e

cd ..
grep -o '^[^#]*' lint/filelist.f | xargs verible-verilog-lint --rules_config .rules.verible_lint
