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
verilator -DSIMULATION -DVERILATOR --lint-only -Wall -f lint/filelist.f -top letc_top --waiver-output lint/waivers.txt
