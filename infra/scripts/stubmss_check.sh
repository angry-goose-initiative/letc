#!/usr/bin/env bash
#Partially borrowed from JZJ's URA project!
#Copyright:
#   Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
#   Copyright (C) 2024 Nachiket Kapre
#   Copyright (C) 2024-2025 John Jekel
#See the README.md file at the root of the repo for licensing info.
#
#Example invocation: stubmss_check.sh path/to/test_program.vhex8 (and optionally an addititional "1" argument to view waves)
set -e
set -o pipefail

####################################################################################################
# Variables
####################################################################################################

TEST_PROGRAM_PATH=$1
VIEW_WAVES=$2

TEST_PROGRAM=`basename $TEST_PROGRAM_PATH .vhex8`

REPO_ROOT=`git rev-parse --show-toplevel`

IRVE_BINARY=${REPO_ROOT}/build/irve/src/irve
STUBMSS_RUN_SCRIPT=${REPO_ROOT}/infra/scripts/stubmss_run.sh

STUBMSS_OUT_DIR=${REPO_ROOT}/build/stubmss
OUT_DIR=${STUBMSS_OUT_DIR}/${TEST_PROGRAM}

IRVE_LOG=${OUT_DIR}/irve_log.txt
OUTPUT_IRVE_TRACE=${OUT_DIR}/irve_trace.txt
OUTPUT_LETC_TRACE=${OUT_DIR}/letc_trace.txt
OUTPUT_TRACE_DIFF=${OUT_DIR}/irve_to_letc_trace.diff

####################################################################################################
# Running LETC
####################################################################################################

echo "Running LETC..."
$STUBMSS_RUN_SCRIPT $TEST_PROGRAM_PATH $VIEW_WAVES

####################################################################################################
# Running IRVE
####################################################################################################

cd ${OUT_DIR}
ln -s ${REPO_ROOT}/build ${OUT_DIR}/build

echo "Running IRVE..."
$IRVE_BINARY $TEST_PROGRAM_PATH 2>&1 | tee $IRVE_LOG

####################################################################################################
# Diffing Traces
####################################################################################################

echo "Diffing traces..."

diff -u $OUTPUT_IRVE_TRACE $OUTPUT_LETC_TRACE | tee $OUTPUT_TRACE_DIFF
