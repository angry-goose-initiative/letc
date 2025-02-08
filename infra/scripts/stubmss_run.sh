#!/usr/bin/env bash
#Partially borrowed from JZJ's URA project!
#Copyright:
#   Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
#   Copyright (C) 2024 Nachiket Kapre
#   Copyright (C) 2024-2025 John Jekel
#See the README.md file at the root of the repo for licensing info.
#
#Example invocation: unit_verilator.sh path/to/test_program.vhex8
set -e
set -o pipefail

####################################################################################################
# Variables
####################################################################################################

TEST_PROGRAM_PATH=$1
VIEW_WAVES=$2

TEST_PROGRAM=`basename $TEST_PROGRAM_PATH .vhex8`

REPO_ROOT=`git rev-parse --show-toplevel`

STUBMSS_OUT_DIR=${REPO_ROOT}/build/stubmss
OUT_DIR=${STUBMSS_OUT_DIR}/${TEST_PROGRAM}

LOG=${OUT_DIR}/simulation_log.txt
OUTPUT_WAVES=${OUT_DIR}/waves.fst
OUTPUT_TRACE=${OUT_DIR}/letc_trace.txt

INTERMEDIATE_DIR=${STUBMSS_OUT_DIR}/intermediate
SIM_BIN=${INTERMEDIATE_DIR}/simulation.elf

####################################################################################################
# Clean + Create Directories
####################################################################################################

rm -rf ${OUT_DIR}
mkdir -p ${OUT_DIR}

#cd ${REPO_ROOT}
#So the waves get placed in the current directory
cd ${OUT_DIR}
ln -s ${REPO_ROOT}/build ${OUT_DIR}/build

####################################################################################################
# Helpful Output
####################################################################################################

echo "TEST_PROGRAM_PATH:    $TEST_PROGRAM_PATH" | tee $LOG
echo "VIEW_WAVES:           $VIEW_WAVES" | tee -a $LOG
echo "TEST_PROGRAM:         $TEST_PROGRAM" | tee -a $LOG
echo "REPO_ROOT:            $REPO_ROOT" | tee -a $LOG
echo "STUBMSS_OUT_DIR:      $STUBMSS_OUT_DIR" | tee -a $LOG
echo "OUT_DIR:              $OUT_DIR" | tee -a $LOG
echo "LOG:                  $LOG" | tee -a $LOG
echo "OUTPUT_WAVES:         $OUTPUT_WAVES" | tee -a $LOG
echo "INTERMEDIATE_DIR:     $INTERMEDIATE_DIR" | tee -a $LOG
echo "SIM_BIN:              $SIM_BIN" | tee -a $LOG

####################################################################################################
# Main Script Logic
####################################################################################################

echo "Running $SIM_BIN..." | tee -a $LOG
$SIM_BIN +TEST_PROGRAM_PATH=$TEST_PROGRAM_PATH +OUTPUT_TRACE_PATH=$OUTPUT_TRACE 2>&1 | tee -a $LOG

#Also convert the waves to VCD
#Actually don't do this (much less efficient)
#fst2vcd -f $OUTPUT_WAVES -o $OUTPUT_WAVES_VCD | tee -a $LOG

if [[ $VIEW_WAVES == "1" ]]; then
    echo "Viewing waves..." | tee -a $LOG
    gtkwave $OUTPUT_WAVES
fi

rm ${OUT_DIR}/build
