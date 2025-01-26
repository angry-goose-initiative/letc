#!/usr/bin/env bash
#Partially borrowed from JZJ's URA project!
#Copyright:
#   Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
#   Copyright (C) 2024 Nachiket Kapre
#   Copyright (C) 2024-2025 John Jekel
#See the README.md file at the root of the repo for licensing info.
#
#Example invocation: stubmss_build.sh
set -e
set -o pipefail

####################################################################################################
# Variables
####################################################################################################

TB_FILELIST_PATH="filelists/verif/stubmss/letc_core_stubmss_tb.f"

TB=letc_core_stubmss_tb

BUILD_THREADS=`nproc`
SIM_THREADS=`nproc`
TRACE_THREADS=2

REPO_ROOT=`git rev-parse --show-toplevel`

VERIF_DIR=${REPO_ROOT}/verif
#TODO replace with stubmss-specific one
VERILATOR_WRAPPER=${VERIF_DIR}/stubmss/stubmss_verilator_wrapper.cpp

SCRIPTS_DIR=${REPO_ROOT}/infra/scripts
FILELIST=`${SCRIPTS_DIR}/resolve_filelist.sh $TB_FILELIST_PATH`

OUT_DIR=${REPO_ROOT}/build/stubmss

LOG=${OUT_DIR}/build_log.txt

INTERMEDIATE_DIR=${OUT_DIR}/intermediate
SIM_BIN=${INTERMEDIATE_DIR}/simulation.elf

PERF_FLAGS="-O3 -march=native -mtune=native -flto"

####################################################################################################
# Clean + Create Directories
####################################################################################################

rm -rf ${OUT_DIR}
mkdir -p ${OUT_DIR}
mkdir -p ${INTERMEDIATE_DIR}

cd ${REPO_ROOT}

####################################################################################################
# Helpful Output
####################################################################################################

echo "TB_FILELIST_PATH:     $TB_FILELIST_PATH" | tee $LOG
echo "TB:                   $TB" | tee -a $LOG
echo "BUILD_THREADS:        $BUILD_THREADS" | tee -a $LOG
echo "SIM_THREADS:          $SIM_THREADS" | tee -a $LOG
echo "TRACE_THREADS:        $TRACE_THREADS" | tee -a $LOG
echo "REPO_ROOT:            $REPO_ROOT" | tee -a $LOG
echo "VERIF_DIR:            $VERIF_DIR" | tee -a $LOG
echo "VERILATOR_WRAPPER:    $VERILATOR_WRAPPER" | tee -a $LOG
echo "SCRIPTS_DIR:          $SCRIPTS_DIR" | tee -a $LOG
echo "FILELIST:             $FILELIST" | tee -a $LOG
echo "OUT_DIR:              $OUT_DIR" | tee -a $LOG
echo "LOG:                  $LOG" | tee -a $LOG
echo "INTERMEDIATE_DIR:     $INTERMEDIATE_DIR" | tee -a $LOG
echo "SIM_BIN:              $SIM_BIN" | tee -a $LOG

####################################################################################################
# Main Script Logic
####################################################################################################

echo "Building simulator binary $SIM_BIN..." | tee -a $LOG
verilator \
    --exe --build --timing \
    --build-jobs $BUILD_THREADS --threads $SIM_THREADS \
    +1800-2012ext+sv -sv -Wall -Wno-fatal -cc --assert \
    --trace-threads $TRACE_THREADS --trace-structs --trace-fst \
    -DREPO_ROOT=$REPO_ROOT -DSIMULATION \
    --top-module $TB \
    -MAKEFLAGS OPT="\"$PERF_FLAGS\"" \
    -MAKEFLAGS OPT_SLOW="\"$PERF_FLAGS\"" \
    -MAKEFLAGS OPT_FAST="\"$PERF_FLAGS\"" \
    -MAKEFLAGS OPT_GLOBAL="\"$PERF_FLAGS\"" \
    -LDFLAGS "$PERF_FLAGS" \
    -CFLAGS -fcoroutines \
    -CFLAGS -DSV_TBENCH_NAME=$TB -CFLAGS -DVERILATED_CLASS=V$TB -CFLAGS -DVERILATED_HEADER=\"V$TB.h\" -CFLAGS -DWAVES_OUTPUT_PATH=waves.fst \
    --Mdir $INTERMEDIATE_DIR \
    $VERIF_DIR/include/verif_macros.h $FILELIST $VERILATOR_WRAPPER \
    -o $SIM_BIN 2>&1 | tee -a $LOG
