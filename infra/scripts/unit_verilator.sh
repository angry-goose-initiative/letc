#!/usr/bin/env bash
#Partially borrowed from JZJ's URA project!
#Copyright:
#   Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
#   Copyright (C) 2024 Nachiket Kapre
#   Copyright (C) 2024-2025 John Jekel
#See the README.md file at the root of the repo for licensing info.
#
#Example invocation: unit_verilator.sh path/to/filelist_tb.f
set -e
set -o pipefail

####################################################################################################
# Variables
####################################################################################################

TB_FILELIST_PATH=$1
VIEW_WAVES=$2
if [ -z "$3" ]; then
    SV2V_VERILATOR=0
else
    SV2V_VERILATOR=$3
fi

TB=`basename $TB_FILELIST_PATH .f`

#Get parallelism by running multiple sims at once instead
#BUILD_THREADS=`nproc`
BUILD_THREADS=1
SIM_THREADS=1
TRACE_THREADS=1

REPO_ROOT=`git rev-parse --show-toplevel`

VERIF_DIR=${REPO_ROOT}/verif
VERILATOR_WRAPPER=${VERIF_DIR}/unit/unit_verilator_wrapper.cpp

SCRIPTS_DIR=${REPO_ROOT}/infra/scripts
FILELIST=`${SCRIPTS_DIR}/resolve_filelist.sh $TB_FILELIST_PATH`

ALL_TB_FILELIST_DIR=${REPO_ROOT}/filelists/verif/unit/tb

UNIT_OUT_DIR=${REPO_ROOT}/build/unit
VERILATOR_OUT_DIR=${UNIT_OUT_DIR}/verilator
OUT_DIR=${VERILATOR_OUT_DIR}/`dirname ${TB_FILELIST_PATH} | xargs realpath --relative-to=${ALL_TB_FILELIST_DIR}`/${TB}

OUTPUT_WAVES=${OUT_DIR}/waves.fst
#OUTPUT_WAVES_VCD=${OUT_DIR}/waves.vcd
STATS_OUTPUT=${OUT_DIR}/stats.csv
LOG=${OUT_DIR}/log.txt

INTERMEDIATE_DIR=${OUT_DIR}/intermediate
SIM_BIN=${INTERMEDIATE_DIR}/simulation.elf

SV2V_OUTPUT=${INTERMEDIATE_DIR}/sv2v_output.sv

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
echo "VIEW_WAVES:           $VIEW_WAVES" | tee -a $LOG
echo "SV2V_VERILATOR:       $SV2V_VERILATOR" | tee -a $LOG
echo "TB:                   $TB" | tee -a $LOG
echo "BUILD_THREADS:        $BUILD_THREADS" | tee -a $LOG
echo "SIM_THREADS:          $SIM_THREADS" | tee -a $LOG
echo "TRACE_THREADS:        $TRACE_THREADS" | tee -a $LOG
echo "REPO_ROOT:            $REPO_ROOT" | tee -a $LOG
echo "VERIF_DIR:            $VERIF_DIR" | tee -a $LOG
echo "VERILATOR_WRAPPER:    $VERILATOR_WRAPPER" | tee -a $LOG
echo "SCRIPTS_DIR:          $SCRIPTS_DIR" | tee -a $LOG
echo "FILELIST:             $FILELIST" | tee -a $LOG
echo "UNIT_OUT_DIR:         $UNIT_OUT_DIR" | tee -a $LOG
echo "VERILATOR_OUT_DIR:    $VERILATOR_OUT_DIR" | tee -a $LOG
echo "OUT_DIR:              $OUT_DIR" | tee -a $LOG
echo "OUTPUT_WAVES:         $OUTPUT_WAVES" | tee -a $LOG
#echo "OUTPUT_WAVES_VCD:     $OUTPUT_WAVES_VCD" | tee -a $LOG
echo "LOG:                  $LOG" | tee -a $LOG
echo "INTERMEDIATE_DIR:     $INTERMEDIATE_DIR" | tee -a $LOG
echo "SIM_BIN:              $SIM_BIN" | tee -a $LOG
echo "SV2V_OUTPUT:          $SV2V_OUTPUT" | tee -a $LOG

####################################################################################################
# Main Script Logic
####################################################################################################

if [[ $SV2V_VERILATOR == "1" ]]; then
    echo "SV2V_VERILATOR set: Doing SV2V conversion..." | tee -a $LOG
    sv2v $VERIF_DIR/include/verif_macros.h $FILELIST -DVERILATOR -DREPO_ROOT=$REPO_ROOT -DSIMULATION --exclude=Always --exclude=Assert --exclude=UnbasedUnsized --top=$TB > ${SV2V_OUTPUT}
    FILELIST=${SV2V_OUTPUT}
    echo "Filelist is now $FILELIST" | tee -a $LOG
fi

echo "Building simulator binary $SIM_BIN..." | tee -a $LOG
verilator \
    --exe --build --timing \
    --build-jobs $BUILD_THREADS --threads $SIM_THREADS \
    +1800-2012ext+sv -sv -Wall -Wno-fatal -cc --assert \
    --trace-threads $TRACE_THREADS --trace-structs --trace-fst \
    -DREPO_ROOT=$REPO_ROOT -DSIMULATION \
    --top-module $TB \
    -CFLAGS -fcoroutines \
    -CFLAGS -DSV_TBENCH_NAME=$TB -CFLAGS -DVERILATED_CLASS=V$TB -CFLAGS -DVERILATED_HEADER=\"V$TB.h\" -CFLAGS -DWAVES_OUTPUT_PATH=$OUTPUT_WAVES \
    --Mdir $INTERMEDIATE_DIR \
    $VERIF_DIR/include/verif_macros.h $FILELIST $VERILATOR_WRAPPER \
    -o $SIM_BIN 2>&1 | tee -a $LOG

if [[ $SV2V_VERILATOR != "1" ]]; then
    #Skip these extra checks if we're using SV2V since it introduces a bunch of them...
    echo "Checking for build problems..." | tee -a $LOG

    #Return failure if there was a warning or error during the build
    grep "Error" -vqz $LOG | tee -a $LOG
    grep "Warning" -vqz $LOG | tee -a $LOG
fi

echo "Running $SIM_BIN..." | tee -a $LOG
$SIM_BIN 2>&1 | tee -a $LOG

#Also convert the waves to VCD
#Actually don't do this (much less efficient)
#fst2vcd -f $OUTPUT_WAVES -o $OUTPUT_WAVES_VCD | tee -a $LOG

if [[ $VIEW_WAVES == "1" ]]; then
    echo "Viewing waves..." | tee -a $LOG
    gtkwave $OUTPUT_WAVES
fi
