#!/bin/bash
#Partially borrowed from JZJ's URA project!
#Copyright:
#   Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
#   Copyright (C) 2024 Nachiket Kapre
#   Copyright (C) 2024 John Jekel
#See the README.md file at the root of the repo for licensing info.
#
#Example invocation: unit_iverilog.sh path/to/filelist_tb.f
set -e
set -o pipefail

####################################################################################################
# Variables
####################################################################################################

TB_FILELIST_PATH=$1
VIEW_WAVES=$2

TB=`basename $TB_FILELIST_PATH .f`

REPO_ROOT=`git rev-parse --show-toplevel`

VERIF_DIR=${REPO_ROOT}/verif

SCRIPTS_DIR=${REPO_ROOT}/infra/scripts
FILELIST=`${SCRIPTS_DIR}/resolve_filelist.sh $TB_FILELIST_PATH`

ALL_TB_FILELIST_DIR=${REPO_ROOT}/filelists/verif/unit/tb

UNIT_OUT_DIR=${REPO_ROOT}/build/unit
XSIM_OUT_DIR=${UNIT_OUT_DIR}/xsim
OUT_DIR=${XSIM_OUT_DIR}/`dirname ${TB_FILELIST_PATH} | xargs realpath --relative-to=${ALL_TB_FILELIST_DIR}`/${TB}

OUTPUT_WAVES=${OUT_DIR}/waves.wdb
#OUTPUT_WAVES_VCD=${OUT_DIR}/waves.vcd
STATS_OUTPUT=${OUT_DIR}/stats.csv
LOG=${OUT_DIR}/log.txt

INTERMEDIATE_DIR=${OUT_DIR}/intermediate

SV2V_OUTPUT=${INTERMEDIATE_DIR}/sv2v_output.sv

TCL=${VERIF_DIR}/unit/unit_xsim.tcl

SNAPSHOT_NAME=snapshot

####################################################################################################
# Clean + Create Directories
####################################################################################################

rm -rf ${OUT_DIR}
mkdir -p ${OUT_DIR}
mkdir -p ${INTERMEDIATE_DIR}

#No easy way to prevent xsim from writing garbage to the current directory so we do this instead
#cd ${REPO_ROOT}
cd ${INTERMEDIATE_DIR}
ln -s ${REPO_ROOT}/* ./

####################################################################################################
# Helpful Output
####################################################################################################

echo "TB_FILELIST_PATH:     $TB_FILELIST_PATH" | tee $LOG
echo "VIEW_WAVES:           $VIEW_WAVES" | tee -a $LOG
echo "TB:                   $TB" | tee -a $LOG
echo "REPO_ROOT:            $REPO_ROOT" | tee -a $LOG
echo "VERIF_DIR:            $VERIF_DIR" | tee -a $LOG
echo "SCRIPTS_DIR:          $SCRIPTS_DIR" | tee -a $LOG
echo "FILELIST:             $FILELIST" | tee -a $LOG
echo "UNIT_OUT_DIR:         $UNIT_OUT_DIR" | tee -a $LOG
echo "XSIM_OUT_DIR:         $XSIM_OUT_DIR" | tee -a $LOG
echo "OUT_DIR:              $OUT_DIR" | tee -a $LOG
echo "OUTPUT_WAVES:         $OUTPUT_WAVES" | tee -a $LOG
#echo "OUTPUT_WAVES_VCD:     $OUTPUT_WAVES_VCD" | tee -a $LOG
echo "STATS_OUTPUT:         $STATS_OUTPUT" | tee -a $LOG
echo "LOG:                  $LOG" | tee -a $LOG
echo "INTERMEDIATE_DIR:     $INTERMEDIATE_DIR" | tee -a $LOG
echo "SV2V_OUTPUT:          $SV2V_OUTPUT" | tee -a $LOG
echo "TCL:                  $TCL" | tee -a $LOG
echo "SNAPSHOT_NAME:        $SNAPSHOT_NAME" | tee -a $LOG

####################################################################################################
# Main Script Logic
####################################################################################################

echo "Parsing (System)Verilog sources..." | tee -a $LOG
xvlog -d REPO_ROOT=$REPO_ROOT -d SIMULATION -d XSIM -sv $VERIF_DIR/include/verif_macros.h $FILELIST | tee -a $LOG

echo "Elaborating design for simulation..." | tee -a $LOG
xelab -debug all -top $TB -snapshot $SNAPSHOT_NAME | tee -a $LOG

echo "Simulating design..." | tee -a $LOG
xsim $SNAPSHOT_NAME -tclbatch $TCL 2>&1 | tee -a $LOG

mv $SNAPSHOT_NAME.wdb $OUTPUT_WAVES

#Return failure if an assertion fired
#Either "Error: Assertion violation" or "ERROR: Assertion failed."
grep "Assertion" -vqz $LOG | tee -a $LOG

if [[ $VIEW_WAVES == "1" ]]; then
    echo "Viewing waves..." | tee -a $LOG
    xsim --gui $SNAPSHOT_NAME
fi
