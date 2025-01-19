#!/usr/bin/env bash
#Partially borrowed from JZJ's URA project!
#Copyright:
#   Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
#   Copyright (C) 2024 Nachiket Kapre
#   Copyright (C) 2024-2025 John Jekel
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

THIS_TB_FILELIST_DIR=`dirname ${TB_FILELIST_PATH}`
ALL_TB_FILELIST_DIR=filelists/verif/unit/tb/
REL_TB_FILELIST_DIR=${THIS_TB_FILELIST_DIR#${ALL_TB_FILELIST_DIR}}

UNIT_OUT_DIR=${REPO_ROOT}/build/unit
IVERILOG_OUT_DIR=${UNIT_OUT_DIR}/iverilog
OUT_DIR=${IVERILOG_OUT_DIR}/${REL_TB_FILELIST_DIR}/${TB}

OUTPUT_WAVES=${OUT_DIR}/waves.fst
#OUTPUT_WAVES_VCD=${OUT_DIR}/waves.vcd
STATS_OUTPUT=${OUT_DIR}/stats.csv
LOG=${OUT_DIR}/log.txt

INTERMEDIATE_DIR=${OUT_DIR}/intermediate
SIM_BIN=${INTERMEDIATE_DIR}/simulation.vvp

IVERILOG_TOP=${INTERMEDIATE_DIR}/iverilog_top.sv
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
echo "TB:                   $TB" | tee -a $LOG
echo "REPO_ROOT:            $REPO_ROOT" | tee -a $LOG
echo "VERIF_DIR:            $VERIF_DIR" | tee -a $LOG
echo "SCRIPTS_DIR:          $SCRIPTS_DIR" | tee -a $LOG
echo "FILELIST:             $FILELIST" | tee -a $LOG
echo "THIS_TB_FILELIST_DIR: $THIS_TB_FILELIST_DIR" | tee -a $LOG
echo "ALL_TB_FILELIST_DIR:  $ALL_TB_FILELIST_DIR" | tee -a $LOG
echo "REL_TB_FILELIST_DIR:  $REL_TB_FILELIST_DIR" | tee -a $LOG
echo "UNIT_OUT_DIR:         $UNIT_OUT_DIR" | tee -a $LOG
echo "IVERILOG_OUT_DIR:     $IVERILOG_OUT_DIR" | tee -a $LOG
echo "OUT_DIR:              $OUT_DIR" | tee -a $LOG
echo "OUTPUT_WAVES:         $OUTPUT_WAVES" | tee -a $LOG
#echo "OUTPUT_WAVES_VCD:     $OUTPUT_WAVES_VCD" | tee -a $LOG
echo "STATS_OUTPUT:         $STATS_OUTPUT" | tee -a $LOG
echo "LOG:                  $LOG" | tee -a $LOG
echo "INTERMEDIATE_DIR:     $INTERMEDIATE_DIR" | tee -a $LOG
echo "SIM_BIN:              $SIM_BIN" | tee -a $LOG
echo "IVERILOG_TOP:         $IVERILOG_TOP" | tee -a $LOG
echo "SV2V_OUTPUT:          $SV2V_OUTPUT" | tee -a $LOG

####################################################################################################
# Main Script Logic
####################################################################################################

cat > $IVERILOG_TOP << EOF
module iverilog_top;
    ${TB} tb ();

    initial begin
        \$dumpfile("${OUTPUT_WAVES}");
        \$dumpvars(0, iverilog_top.tb);
    end
endmodule
EOF

#TODO set SIMULATION once iverilog supports concurrent assertions
echo "Doing SV2V conversion..." | tee -a $LOG
sv2v $VERIF_DIR/include/verif_macros.h $FILELIST $IVERILOG_TOP -DIVERILOG -DREPO_ROOT=$REPO_ROOT --exclude=Always --exclude=Assert --exclude=UnbasedUnsized --top=iverilog_top > ${SV2V_OUTPUT} | tee -a $LOG
#sv2v $VERIF_DIR/include/verif_macros.h $FILELIST $IVERILOG_TOP -DIVERILOG -DREPO_ROOT=$REPO_ROOT -DSIMULATION --exclude=Always --exclude=Assert --exclude=UnbasedUnsized --top=iverilog_top > ${SV2V_OUTPUT} | tee -a $LOG

echo "Elaborating $TB..." | tee -a $LOG
iverilog -g2012 -gsupported-assertions -DREPO_ROOT=$REPO_ROOT -DSIMULATION -o $SIM_BIN ${SV2V_OUTPUT} | tee -a $LOG

echo "Simulating $TB..." | tee -a $LOG
vvp $SIM_BIN -fst | tee -a $LOG

#Return failure if an assertion fired
grep ERROR -vqz $LOG | tee -a $LOG

#Also convert the waves to VCD
#Actually don't do this (much less efficient)
#fst2vcd -f $OUTPUT_WAVES -o $OUTPUT_WAVES_VCD | tee -a $LOG

if [[ $VIEW_WAVES == "1" ]]; then
    echo "Viewing waves..." | tee -a $LOG
    gtkwave $OUTPUT_WAVES
fi
