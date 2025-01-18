#!/usr/bin/env bash
#Partially borrowed from JZJ's URA project!
#Copyright:
#   Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
#   Copyright (C) 2024 Nachiket Kapre
#   Copyright (C) 2024 John Jekel
#See the README.md file at the root of the repo for licensing info.
#
#Example invocation: synth_yosys.sh path/to/filelist.f
set -e
set -o pipefail

####################################################################################################
# Variables
####################################################################################################

FILELIST_PATH=$1

NAME=`basename $FILELIST_PATH .f`

REPO_ROOT=`git rev-parse --show-toplevel`

SYNTH_DIR=${REPO_ROOT}/synth

SCRIPTS_DIR=${REPO_ROOT}/infra/scripts
FILELIST=`${SCRIPTS_DIR}/resolve_filelist.sh $FILELIST_PATH`

ALL_RTL_FILELIST_DIR=${REPO_ROOT}/filelists/rtl

SYNTH_OUT_DIR=${REPO_ROOT}/build/synth
YOSYS_OUT_DIR=${SYNTH_OUT_DIR}/yosys
OUT_DIR=${YOSYS_OUT_DIR}/`dirname ${FILELIST_PATH} | xargs realpath --relative-to=${ALL_RTL_FILELIST_DIR}`/${NAME}

LOG=${OUT_DIR}/log.txt

INTERMEDIATE_DIR=${OUT_DIR}/intermediate
SV2V_OUTPUT=${INTERMEDIATE_DIR}/sv2v_output.sv
YOSYS_SYNTH_SCRIPT=${INTERMEDIATE_DIR}/yosys_synth_script.ys

OUTPUT_NETLIST_VERILOG=${OUT_DIR}/netlist.v
#OUTPUT_NETLIST_EDIF=${OUT_DIR}/netlist.edif
#OUTPUT_NETLIST_BLIF=${OUT_DIR}/netlist.blif
OUTPUT_SCHEMATIC_PRE_SYNTH=${OUT_DIR}/pre_synth
OUTPUT_SCHEMATIC_POST_SYNTH=${OUT_DIR}/post_synth

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

echo "FILELIST_PATH:                $FILELIST_PATH" | tee $LOG
echo "NAME:                         $NAME" | tee -a $LOG
echo "REPO_ROOT:                    $REPO_ROOT" | tee -a $LOG
echo "SYNTH_DIR:                    $SYNTH_DIR" | tee -a $LOG
echo "SCRIPTS_DIR:                  $SCRIPTS_DIR" | tee -a $LOG
echo "FILELIST:                     $FILELIST" | tee -a $LOG
echo "SYNTH_OUT_DIR:                $SYNTH_OUT_DIR" | tee -a $LOG
echo "YOSYS_OUT_DIR:                $YOSYS_OUT_DIR" | tee -a $LOG
echo "OUT_DIR:                      $OUT_DIR" | tee -a $LOG
echo "LOG:                          $LOG" | tee -a $LOG
echo "INTERMEDIATE_DIR:             $INTERMEDIATE_DIR" | tee -a $LOG
echo "SV2V_OUTPUT:                  $SV2V_OUTPUT" | tee -a $LOG
echo "YOSYS_SYNTH_SCRIPT:           $YOSYS_SYNTH_SCRIPT" | tee -a $LOG
echo "OUTPUT_NETLIST_VERILOG:       $OUTPUT_NETLIST_VERILOG" | tee -a $LOG
#echo "OUTPUT_NETLIST_EDIF:          $OUTPUT_NETLIST_EDIF" | tee -a $LOG
#echo "OUTPUT_NETLIST_BLIF:          $OUTPUT_NETLIST_BLIF" | tee -a $LOG
echo "OUTPUT_SCHEMATIC_PRE_SYNTH:   $OUTPUT_SCHEMATIC_PRE_SYNTH" | tee -a $LOG
echo "OUTPUT_SCHEMATIC_POST_SYNTH:  $OUTPUT_SCHEMATIC_POST_SYNTH" | tee -a $LOG

####################################################################################################
# Main Script Logic
####################################################################################################

echo "Doing SV2V conversion..." | tee -a $LOG
sv2v $FILELIST --top=$NAME > ${SV2V_OUTPUT}

cat > $YOSYS_SYNTH_SCRIPT << EOF
read -sv ${SV2V_OUTPUT}

hierarchy -check -top ${NAME}
show -prefix ${OUTPUT_SCHEMATIC_PRE_SYNTH} -format dot -viewer true
#show -prefix ${OUTPUT_SCHEMATIC_PRE_SYNTH} -format svg -viewer true

synth_xilinx -family xc7 -top ${NAME} -retime
#synth_xilinx -family xc7 -top ${NAME} -retime -edif ${OUTPUT_NETLIST_EDIF} -blif ${OUTPUT_NETLIST_BLIF}

show -prefix ${OUTPUT_SCHEMATIC_POST_SYNTH} -format dot -viewer true
#show -prefix ${OUTPUT_SCHEMATIC_POST_SYNTH} -format svg -viewer true

write_verilog ${OUTPUT_NETLIST_VERILOG}

stat -tech xilinx
EOF

echo "Yosys synthesis script:" | tee -a $LOG
cat $YOSYS_SYNTH_SCRIPT | tee -a $LOG

echo "Running yosys..." | tee -a $LOG
yosys -s $YOSYS_SYNTH_SCRIPT 2>&1 | tee -a $LOG
