#!/usr/bin/env bash
#Partially borrowed from JZJ's URA project!
#Copyright:
#   Copyright (C) 2019 Gurshaant Singh Malik, Nachiket Kapre
#   Copyright (C) 2024 Nachiket Kapre
#   Copyright (C) 2024-2025 John Jekel
#See the README.md file at the root of the repo for licensing info.
#
#Example invocation: synth_vivado_ooc.sh path/to/filelist.f
set -e
set -o pipefail

####################################################################################################
# Variables
####################################################################################################

FILELIST_PATH=$1

NAME=`basename $FILELIST_PATH .f`

#Get parallelism by running multiple sims at once instead
#THREADS=`nproc`
THREADS=1

REPO_ROOT=`git rev-parse --show-toplevel`

SYNTH_DIR=${REPO_ROOT}/synth
XDC=${SYNTH_DIR}/vivado_ooc.xdc

SCRIPTS_DIR=${REPO_ROOT}/infra/scripts
FILELIST=`${SCRIPTS_DIR}/resolve_filelist.sh $FILELIST_PATH`

THIS_RTL_FILELIST_DIR=`dirname ${FILELIST_PATH}`
ALL_RTL_FILELIST_DIR=filelists/rtl/
REL_RTL_FILELIST_DIR=${THIS_RTL_FILELIST_DIR#${ALL_RTL_FILELIST_DIR}}

SYNTH_OUT_DIR=${REPO_ROOT}/build/synth
VIVADO_OOC_OUT_DIR=${SYNTH_OUT_DIR}/vivado_ooc
OUT_DIR=${VIVADO_OOC_OUT_DIR}/${REL_RTL_FILELIST_DIR}/${NAME}

LOG=${OUT_DIR}/log.txt

INTERMEDIATE_DIR=${OUT_DIR}/intermediate
VIVADO_OOC_SYNTH_SCRIPT=${INTERMEDIATE_DIR}/vivado_ooc_synth_script.tcl

OUTPUT_REPORT_POWER=${OUT_DIR}/power.txt
OUTPUT_REPORT_AREA=${OUT_DIR}/area.txt
OUTPUT_REPORT_TIMING=${OUT_DIR}/timing.txt
OUTPUT_NETLIST_VERILOG=${OUT_DIR}/netlist.v
#OUTPUT_NETLIST_EDIF=${OUT_DIR}/netlist.edif

####################################################################################################
# Clean + Create Directories
####################################################################################################

rm -rf ${OUT_DIR}
mkdir -p ${OUT_DIR}
mkdir -p ${INTERMEDIATE_DIR}

#No easy way to prevent vivado from writing garbage to the current directory so we do this instead
#cd ${REPO_ROOT}
cd ${INTERMEDIATE_DIR}
ln -s ${REPO_ROOT}/* ./

####################################################################################################
# Helpful Output
####################################################################################################

echo "FILELIST_PATH:            $FILELIST_PATH" | tee $LOG
echo "NAME:                     $NAME" | tee -a $LOG
echo "THREADS:                  $THREADS" | tee -a $LOG
echo "REPO_ROOT:                $REPO_ROOT" | tee -a $LOG
echo "SYNTH_DIR:                $SYNTH_DIR" | tee -a $LOG
echo "XDC:                      $XDC" | tee -a $LOG
echo "SCRIPTS_DIR:              $SCRIPTS_DIR" | tee -a $LOG
echo "FILELIST:                 $FILELIST" | tee -a $LOG
echo "THIS_RTL_FILELIST_DIR:    $THIS_RTL_FILELIST_DIR" | tee -a $LOG
echo "ALL_RTL_FILELIST_DIR:     $ALL_RTL_FILELIST_DIR" | tee -a $LOG
echo "REL_RTL_FILELIST_DIR:     $REL_RTL_FILELIST_DIR" | tee -a $LOG
echo "SYNTH_OUT_DIR:            $SYNTH_OUT_DIR" | tee -a $LOG
echo "VIVADO_OOC_OUT_DIR:       $VIVADO_OOC_OUT_DIR" | tee -a $LOG
echo "OUT_DIR:                  $OUT_DIR" | tee -a $LOG
echo "LOG:                      $LOG" | tee -a $LOG
echo "INTERMEDIATE_DIR:         $INTERMEDIATE_DIR" | tee -a $LOG
echo "VIVADO_OOC_SYNTH_SCRIPT:  $VIVADO_OOC_SYNTH_SCRIPT" | tee -a $LOG
echo "OUTPUT_REPORT_POWER:      $OUTPUT_REPORT_POWER" | tee -a $LOG
echo "OUTPUT_REPORT_AREA:       $OUTPUT_REPORT_AREA" | tee -a $LOG
echo "OUTPUT_REPORT_TIMING:     $OUTPUT_REPORT_TIMING" | tee -a $LOG
echo "OUTPUT_NETLIST_VERILOG:   $OUTPUT_NETLIST_VERILOG" | tee -a $LOG
#echo "OUTPUT_NETLIST_EDIF:      $OUTPUT_NETLIST_EDIF" | tee -a $LOG

####################################################################################################
# Main Script Logic
####################################################################################################

cat > $VIVADO_OOC_SYNTH_SCRIPT << EOF
create_project TOP -part xc7z007sclg400-1

set_param general.maxThreads ${THREADS}

add_files -norecurse {${FILELIST}}
add_files -fileset constrs_1 -norecurse ${XDC}

update_compile_order -fileset sources_1
update_compile_order -fileset sim_1

if { [catch {synth_design -mode out_of_context -top ${NAME} -lint}] } {
    puts "ERROR: Linting failed"
    exit 1
}

if { [catch {synth_design -mode out_of_context -top ${NAME}}] } {
    puts "ERROR: Synthesis failed"
    exit 1
}

if { [catch {opt_design} ]} {
    puts "ERROR: Optimization failed"
    exit 1
}

if { [catch {place_design}]} {
    puts "ERROR: Placement failed"
    exit 1
}

if { [catch {route_design}]} {
    puts "ERROR: Routing failed"
    exit 1
}

set_switching_activity -default_toggle_rate 100
report_power -file ${OUTPUT_REPORT_POWER}
report_utilization -file ${OUTPUT_REPORT_AREA}
report_timing_summary -file ${OUTPUT_REPORT_TIMING}
#write_edif ${OUTPUT_NETLIST_EDIF}
write_verilog ${OUTPUT_NETLIST_VERILOG}
exit
EOF

#Actually don't print this out so that "ERROR" doesn't appear in the log
#echo "Vivado synthesis script:" | tee -a $LOG
#cat $VIVADO_OOC_SYNTH_SCRIPT | tee -a $LOG

echo "Running Vivado..." | tee -a $LOG
vivado -mode tcl -s $VIVADO_OOC_SYNTH_SCRIPT 2>&1 | tee -a $LOG
