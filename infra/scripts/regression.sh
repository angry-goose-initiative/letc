#!/usr/bin/env bash
set -e
set -o pipefail

####################################################################################################
# Variables
####################################################################################################

if [ -z "$1" ]; then
    USE_GNU_PARALLEL=0
else
    USE_GNU_PARALLEL=$1
fi

REPO_ROOT=`git rev-parse --show-toplevel`
SCRIPTS_DIR=${REPO_ROOT}/infra/scripts

REGRESSION_FILELIST_DIR=${REPO_ROOT}/filelists/regression

UNIT_IVERILOG=${SCRIPTS_DIR}/unit_iverilog.sh
UNIT_VERILATOR=${SCRIPTS_DIR}/unit_verilator.sh
UNIT_XSIM=${SCRIPTS_DIR}/unit_xsim.sh

SYNTH_VIVADO_OOC=${SCRIPTS_DIR}/synth_vivado_ooc.sh
SYNTH_YOSYS=${SCRIPTS_DIR}/synth_yosys.sh

UNIT_IVERILOG_FILELIST=`${SCRIPTS_DIR}/resolve_filelist.sh ${REGRESSION_FILELIST_DIR}/unit_iverilog.f`
UNIT_VERILATOR_FILELIST=`${SCRIPTS_DIR}/resolve_filelist.sh ${REGRESSION_FILELIST_DIR}/unit_verilator.f`
UNIT_SV2V_VERILATOR_FILELIST=`${SCRIPTS_DIR}/resolve_filelist.sh ${REGRESSION_FILELIST_DIR}/unit_sv2v_verilator.f`
UNIT_XSIM_FILELIST=`${SCRIPTS_DIR}/resolve_filelist.sh ${REGRESSION_FILELIST_DIR}/unit_xsim.f`

SYNTH_VIVADO_OOC_FILELIST=`${SCRIPTS_DIR}/resolve_filelist.sh ${REGRESSION_FILELIST_DIR}/synth_vivado_ooc.f`
SYNTH_YOSYS_FILELIST=`${SCRIPTS_DIR}/resolve_filelist.sh ${REGRESSION_FILELIST_DIR}/synth_yosys.f`

####################################################################################################
# Useful Output
####################################################################################################

echo "USE_GNU_PARALLEL:                 $USE_GNU_PARALLEL"
echo "REPO_ROOT:                        $REPO_ROOT"
echo "SCRIPTS_DIR:                      $SCRIPTS_DIR"
echo "REGRESSION_FILELIST_DIR:          $REGRESSION_FILELIST_DIR"
echo "UNIT_IVERILOG:                    $UNIT_IVERILOG"
echo "UNIT_VERILATOR:                   $UNIT_VERILATOR"
echo "UNIT_XSIM:                        $UNIT_XSIM"
echo "SYNTH_VIVADO_OOC:                 $SYNTH_VIVADO_OOC"
echo "SYNTH_YOSYS:                      $SYNTH_YOSYS"
echo "UNIT_IVERILOG_FILELIST:           $UNIT_IVERILOG_FILELIST"
echo "UNIT_VERILATOR_FILELIST:          $UNIT_VERILATOR_FILELIST"
echo "UNIT_SV2V_VERILATOR_FILELIST:     $UNIT_SV2V_VERILATOR_FILELIST"
echo "UNIT_XSIM_FILELIST:               $UNIT_XSIM_FILELIST"
echo "SYNTH_VIVADO_OOC_FILELIST:        $SYNTH_VIVADO_OOC_FILELIST"
echo "SYNTH_YOSYS_FILELIST:             $SYNTH_YOSYS_FILELIST"

####################################################################################################
# Unit
####################################################################################################

#iverilog
if [[ $USE_GNU_PARALLEL == "1" ]]; then
    echo $UNIT_IVERILOG_FILELIST | parallel --bar $UNIT_IVERILOG
else
    echo $UNIT_IVERILOG_FILELIST | xargs -n 1 -P 1 $UNIT_IVERILOG
fi

#sv2v_verilator
if [[ $USE_GNU_PARALLEL == "1" ]]; then
    echo $UNIT_SV2V_VERILATOR_FILELIST | parallel --bar $UNIT_VERILATOR {} 0 1
else
    echo $UNIT_SV2V_VERILATOR_FILELIST | xargs -I % -n 1 -P 1 $UNIT_VERILATOR % 0 1
fi

#verilator
if [[ $USE_GNU_PARALLEL == "1" ]]; then
    echo $UNIT_VERILATOR_FILELIST | parallel --bar $UNIT_VERILATOR
else
    echo $UNIT_VERILATOR_FILELIST | xargs -n 1 -P 1 $UNIT_VERILATOR
fi

#xsim
if [[ $USE_GNU_PARALLEL == "1" ]]; then
    echo $UNIT_XSIM_FILELIST | parallel --bar $UNIT_XSIM
else
    echo $UNIT_XSIM_FILELIST | xargs -n 1 -P 1 $UNIT_XSIM
fi

####################################################################################################
# Synth
####################################################################################################

#yosys
if [[ $USE_GNU_PARALLEL == "1" ]]; then
    echo $SYNTH_YOSYS_FILELIST | parallel --bar $SYNTH_YOSYS
else
    echo $SYNTH_YOSYS_FILELIST | xargs -n 1 -P 1 $SYNTH_YOSYS
fi

#vivado_ooc
if [[ $USE_GNU_PARALLEL == "1" ]]; then
    echo $SYNTH_VIVADO_OOC_FILELIST | parallel --bar $SYNTH_VIVADO_OOC
else
    echo $SYNTH_VIVADO_OOC_FILELIST | xargs -n 1 -P 1 $SYNTH_VIVADO_OOC
fi
