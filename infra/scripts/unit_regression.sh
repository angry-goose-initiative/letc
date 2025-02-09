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

if [ -z "$2" ]; then
    GITHUB_RUNNER_MODE=0
else
    GITHUB_RUNNER_MODE=$2
fi

REPO_ROOT=`git rev-parse --show-toplevel`
SCRIPTS_DIR=${REPO_ROOT}/infra/scripts

REGRESSION_FILELIST_DIR=${REPO_ROOT}/filelists/regression

UNIT_IVERILOG=${SCRIPTS_DIR}/unit_iverilog.sh
UNIT_VERILATOR=${SCRIPTS_DIR}/unit_verilator.sh
UNIT_XSIM=${SCRIPTS_DIR}/unit_xsim.sh

UNIT_IVERILOG_FILELIST=`${SCRIPTS_DIR}/resolve_filelist.sh ${REGRESSION_FILELIST_DIR}/unit_iverilog.f`
UNIT_VERILATOR_FILELIST=`${SCRIPTS_DIR}/resolve_filelist.sh ${REGRESSION_FILELIST_DIR}/unit_verilator.f`
#UNIT_SV2V_VERILATOR_FILELIST=`${SCRIPTS_DIR}/resolve_filelist.sh ${REGRESSION_FILELIST_DIR}/unit_sv2v_verilator.f`
UNIT_XSIM_FILELIST=`${SCRIPTS_DIR}/resolve_filelist.sh ${REGRESSION_FILELIST_DIR}/unit_xsim.f`

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
echo "UNIT_IVERILOG_FILELIST:           $UNIT_IVERILOG_FILELIST"
echo "UNIT_VERILATOR_FILELIST:          $UNIT_VERILATOR_FILELIST"
#echo "UNIT_SV2V_VERILATOR_FILELIST:     $UNIT_SV2V_VERILATOR_FILELIST"
echo "UNIT_XSIM_FILELIST:               $UNIT_XSIM_FILELIST"

if [[ $GITHUB_RUNNER_MODE == "0" ]]; then
    if [[ $USE_GNU_PARALLEL == "1" ]]; then
        mkdir -p ${REPO_ROOT}/build
        GNU_PARALLEL_COMMANDS_FILE=${REPO_ROOT}/build/gnu_parallel_commands.txt
        rm -f $GNU_PARALLEL_COMMANDS_FILE
        touch $GNU_PARALLEL_COMMANDS_FILE

        #iverilog
        echo $UNIT_IVERILOG_FILELIST | xargs -n 1 -P 1 echo $UNIT_IVERILOG >> $GNU_PARALLEL_COMMANDS_FILE

        #sv2v_verilator
        #echo $UNIT_SV2V_VERILATOR_FILELIST | xargs -I % -n 1 -P 1 echo $UNIT_VERILATOR % 0 1 >> $GNU_PARALLEL_COMMANDS_FILE

        #verilator
        echo $UNIT_VERILATOR_FILELIST | xargs -n 1 -P 1 echo $UNIT_VERILATOR >> $GNU_PARALLEL_COMMANDS_FILE

        #xsim
        echo $UNIT_XSIM_FILELIST | xargs -n 1 -P 1 echo $UNIT_XSIM >> $GNU_PARALLEL_COMMANDS_FILE

        #Now run all the things!
        parallel --slf .. --bar < $GNU_PARALLEL_COMMANDS_FILE
    else
        #iverilog
        echo $UNIT_IVERILOG_FILELIST | xargs -n 1 -P 1 $UNIT_IVERILOG

        #sv2v_verilator
        #echo $UNIT_SV2V_VERILATOR_FILELIST | xargs -I % -n 1 -P 1 $UNIT_VERILATOR % 0 1

        #verilator
        echo $UNIT_VERILATOR_FILELIST | xargs -n 1 -P 1 $UNIT_VERILATOR

        #xsim
        echo $UNIT_XSIM_FILELIST | xargs -n 1 -P 1 $UNIT_XSIM
    fi
elif [[ $GITHUB_RUNNER_MODE == "1" ]]; then #iverilog only
    #iverilog
    echo $UNIT_IVERILOG_FILELIST | xargs -n 1 -P 1 $UNIT_IVERILOG
elif [[ $GITHUB_RUNNER_MODE == "2" ]]; then #verilator only
    #verilator
    echo $UNIT_VERILATOR_FILELIST | xargs -n 1 -P 1 $UNIT_VERILATOR
else
    echo "Invalid GITHUB_RUNNER_MODE: $GITHUB_RUNNER_MODE"
    exit 1
fi
