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

SYNTH_VIVADO_OOC=${SCRIPTS_DIR}/synth_vivado_ooc.sh
SYNTH_YOSYS=${SCRIPTS_DIR}/synth_yosys.sh

SYNTH_VIVADO_OOC_FILELIST=`${SCRIPTS_DIR}/resolve_filelist.sh ${REGRESSION_FILELIST_DIR}/synth_vivado_ooc.f`
SYNTH_YOSYS_FILELIST=`${SCRIPTS_DIR}/resolve_filelist.sh ${REGRESSION_FILELIST_DIR}/synth_yosys.f`

####################################################################################################
# Useful Output
####################################################################################################

echo "USE_GNU_PARALLEL:                 $USE_GNU_PARALLEL"
echo "REPO_ROOT:                        $REPO_ROOT"
echo "SCRIPTS_DIR:                      $SCRIPTS_DIR"
echo "REGRESSION_FILELIST_DIR:          $REGRESSION_FILELIST_DIR"
echo "SYNTH_VIVADO_OOC:                 $SYNTH_VIVADO_OOC"
echo "SYNTH_YOSYS:                      $SYNTH_YOSYS"
echo "SYNTH_VIVADO_OOC_FILELIST:        $SYNTH_VIVADO_OOC_FILELIST"
echo "SYNTH_YOSYS_FILELIST:             $SYNTH_YOSYS_FILELIST"

if [[ $USE_GNU_PARALLEL == "1" ]]; then
    mkdir -p ${REPO_ROOT}/build
    GNU_PARALLEL_COMMANDS_FILE=${REPO_ROOT}/build/gnu_parallel_commands.txt
    rm -f $GNU_PARALLEL_COMMANDS_FILE
    touch $GNU_PARALLEL_COMMANDS_FILE

    #yosys
    echo $SYNTH_YOSYS_FILELIST | xargs -n 1 -P 1 echo $SYNTH_YOSYS >> $GNU_PARALLEL_COMMANDS_FILE

    #vivado_ooc
    echo $SYNTH_VIVADO_OOC_FILELIST | xargs -n 1 -P 1 echo $SYNTH_VIVADO_OOC >> $GNU_PARALLEL_COMMANDS_FILE

    #Now run all the things!
    parallel --slf .. --bar < $GNU_PARALLEL_COMMANDS_FILE
else
    #yosys
    echo $SYNTH_YOSYS_FILELIST | xargs -n 1 -P 1 $SYNTH_YOSYS

    #vivado_ooc
    echo $SYNTH_VIVADO_OOC_FILELIST | xargs -n 1 -P 1 $SYNTH_VIVADO_OOC
fi
