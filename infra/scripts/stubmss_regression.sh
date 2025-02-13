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

STUBMSS_CHECK=${SCRIPTS_DIR}/stubmss_check.sh

STUBMSS_TEST_PROGRAM_FILELIST=`${SCRIPTS_DIR}/resolve_filelist.sh ${REGRESSION_FILELIST_DIR}/stubmss.f`

####################################################################################################
# Useful Output
####################################################################################################

echo "USE_GNU_PARALLEL:                 $USE_GNU_PARALLEL"
echo "REPO_ROOT:                        $REPO_ROOT"
echo "SCRIPTS_DIR:                      $SCRIPTS_DIR"
echo "REGRESSION_FILELIST_DIR:          $REGRESSION_FILELIST_DIR"
echo "STUBMSS_RUN:                      $STUBMSS_RUN"
echo "STUBMSS_TEST_PROGRAM_FILELIST:    $STUBMSS_TEST_PROGRAM_FILELIST"

if [[ $USE_GNU_PARALLEL == "1" ]]; then
    mkdir -p ${REPO_ROOT}/build
    GNU_PARALLEL_COMMANDS_FILE=${REPO_ROOT}/build/gnu_parallel_commands.txt
    rm -f $GNU_PARALLEL_COMMANDS_FILE
    touch $GNU_PARALLEL_COMMANDS_FILE

    echo $STUBMSS_TEST_PROGRAM_FILELIST | xargs -n 1 -P 1 echo $STUBMSS_CHECK >> $GNU_PARALLEL_COMMANDS_FILE

    #Now run all the things!
    parallel --slf .. --bar < $GNU_PARALLEL_COMMANDS_FILE
else
    echo $STUBMSS_TEST_PROGRAM_FILELIST | xargs -n 1 -P 1 $STUBMSS_CHECK
fi
