#!/bin/sh
# Copyright (C) 2024 John Jekel
# See the LICENSE file at the root of the project for licensing info.
#
# Regression script for Non-UVM testbenches

####################################################################################################
# common
####################################################################################################

make clean simulate TBENCH=common/axi/smoke
make clean simulate TBENCH=common/fifo/fifo_0r1w

####################################################################################################
# example
####################################################################################################

make clean simulate TBENCH=example

####################################################################################################
# letc
####################################################################################################

make clean simulate TBENCH=letc/smoke

#core
make clean simulate TBENCH=letc/core/alu
make clean simulate TBENCH=letc/core/branch_comparator
make clean simulate TBENCH=letc/core/gen_imm
make clean simulate TBENCH=letc/core/rf

#matrix
#TODO
