#!/bin/bash
# Copyright (C) 2024 John Jekel
# See the LICENSE file at the root of the project for licensing info.
#
# Regression script for synthesis

# Exit on error immediately
set -e

####################################################################################################
# Subblock
####################################################################################################

pushd subblock

make clean synth BLOCK=common/axi/axi_buffer
make clean synth BLOCK=common/fifo/fifo_0r0w
make clean synth BLOCK=common/fifo/fifo_0r1w
make clean synth BLOCK=common/fifo/fifo_1r1w
make clean synth BLOCK=common/sram/amd_bram

make clean synth BLOCK=letc/core
make clean synth BLOCK=letc/core/axi_fsm
make clean synth BLOCK=letc/core/multiplier
make clean synth BLOCK=letc/core/rf
make clean synth BLOCK=letc/core/stage_d
make clean synth BLOCK=letc/matrix

popd

####################################################################################################
# Full-Chip
####################################################################################################

pushd fc

make clean synth

popd
