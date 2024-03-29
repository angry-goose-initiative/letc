# synthesis.tcl
# Copyright (C) 2024 John Jekel
# See the LICENSE file at the root of the project for licensing info.
#

####################################################################################################
# Variables from Makefile
####################################################################################################

set RTL_ROOT        [lindex $argv 0]
set SUBBLOCK_ROOT   [lindex $argv 1]
set BLOCK_PATH      [lindex $argv 2]

####################################################################################################
# Synthesis Config
####################################################################################################

set RTL_TOP fifo_1r1w
set CONSTRAINTS_SOURCE $SUBBLOCK_ROOT/usual.xdc
set RTL_SOURCE $RTL_ROOT/common/fifo/fifo_1r1w.sv

####################################################################################################
# Run Out of Context Synthesis
####################################################################################################

source $SUBBLOCK_ROOT/ooc_synth.tcl
