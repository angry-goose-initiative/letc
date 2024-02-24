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

set RTL_TOP letc_core_multiplier
set CONSTRAINTS_SOURCE $SUBBLOCK_ROOT/usual.xdc
set RTL_SOURCE "
    $RTL_ROOT/letc/letc_pkg.sv
    $RTL_ROOT/letc/core/letc_core_pkg.sv
    $RTL_ROOT/letc/core/letc_core_multiplier.sv
"

####################################################################################################
# Run Out of Context Synthesis
####################################################################################################

source $SUBBLOCK_ROOT/ooc_synth.tcl
