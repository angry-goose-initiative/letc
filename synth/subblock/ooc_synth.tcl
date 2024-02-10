# ooc_synth.tcl
# Copyright (C) 2024 John Jekel
# See the LICENSE file at the root of the project for licensing info.
#
# Common TCL script for Vivado Out of Context synthesis
#
# https://docs.xilinx.com/r/en-US/ug892-vivado-design-flows-overview/Non-Project-Mode-Tcl-Script-Example
# https://docs.xilinx.com/r/2021.2-English/ug905-vivado-hierarchical-design/Out-Of-Context-Commands-and-Constraints

set OUTPUT_DIR ./build
file mkdir $OUTPUT_DIR

read_verilog -sv $RTL_SOURCE
