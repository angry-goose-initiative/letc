# ooc_synth.tcl
# Copyright (C) 2024 John Jekel
# See the LICENSE file at the root of the project for licensing info.
#
# Common TCL script for Vivado Out of Context synthesis
#
# https://docs.xilinx.com/r/en-US/ug892-vivado-design-flows-overview/Non-Project-Mode-Tcl-Script-Example
# https://docs.xilinx.com/r/2021.2-English/ug905-vivado-hierarchical-design/Out-Of-Context-Commands-and-Constraints

####################################################################################################
# Setup
####################################################################################################

set OUTPUT_DIR ./
file mkdir $OUTPUT_DIR

####################################################################################################
# Read Sources
####################################################################################################

read_verilog -sv $RTL_SOURCE
read_xdc $CONSTRAINTS_SOURCE

####################################################################################################
# Synthesize
####################################################################################################

synth_design -mode out_of_context -part xc7z007sclg400-1 -top $RTL_TOP
write_checkpoint -force $OUTPUT_DIR/post_synth
report_timing_summary -file $OUTPUT_DIR/post_synth_timing_summary.rpt
report_power -file $OUTPUT_DIR/post_synth_power.rpt
report_clock_networks -file $OUTPUT_DIR/post_synth_clock_networks.rpt

####################################################################################################
# Place
####################################################################################################

#opt_design
#opt_design -retarget -propconst -sweep -bufg_opt -mbufg_opt -remap -aggressive_remap -resynth_remap -muxf_remap -shift_register_opt -dsp_register_opt
opt_design -directive ExploreWithRemap
place_design
phys_opt_design
write_checkpoint -force $OUTPUT_DIR/post_place
report_timing_summary -file $OUTPUT_DIR/post_place_timing_summary.rpt
report_power -file $OUTPUT_DIR/post_place_power.rpt

####################################################################################################
# Route
####################################################################################################

route_design
write_checkpoint -force $OUTPUT_DIR/post_route
report_timing_summary -file $OUTPUT_DIR/post_route_timing_summary.rpt
report_timing -sort_by group -max_paths 100 -path_type summary -file $OUTPUT_DIR/post_route_timing.rpt
report_clock_utilization -file $OUTPUT_DIR/post_route_clock_util.rpt
report_utilization -file $OUTPUT_DIR/post_route_util.rpt
report_power -file $OUTPUT_DIR/post_route_power.rpt
report_drc -file $OUTPUT_DIR/post_route_drc.rpt

####################################################################################################
# Output Files
####################################################################################################

write_verilog -force $OUTPUT_DIR/output_netlist.v
write_xdc -no_fixed_only -force $OUTPUT_DIR/output_constraints.xdc

# No point in doing this for an OOC run
#write_bitstream -force $OUTPUT_DIR/output_bitstream.bit
