# fc_synth.tcl
# Copyright (C) 2024 John Jekel
# See the LICENSE file at the root of the project for licensing info.
#
# TCL script for Vivado full chip synthesis
#
# https://docs.xilinx.com/r/en-US/ug892-vivado-design-flows-overview/Non-Project-Mode-Tcl-Script-Example
# https://docs.xilinx.com/r/en-US/ug896-vivado-ip/Scripting-Examples

####################################################################################################
# Settings
####################################################################################################

#Paths
set PROJECT_ROOT        [lindex $argv 0]
set RTL_ROOT            $PROJECT_ROOT/rtl
set FC_ROOT             $PROJECT_ROOT/synth/fc
set AMD_IP_ROOT         $PROJECT_ROOT/external_ip/amd
set AMD_IP_CONFIGS_ROOT $AMD_IP_ROOT/configurations
set OUTPUT_DIR          ./

#Other Settings
set RTL_TOP coraz7_top
set CONSTRAINTS_SOURCE $FC_ROOT/constraints.xdc
set RTL_SOURCE "
    $RTL_ROOT/common/fifo/fifo_0r0w.sv
    $RTL_ROOT/common/fifo/fifo_0r1w.sv
    $RTL_ROOT/common/fifo/fifo_1r1w.sv
    $RTL_ROOT/common/cdc/cdc_synchronizer.sv
    $RTL_ROOT/common/axi/axi_pkg.sv
    $RTL_ROOT/common/axi/axi_if.sv
    $RTL_ROOT/common/axi/axi_buffer.sv

    $RTL_ROOT/letc/letc_pkg.sv
    $RTL_ROOT/letc/letc_top.sv

    $RTL_ROOT/letc/core/letc_core_pkg.sv
    $RTL_ROOT/letc/core/letc_core_top.sv
    $RTL_ROOT/letc/core/letc_core_rf.sv
    $RTL_ROOT/letc/core/letc_core_stage_f1.sv
    $RTL_ROOT/letc/core/letc_core_stage_f2.sv
    $RTL_ROOT/letc/core/letc_core_stage_d.sv
    $RTL_ROOT/letc/core/letc_core_stage_e1.sv
    $RTL_ROOT/letc/core/letc_core_stage_e2.sv
    $RTL_ROOT/letc/core/letc_core_stage_w.sv
    $RTL_ROOT/letc/core/letc_core_tghm.sv
    $RTL_ROOT/letc/core/letc_core_cache.sv
    $RTL_ROOT/letc/core/letc_core_tlb.sv
    $RTL_ROOT/letc/core/letc_core_mmu.sv
    $RTL_ROOT/letc/core/letc_core_csr.sv
    $RTL_ROOT/letc/core/letc_core_limp_if.sv
    $RTL_ROOT/letc/core/letc_core_cache_if.sv
    $RTL_ROOT/letc/core/letc_core_tlb_if.sv
    $RTL_ROOT/letc/core/letc_core_axi_fsm.sv

    $RTL_ROOT/letc/matrix/letc_matrix_top.sv
    $RTL_ROOT/letc/matrix/letc_matrix_switch.sv
    $RTL_ROOT/letc/matrix/letc_matrix_default_subordinate.sv

    $RTL_ROOT/fpga_wrapper/coraz7_top.sv
"
set IP "
    letc_ps7
"
set IP_SOURCE "
    $AMD_IP_CONFIGS_ROOT/letc_ps7.xci
"

####################################################################################################
# Init
####################################################################################################

file mkdir $OUTPUT_DIR
create_project -in_memory -part xc7z007sclg400-1
set_property BOARD_PART digilentinc.com:cora-z7-07s:part0:1.1 [current_project]

####################################################################################################
# Generate IP From Configs
####################################################################################################

read_ip $IP_SOURCE
generate_target all [get_ips $IP]

#Needed so it doesn't assume a "dcp" has already been generated
set_property generate_synth_checkpoint false [get_files $IP_SOURCE]

####################################################################################################
# Read RTL Sources And Constraints
####################################################################################################

read_verilog -sv $RTL_SOURCE
read_xdc $CONSTRAINTS_SOURCE

####################################################################################################
# Synthesize
####################################################################################################

synth_design -part xc7z007sclg400-1 -top $RTL_TOP
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
write_bitstream -force $OUTPUT_DIR/output_bitstream.bit

#https://support.xilinx.com/s/question/0D52E00006hpPHtSAM/error-common-1769-command-failed-writehwplatform-is-only-supported-for-synthesized-implemented-or-checkpoint-designs
#open_checkpoint $OUTPUT_DIR/post_route.dcp
#set_property platform.name "letc_platform" [current_project]
#write_hw_platform -force $OUTPUT_DIR/output_hw_platform.xsa
