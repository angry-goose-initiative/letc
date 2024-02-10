# https://docs.xilinx.com/r/en-US/ug892-vivado-design-flows-overview/Non-Project-Mode-Tcl-Script-Example
set outputDir ./build
file mkdir $outputDir

read_verilog -sv fifo_0r1w.sv
synth_design -part xc7z007sclg400-1 -top fifo_0r1w -generic DWIDTH=128 -generic DEPTH=16

#read_verilog -sv fifo_1r1w.sv
#synth_design -part xc7z007sclg400-1 -top fifo_1r1w -generic DWIDTH=128 -generic DEPTH=16

create_clock -name clock -period 10 -waveform {0 5} [get_ports i_clk]
#create_clock -name clock -period 2 -waveform {0 1} [get_ports i_clk]

write_checkpoint -force $outputDir/post_synth
report_timing_summary -file $outputDir/post_synth_timing_summary.rpt
report_power -file $outputDir/post_synth_power.rpt

report_clock_networks

opt_design
#opt_design -retarget -propconst -sweep -bufg_opt -mbufg_opt -remap -aggressive_remap -resynth_remap -muxf_remap -shift_register_opt -dsp_register_opt
report_timing_summary -file $outputDir/post_opt_timing_summary.rpt
report_power -file $outputDir/post_opt_power.rpt
write_checkpoint -force $outputDir/post_opt

place_design
phys_opt_design
write_checkpoint -force $outputDir/post_place
report_timing_summary -file $outputDir/post_place_timing_summary.rpt

route_design
write_checkpoint -force $outputDir/post_route
report_timing_summary -file $outputDir/post_route_timing_summary.rpt
report_timing -sort_by group -max_paths 100 -path_type summary -file $outputDir/post_route_timing.rpt
report_clock_utilization -file $outputDir/clock_util.rpt
report_utilization -file $outputDir/post_route_util.rpt
report_power -file $outputDir/post_route_power.rpt
report_drc -file $outputDir/post_imp_drc.rpt
write_verilog -force $outputDir/bft_impl_netlist.v
write_xdc -no_fixed_only -force $outputDir/bft_impl.xdc
