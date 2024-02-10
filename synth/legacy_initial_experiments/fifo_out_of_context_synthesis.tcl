#https://docs.xilinx.com/r/2021.2-English/ug905-vivado-hierarchical-design/Out-Of-Context-Commands-and-Constraints

set outputDir ./build
file mkdir $outputDir

read_verilog -sv fifo_0r1w.sv
synth_design -mode out_of_context -part xc7z007sclg400-1 -top fifo_0r1w -generic DWIDTH=128 -generic DEPTH=16

#read_verilog -sv fifo_1r1w.sv
#synth_design -part xc7z007sclg400-1 -top fifo_1r1w -generic DWIDTH=128 -generic DEPTH=16

create_clock -name clock -period 10 -waveform {0 5} [get_ports i_clk]
#create_clock -name clock -period 2 -waveform {0 1} [get_ports i_clk]

write_checkpoint -force $outputDir/post_synth
report_timing_summary -file $outputDir/post_synth_timing_summary.rpt
report_power -file $outputDir/post_synth_power.rpt

report_clock_networks
