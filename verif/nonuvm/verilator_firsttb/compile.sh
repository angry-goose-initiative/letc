#!/bin/bash
#Based on script from vgacpu

FILES_TO_INCLUDE="-I ../../../rtl/letc/letc_top.sv"

#Verilate the testbench and vgacpu SystemVerilog files//todo split into multiple commands
verilator $FILES_TO_INCLUDE --timescale 1ns/1ns -DFIRSTTB_DUMPFILE_PATH=\"/tmp/verilator_firsttb.vcd\" --trace --trace-structs -Wall -Wno-fatal -sv -cc verilator_firsttb.sv --timing --exe --trace-fst -O3 --top-module verilator_firsttb +1800-2017ext+sv --build verilator_firsttb.cpp
#Run the simulation (creates /tmp/vgacpu_verilator.vcd)
#(cd ../../ && ./tb/verilator/obj_dir/Vverilator_firsttb)
./obj_dir/Vverilator_firsttb
#Open in waveform viewer
gtkwave /tmp/verilator_firsttb.vcd
#Delete files
#rm -rf ./obj_dir
#rm /tmp/verilator_firsttb.vcd
