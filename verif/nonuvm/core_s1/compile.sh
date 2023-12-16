#!/bin/bash
#Based on script from vgacpu

FILES="-I ../../../rtl/letc/letc_pkg.svh"
FILES="$FILES -I ../../../rtl/axi_pkg.svh"
FILES="$FILES -I ../../../rtl/letc/limp_pkg.svh"
FILES="$FILES -I ../../../rtl/letc/core/core_pkg.svh"
FILES="$FILES -I ../../../rtl/letc/core/s1/core_s1.sv"

#TODO this FPGA-specific stuff likely shouldn't be here
FILES="$FILES -I ../../../rtl/fpga_wrapper/intel_fpga_sram.sv"

verilator $FILES --timescale 1ns/1ns -DCORE_S1_TB_DUMPFILE_PATH=\"/tmp/core_s1_tb.vcd\" --trace-threads 2 --trace-structs -Wall -Wno-fatal -sv -cc core_s1_tb.sv --timing --exe --trace-fst -O3 --top-module core_s1_tb +1800-2012ext+sv --build core_s1_tb.cpp
