#!/bin/bash
#Based on script from vgacpu

FILES="-I ../../../rtl/axi_pkg.svh"
FILES="$FILES -I ../../../verif/lib/behavioural_axi_memory.sv"

verilator $FILES --timescale 1ns/1ns -DDUMPFILE_PATH=\"/tmp/behavioural_memory_devel_tb.vcd\" --trace-threads 2 --trace-structs -Wall -Wno-fatal -sv -cc behavioural_memory_devel_tb.sv --timing --exe --trace-fst -O3 --top-module behavioural_memory_devel_tb +1800-2012ext+sv --build behavioural_memory_devel_tb.cpp
