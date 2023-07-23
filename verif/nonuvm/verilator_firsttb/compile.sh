#!/bin/bash
#Based on script from vgacpu

FILES="-I ../../../rtl/letc/letc_pkg.svh -I ../../../rtl/letc/letc_top.sv"
FILES="$FILES ../../../rtl/letc/core/core_top.sv"
FILES="$FILES ../../../rtl/letc/core/core_control.sv"

verilator $FILES --timescale 1ns/1ns -DVERILATOR_FIRSTTB_DUMPFILE_PATH=\"/tmp/verilator_firsttb.vcd\" --trace-threads 2 --trace-structs -Wall -Wno-fatal -sv -cc verilator_firsttb.sv --timing --exe --trace-fst -O3 --top-module verilator_firsttb +1800-2012ext+sv --build verilator_firsttb.cpp
