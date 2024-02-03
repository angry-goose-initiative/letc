#!/bin/bash

FILES="firsttb.sv ../../../rtl/letc/letc_pkg.svh ../../../rtl/letc/letc_top.sv"
FILES="$FILES ../../../rtl/letc/core/core_pkg.svh"
FILES="$FILES ../../../rtl/letc/core/core_top.sv"
FILES="$FILES ../../../rtl/letc/core/core_alu.sv"
FILES="$FILES ../../../rtl/letc/core/core_control.sv"
FILES="$FILES ../../../rtl/letc/core/core_decode.sv"
FILES="$FILES ../../../rtl/letc/core/core_gen_imm.sv"
FILES="$FILES ../../../rtl/letc/core/core_mmu.sv"
FILES="$FILES ../../../rtl/letc/core/core_reg_file.sv"

iverilog -g2012 -s firsttb -o /tmp/firsttb -D 'FIRSTTB_DUMPFILE_PATH="/tmp/firsttb.vcd"' $FILES
