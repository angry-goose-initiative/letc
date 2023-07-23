#!/bin/bash

FILES="firsttb.sv ../../../rtl/letc/letc_pkg.svh ../../../rtl/letc/letc_top.sv"
FILES="$FILES ../../../rtl/letc/core/core_top.sv"
FILES="$FILES ../../../rtl/letc/core/core_control.sv"

iverilog -g2012 -s firsttb -o /tmp/firsttb -D 'FIRSTTB_DUMPFILE_PATH="/tmp/firsttb.vcd"' $FILES
