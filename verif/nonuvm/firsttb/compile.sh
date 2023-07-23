#!/bin/bash

FILES="firsttb.sv ../../../rtl/letc/letc_top.sv"

iverilog -g2012 -s firsttb -o /tmp/firsttb -D 'FIRSTTB_DUMPFILE_PATH="/tmp/firsttb.vcd"' $FILES
