#!/bin/bash

FILES="-I ../../../rtl/fifo.sv"

verilator $FILES --timescale 1ns/1ns -DDUMPFILE_PATH=\"/tmp/fifo_tb.vcd\" --trace-threads 2 --trace-structs -Wall -Wno-fatal -sv -cc fifo_tb.sv --timing --exe --trace-fst -O3 --top-module fifo_tb +1800-2012ext+sv --build fifo_tb.cpp
