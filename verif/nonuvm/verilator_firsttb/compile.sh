#!/bin/bash
#Based on script from vgacpu

FILES="-I ../../../rtl/letc/letc_pkg.svh"
FILES="$FILES -I ../../../rtl/letc/limp_pkg.svh"
FILES="$FILES -I ../../../rtl/letc/letc_top.sv"
FILES="$FILES -I ../../../rtl/letc/core/core_pkg.svh"
FILES="$FILES -I ../../../rtl/letc/core/core_top.sv"
FILES="$FILES -I ../../../rtl/letc/core/core_master_control.sv"
FILES="$FILES -I ../../../rtl/letc/core/core_csr_file.sv"
FILES="$FILES -I ../../../rtl/letc/core/core_mmu.sv"
FILES="$FILES -I ../../../rtl/letc/core/s1/core_s1.sv"
FILES="$FILES -I ../../../rtl/letc/core/s1/core_s1_control.sv"
FILES="$FILES -I ../../../rtl/letc/core/s2/core_s2.sv"
FILES="$FILES -I ../../../rtl/letc/core/s2/core_s2_alu.sv"
FILES="$FILES -I ../../../rtl/letc/core/s2/core_s2_alu_src_mux.sv"
FILES="$FILES -I ../../../rtl/letc/core/s2/core_s2_comparator.sv"
FILES="$FILES -I ../../../rtl/letc/core/s2/core_s2_control.sv"
FILES="$FILES -I ../../../rtl/letc/core/s2/core_s2_gen_imm.sv"
FILES="$FILES -I ../../../rtl/letc/core/s2/core_s2_reg_file.sv"
FILES="$FILES -I ../../../rtl/letc/core/s2/core_s2_reg_file_src_mux.sv"

#TODO this FPGA-specific stuff likely shouldn't be here
FILES="$FILES -I ../../../rtl/fpga_wrapper/intel_fpga_sram.sv"

verilator $FILES --timescale 1ns/1ns -DVERILATOR_FIRSTTB_DUMPFILE_PATH=\"/tmp/verilator_firsttb.vcd\" --trace-threads 2 --trace-structs -Wall -Wno-fatal -sv -cc verilator_firsttb.sv --timing --exe --trace-fst -O3 --top-module verilator_firsttb +1800-2012ext+sv --build verilator_firsttb.cpp
