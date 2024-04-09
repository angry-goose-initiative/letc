# synthesis.tcl
# Copyright (C) 2024 John Jekel
# See the LICENSE file at the root of the project for licensing info.
#

####################################################################################################
# Variables from Makefile
####################################################################################################

set RTL_ROOT        [lindex $argv 0]
set SUBBLOCK_ROOT   [lindex $argv 1]
set BLOCK_PATH      [lindex $argv 2]

####################################################################################################
# Synthesis Config
####################################################################################################

set RTL_TOP letc_core_top
set CONSTRAINTS_SOURCE $SUBBLOCK_ROOT/usual.xdc
set RTL_SOURCE "
    $RTL_ROOT/common/sram/amd_lutram.sv
    $RTL_ROOT/common/counter/counter.sv
    $RTL_ROOT/common/shift_register/shift_register.sv
    $RTL_ROOT/common/axi/axi_pkg.sv
    $RTL_ROOT/common/axi/axi_if.sv
    $RTL_ROOT/letc/letc_pkg.sv
    $RTL_ROOT/letc/core/letc_core_pkg.sv
    $RTL_ROOT/letc/core/letc_core_top.sv
    $RTL_ROOT/letc/core/letc_core_rf.sv
    $RTL_ROOT/letc/core/letc_core_stage_f1.sv
    $RTL_ROOT/letc/core/letc_core_stage_f2.sv
    $RTL_ROOT/letc/core/letc_core_stage_d.sv
    $RTL_ROOT/letc/core/letc_core_stage_e1.sv
    $RTL_ROOT/letc/core/letc_core_stage_e2.sv
    $RTL_ROOT/letc/core/letc_core_stage_w.sv
    $RTL_ROOT/letc/core/letc_core_alu.sv
    $RTL_ROOT/letc/core/letc_core_branch_comparator.sv
    $RTL_ROOT/letc/core/letc_core_tghm.sv
    $RTL_ROOT/letc/core/letc_core_cache.sv
    $RTL_ROOT/letc/core/letc_core_tlb.sv
    $RTL_ROOT/letc/core/letc_core_mmu.sv
    $RTL_ROOT/letc/core/letc_core_csr.sv
    $RTL_ROOT/letc/core/letc_core_limp_if.sv
    $RTL_ROOT/letc/core/letc_core_tlb_if.sv
    $RTL_ROOT/letc/core/letc_core_axi_fsm.sv
"

####################################################################################################
# Run Out of Context Synthesis
####################################################################################################

source $SUBBLOCK_ROOT/ooc_synth.tcl
