# Makefile
# Copyright (C) 2024 John Jekel
# See the LICENSE file at the root of the project for licensing info.
#
# Makefile for the letc/core testbench

####################################################################################################
# Testbench Configuration
####################################################################################################

TBENCH_TOP  := letc_core_tb
RTL_SOURCES := \
    $(RTL_ROOT)/common/axi/axi_pkg.sv \
    $(RTL_ROOT)/common/axi/axi_if.sv \
    $(RTL_ROOT)/letc/letc_pkg.sv \
    $(RTL_ROOT)/letc/core/letc_core_pkg.sv \
    $(RTL_ROOT)/letc/core/letc_core_top.sv \
    $(RTL_ROOT)/letc/core/letc_core_rf.sv \
    $(RTL_ROOT)/letc/core/letc_core_stage_f1.sv \
    $(RTL_ROOT)/letc/core/letc_core_stage_f2.sv \
    $(RTL_ROOT)/letc/core/letc_core_stage_d.sv \
    $(RTL_ROOT)/letc/core/letc_core_stage_e1.sv \
    $(RTL_ROOT)/letc/core/letc_core_stage_e2.sv \
    $(RTL_ROOT)/letc/core/letc_core_stage_w.sv \
    $(RTL_ROOT)/letc/core/letc_core_tghm.sv \
    $(RTL_ROOT)/letc/core/letc_core_cache.sv \
    $(RTL_ROOT)/letc/core/letc_core_tlb.sv \
    $(RTL_ROOT)/letc/core/letc_core_mmu.sv \
    $(RTL_ROOT)/letc/core/letc_core_csr.sv \
    $(RTL_ROOT)/letc/core/letc_core_axi_fsm.sv

####################################################################################################
# Add Targets!
####################################################################################################

include $(TBENCH_ROOT)/nonuvm.mk
