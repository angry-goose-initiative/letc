# Makefile
# Copyright (C) 2024 John Jekel
# Copyright (C) 2024 Eric Jessee
# See the LICENSE file at the root of the project for licensing info.
#
# Makefile for the letc/core/stage_e1 testbench

####################################################################################################
# Testbench Configuration
####################################################################################################

TBENCH_TOP  := letc_core_stage_e1_tb
RTL_SOURCES := \
    $(RTL_ROOT)/letc/letc_pkg.sv \
    $(RTL_ROOT)/letc/core/letc_core_pkg.sv \
    $(RTL_ROOT)/letc/core/letc_core_stage_e1.sv \
    $(RTL_ROOT)/letc/core/letc_core_tlb_if.sv \
    $(RTL_ROOT)/letc/core/letc_core_alu.sv

####################################################################################################
# Add Targets!
####################################################################################################

include $(TBENCH_ROOT)/nonuvm.mk
