# Makefile
# Copyright (C) 2024 John Jekel
# See the LICENSE file at the root of the project for licensing info.
#
# Makefile for the letc/core/gen_imm testbench

####################################################################################################
# Testbench Configuration
####################################################################################################

TBENCH_TOP  := letc_core_cache_tb
RTL_SOURCES := \
    $(RTL_ROOT)/common/sram/amd_lutram.sv \
    $(RTL_ROOT)/letc/letc_pkg.sv \
    $(RTL_ROOT)/letc/core/letc_core_pkg.sv \
    $(RTL_ROOT)/letc/core/letc_core_limp_if.sv \
    $(RTL_ROOT)/letc/core/letc_core_cache.sv

####################################################################################################
# Add Targets!
####################################################################################################

include $(TBENCH_ROOT)/nonuvm.mk
