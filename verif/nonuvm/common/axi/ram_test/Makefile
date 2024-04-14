# Makefile
# Copyright (C) 2024 John Jekel
# See the LICENSE file at the root of the project for licensing info.
#
# Makefile for the common/axi/smoke testbench

####################################################################################################
# Testbench Configuration
####################################################################################################

TBENCH_TOP  := ram_test_tb
#We need the pkg before the tb, so no wildcard for us
RTL_SOURCES := \
    $(RTL_ROOT)/letc/letc_pkg.sv \
    $(RTL_ROOT)/letc/core/letc_core_pkg.sv \
    $(RTL_ROOT)/common/test_ram/test_ram.v \
    $(RTL_ROOT)/common/test_ram/blk_mem_gen_v8_4.v \
	$(RTL_ROOT)/common/axi/axi_pkg.sv \
	$(RTL_ROOT)/common/axi/axi_if.sv \
	$(RTL_ROOT)/letc/core/letc_core_limp_if.sv \
	$(RTL_ROOT)/letc/core/letc_core_axi_fsm.sv \

####################################################################################################
# Add Targets!
####################################################################################################

include $(TBENCH_ROOT)/nonuvm.mk
