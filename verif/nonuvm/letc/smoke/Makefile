# Makefile
# Copyright (C) 2024 John Jekel
# See the LICENSE file at the root of the project for licensing info.
#
# Makefile for the letc/smoke testbench

####################################################################################################
# Testbench Configuration
####################################################################################################

TBENCH_TOP  := smoke_tb
RTL_SOURCES := $(RTL_ROOT)/common/axi/axi_pkg.sv $(RTL_ROOT)/letc/letc_pkg.sv $(RTL_ROOT)/letc/core/letc_core_pkg.sv \
	$(RTL_ROOT)/common/axi/axi_if.sv $(RTL_ROOT)/letc/core/letc_core_top.sv $(RTL_ROOT)/letc/letc_top.sv

####################################################################################################
# Add Targets!
####################################################################################################

include $(TBENCH_ROOT)/nonuvm.mk
