# Makefile
# Copyright (C) 2024 John Jekel
# See the LICENSE file at the root of the project for licensing info.
#
# Makefile for the common/axi/smoke testbench

####################################################################################################
# Testbench Configuration
####################################################################################################

TBENCH_TOP  := common_axi_smoke_tb
#We need the pkg before the tb, so no wildcard for us
RTL_SOURCES := $(RTL_ROOT)/common/axi/axi_pkg.sv $(RTL_ROOT)/common/axi/axi_if.sv
#RTL_SOURCES := $(wildcard $(RTL_ROOT)/common/axi/*.sv)

####################################################################################################
# Add Targets!
####################################################################################################

include $(TBENCH_ROOT)/nonuvm.mk
