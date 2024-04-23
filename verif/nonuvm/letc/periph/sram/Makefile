# Makefile
# Copyright (C) 2024 John Jekel
# See the LICENSE file at the root of the project for licensing info.
#
# Makefile for the letc/periph/sram testbench

####################################################################################################
# Testbench Configuration
####################################################################################################

TBENCH_TOP  := letc_periph_sram_tb
RTL_SOURCES := \
    $(RTL_ROOT)/common/sram/amd_bram.sv \
    $(RTL_ROOT)/common/axi/axi_pkg.sv \
    $(RTL_ROOT)/common/axi/axi_if.sv \
    $(RTL_ROOT)/letc/letc_pkg.sv \
    $(RTL_ROOT)/letc/periph/letc_periph_sram.sv

####################################################################################################
# Add Targets!
####################################################################################################

include $(TBENCH_ROOT)/nonuvm.mk
