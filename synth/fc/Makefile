# Makefile
# Copyright (C) 2024 John Jekel
# See the LICENSE file at the root of the project for licensing info.
#
# Full Chip Synthesis Makefile

PROJECT_ROOT  := $(abspath ../../)
RTL_ROOT      := $(PROJECT_ROOT)/rtl
SYNTH_ROOT    := $(PROJECT_ROOT)/synth
FC_ROOT       := $(SYNTH_ROOT)/fc

help:
	@echo "This is the Makefile for running full chip synthesis!"
	@echo ""
	@echo "Usage: make synth"
	@echo ""
	@echo "Information"
	@echo "Current Project Root:   $(PROJECT_ROOT)"

.PHONY: synth
synth:
	cd $(FC_ROOT) && mkdir -p build
	cd $(FC_ROOT)/build && vivado -mode batch -source $(FC_ROOT)/fc_synth.tcl -tclargs $(PROJECT_ROOT)

