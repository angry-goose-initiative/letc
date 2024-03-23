# Makefile
# Copyright (C) 2024 John Jekel
# See the LICENSE file at the root of the project for licensing info.
#
# OOC Synthesis Makefile

PROJECT_ROOT  := $(abspath ../../)
RTL_ROOT      := $(PROJECT_ROOT)/rtl
SYNTH_ROOT    := $(PROJECT_ROOT)/synth
SUBBLOCK_ROOT := $(SYNTH_ROOT)/subblock

help:
	@echo "This is the Makefile for running out of context synthesis!"
	@echo ""
	@echo "Usage: make BLOCK="block/subdirs/synth_folder" {synth|clean}"
	@echo ""
	@echo "Information"
	@echo "Current Project Root:   $(PROJECT_ROOT)"
	@echo "Current RTL Root:       $(RTL_ROOT)"
	@echo "Current Synth Root:     $(SYNTH_ROOT)"
	@echo "Current Subblock Root:  $(SUBBLOCK_ROOT)"

.PHONY: synth
synth:
	@test -n "$(BLOCK)" || (echo "Can't synthesize without BLOCK set!" && exit 1)
	cd $(SUBBLOCK_ROOT)/$(BLOCK) && mkdir -p build
	cd $(SUBBLOCK_ROOT)/$(BLOCK)/build && vivado -mode batch -source $(SUBBLOCK_ROOT)/$(BLOCK)/synthesis.tcl -tclargs $(RTL_ROOT) $(SUBBLOCK_ROOT) $(SUBBLOCK_ROOT)/$(BLOCK)

.PHONY: clean
clean:
	@test -n "$(BLOCK)" || (echo "Can't clean without BLOCK set!" && exit 1)
	cd $(SUBBLOCK_ROOT)/$(BLOCK) && rm -rf build

