# Makefile
# Copyright (C) 2024 John Jekel
# See the LICENSE file at the root of the project for licensing info.
#
# Non-UVM Testbenches Makefile

VERILATOR    := verilator
WAVEVIEWER   := gtkwave
PROJECT_ROOT := $(abspath ../../)
RTL_ROOT     := $(PROJECT_ROOT)/rtl
VERIF_ROOT   := $(PROJECT_ROOT)/verif
TBENCH_ROOT  := $(VERIF_ROOT)/nonuvm

export

help:
	@echo "This is the Makefile for running the non-UVM testbenches!"
	@echo ""
	@echo "Usage: make TBENCH="block/subdirs/tbench_folder" {compile|simulate|waves|clean}"
	@echo ""
	@echo "Information"
	@echo "Current Project Root:   $(PROJECT_ROOT)"
	@echo "Current Testbench Root: $(TBENCH_ROOT)"

.PHONY: compile
compile:
	@test -n "$(TBENCH)" || (echo "Can't compile without TBENCH set!" && exit 1)
	@$(MAKE) -C $(TBENCH_ROOT)/$(TBENCH) compile

.PHONY: simulate
simulate:
	@test -n "$(TBENCH)" || (echo "Can't simulate without TBENCH set!" && exit 1)
	@$(MAKE) -C $(TBENCH_ROOT)/$(TBENCH) simulate

.PHONY: waves
waves:
	@test -n "$(TBENCH)" || (echo "Can't view waves without TBENCH set!" && exit 1)
	@$(MAKE) -C $(TBENCH_ROOT)/$(TBENCH) waves

.PHONY: clean
clean:
	@test -n "$(TBENCH)" || (echo "Can't clean without TBENCH set!" && exit 1)
	@$(MAKE) -C $(TBENCH_ROOT)/$(TBENCH) clean
