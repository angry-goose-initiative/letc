# Makefile
# Copyright (C) 2024 John Jekel
# See the LICENSE file at the root of the project for licensing info.
#
# AMD IP Generation Makefile

PROJECT_ROOT  := $(abspath ../../)

help:
	@echo "This is the Makefile for generating AMD IP!"
	@echo ""
	@echo "Usage: make ip IP="block/subdirs/synth_folder""
	@echo ""
	@echo "Information"
	@echo "Current Project Root: $(PROJECT_ROOT)"

.PHONY: ip
ip:
	@test -n "$(IP)" || (echo "Can't generate without IP set!" && exit 1)
	mkdir -p build
	cd build && vivado -mode batch -source ../generate_ip.tcl -tclargs $(IP) $(PROJECT_ROOT)/external_ip/amd/configurations/$(IP).xci

