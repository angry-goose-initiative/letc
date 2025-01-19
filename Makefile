#Main LETC Makefile :)

####################################################################################################
# Variables
####################################################################################################

REPO_ROOT := $(shell git rev-parse --show-toplevel)
INFRA_DIR := ${REPO_ROOT}/infra

BASH := /usr/bin/env bash

ifdef TARGET
	FILELIST := $(shell ${BASH} ${INFRA_DIR}/scripts/resolve_filelist.sh ${TARGET})
endif

####################################################################################################
# Rules
####################################################################################################

.PHONY: help
help:
	@echo "Welcome to LETC! :)"
	@echo "Available targets:"
	@echo "    help                   Display this help message"
	@echo "    clean                  Clean up temporary files"
	@echo "    ctags                  Generate a ctags file"
	@echo "    unit_iverilog          Run a unit simulation with Icarus Verilog (requires TARGET option, optionally WAVES option)"
	@echo "    unit_verilator         Run a unit simulation with Verilator (requires TARGET option, optionally WAVES option)"
	@echo "    unit_sv2v_verilator    Run a unit simulation with Verilator on sv2v'd inputs (requires TARGET option, optionally WAVES option)"
	@echo "    unit_xsim              Run a unit simulation with XSIM (requires TARGET option, optionally WAVES option)"
	@echo "    synth_vivado_ooc       Synthesize a module with Vivado in out-of-context mode (requires TARGET option)"
	@echo "    synth_yosys            Synthesize a module with Yosys (requires TARGET option)"
	@echo "    regression             Run a regression (single-threaded)"
	@echo "    regression_parallel    Multi-threaded using GNU Parallel"
	@echo "Options:"
	@echo "    TARGET                 Path to the filelist to simulate or synthesize"
	@echo "    WAVES                  Set equal to 1 to open waves after a simulation completes"
	@echo "Examples:"
	@echo "    make unit_verilator TARGET=filelists/verif/unit/tb/common/fifo/fifo_0r1w_tb.f"
	@echo "    make synth_vivado_ooc TARGET=filelists/rtl/common/fifo/fifo_0r1w.f"
	@echo "Information:"
	@echo "    REPO_ROOT:             ${REPO_ROOT}"
	@echo "    INFRA_DIR:             ${INFRA_DIR}"
	@echo "    BASH:                  ${BASH}"
	@echo "    TARGET:                ${TARGET}"
	@echo "    FILELIST:              ${FILELIST}"
	@echo "    WAVES:                 ${WAVES}"

include ${INFRA_DIR}/make/*.mk
