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
	@echo "    unit_regression        Run a unit regression (single-threaded)"
	@echo "    unit_regression_par    Run a multi-threaded unit regression using GNU Parallel"
	@echo "    synth_regression       Run a synthesis regression (single-threaded)"
	@echo "    synth_regression_par   Run a multi-threaded synthesis regression using GNU Parallel"
	@echo "    svlint                 Run the svlint linting tool"
	@echo "    verible                Run the verible linting tool"
	@echo "    software               Build software to run on the core"
	@echo "    irve                   Build IRVE with modifications for LETC, to serve as a reference model"
	@echo "    stubmss_build          Build the stubmss testbench to run test programs on the core"
	@echo "    stubmss_run            Run a test program in stubmss mode (requires PROGRAM option, optionally WAVES option)"
	@echo "    stubmss_check          Run a test program in stubmss mode, run it with IRVE, and diff the results (requires PROGRAM option, optionally WAVES option)"
	@echo "Options:"
	@echo "    TARGET                 Path to the filelist to simulate or synthesize"
	@echo "    WAVES                  Set equal to 1 to open waves after a simulation completes"
	@echo "    PROGRAM                Path to the program to run on the core"
	@echo "Examples:"
	@echo "    make unit_verilator TARGET=filelists/verif/unit/tb/common/fifo/fifo_0r1w_tb.f"
	@echo "    make synth_vivado_ooc TARGET=filelists/rtl/common/fifo/fifo_0r1w.f"
	@echo "    make software stubmss_build stubmss_run PROGRAM=build/software/rvsw/src/single_file/asm/jzjcoresoftware/nop.vhex8 WAVES=1"
	@echo "    make irve software stubmss_build stubmss_check PROGRAM=build/software/rvsw/src/single_file/asm/jzjcoresoftware/adding2.vhex8"
	@echo "Information:"
	@echo "    REPO_ROOT:             ${REPO_ROOT}"
	@echo "    INFRA_DIR:             ${INFRA_DIR}"
	@echo "    BASH:                  ${BASH}"
	@echo "    TARGET:                ${TARGET}"
	@echo "    FILELIST:              ${FILELIST}"
	@echo "    WAVES:                 ${WAVES}"
	@echo "    PROGRAM:               ${PROGRAM}"

include ${INFRA_DIR}/make/*.mk
