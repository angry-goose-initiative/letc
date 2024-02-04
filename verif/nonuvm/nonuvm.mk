# nonuvm.mk
# Copyright (C) 2024 John Jekel
# See the LICENSE file at the root of the project for licensing info.
#
# Common Makefile goodness for non-UVM testbenches

TBENCH_PATH  := $(TBENCH_ROOT)/$(TBENCH)

OUTPUT_DIR   := $(TBENCH_PATH)/build
OUTPUT_EXE   := $(OUTPUT_DIR)/V$(TBENCH_TOP)
OUTPUT_WAVES := $(OUTPUT_DIR)/waves.fst

NUM_COMPILE_JOBS := 6

VERIF_SOURCES     := $(wildcard $(TBENCH_PATH)/*.v) $(wildcard $(TBENCH_PATH)/*.sv)
VERILATOR_WRAPPER := $(TBENCH_ROOT)/verilator_wrapper.cpp
SOURCES           := $(VERILATOR_WRAPPER) $(VERIF_SOURCES) $(RTL_SOURCES)

.PHONY: compile
compile: $(OUTPUT_EXE)

.PHONY: simulate
simulate: $(OUTPUT_WAVES)

.PHONY: waves
waves: $(OUTPUT_WAVES)
	@echo "\e[1mViewing testbench waves for testbench: \e[95m$(TBENCH)\e[0m"
	@echo "\e[1mPath: \e[95m$(OUTPUT_WAVES)\e[0m"
	$(WAVEVIEWER) $(OUTPUT_WAVES)
	@echo "\e[1mFinished viewing testbench waves for testbench: \e[95m$(TBENCH)\e[0m"

.PHONY: clean
clean:
	@echo "\e[1mCleaning testbench: \e[96m$(TBENCH)\e[0m"
	rm -rf $(OUTPUT_DIR)
	@echo "\e[1mFinished cleaning testbench: \e[96m$(TBENCH)\e[0m"

$(OUTPUT_WAVES): $(OUTPUT_EXE)
	@echo "\e[1mSimulating testbench: \e[94m$(TBENCH)\e[0m"
	$(OUTPUT_EXE) +verilator+rand+reset+2
	@echo "\e[1mFinished simulating testbench: \e[94m$(TBENCH)\e[0m"
	@echo "\e[1mWaves output: \e[94m$(OUTPUT_WAVES)\e[0m"

$(OUTPUT_EXE): $(SOURCES)
	@echo "\e[1mCompiling testbench: \e[92m$(TBENCH)\e[0m"
	@echo "\e[1mTop module: \e[92m$(TBENCH_TOP)\e[0m"
	$(VERILATOR) --exe --build --timing \
		--timescale 1ns/1ns +1800-2012ext+sv -sv -Wall -Wno-fatal -O3 -cc --assert \
		--trace-threads 2 --trace-structs --trace-fst \
		--build-jobs 4 \
		-DSIMULATION \
		-CFLAGS -O3 -CFLAGS -Wall -CFLAGS -Wextra \
		--top-module $(TBENCH_TOP) \
		-CFLAGS -DSV_TBENCH_NAME=$(TBENCH_TOP) -CFLAGS -DVERILATED_CLASS=V$(TBENCH_TOP) -CFLAGS -DVERILATED_HEADER=\"V$(TBENCH_TOP).h\" -CFLAGS -DWAVES_OUTPUT_PATH=$(OUTPUT_WAVES) \
		$(SOURCES) \
		--Mdir $(OUTPUT_DIR) \
		-o $(OUTPUT_EXE)
	@echo "\e[1mFinished compiling testbench: \e[92m$(TBENCH)\e[0m"
