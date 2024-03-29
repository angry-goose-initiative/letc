# nonuvm.mk
# Copyright (C) 2024 John Jekel
# See the LICENSE file at the root of the project for licensing info.
#
# Common Makefile goodness for non-UVM testbenches

#TODO better incremental compilation, compile files in parallel, etc

TIMESCALE := "1ns/1ns"

TBENCH_PATH  := $(TBENCH_ROOT)/$(TBENCH)

OUTPUT_DIR   := $(TBENCH_PATH)/build

ifeq ($(SIMULATOR),verilator) # VERILATOR #########################################################

	OUTPUT_WAVES := $(OUTPUT_DIR)/verilator_waves.fst
	OUTPUT_EXE   := $(OUTPUT_DIR)/V$(TBENCH_TOP)

else ifeq ($(SIMULATOR),xsim) # XSIM ##############################################################

ifeq ($(WAVE_VIEWER),gtkwave)
	OUTPUT_WAVES := $(OUTPUT_DIR)/xsim_waves.vcd
else
	OUTPUT_WAVES := $(OUTPUT_DIR)/snapshot_$(TBENCH_TOP).wdb
endif

	OUTPUT_EXE   := $(OUTPUT_DIR)/xsim.dir/snapshot_$(TBENCH_TOP)

else ifeq ($(SIMULATOR),vsim) # VSIM ##############################################################

ifeq ($(WAVE_VIEWER),gtkwave)
	OUTPUT_WAVES := $(OUTPUT_DIR)/vsim_waves.vcd
else
	OUTPUT_WAVES := $(OUTPUT_DIR)/vsim_waves.wlf
endif

	OUTPUT_EXE   := $(OUTPUT_DIR)/work

else
	$(error "Unsupported simulator: $(SIMULATOR)")
endif

NUM_COMPILE_JOBS := 6

VERIF_SOURCES     := $(wildcard $(TBENCH_PATH)/*.v) $(wildcard $(TBENCH_PATH)/*.sv)
SOURCES           := $(RTL_SOURCES) $(VERIF_SOURCES)
VERILATOR_WRAPPER := $(TBENCH_ROOT)/verilator_wrapper.cpp
XSIM_TCL          := $(TBENCH_ROOT)/xsim.tcl

.PHONY: compile
compile: $(OUTPUT_EXE)

.PHONY: simulate
simulate: $(OUTPUT_WAVES)

.PHONY: waves
waves: $(OUTPUT_WAVES)
	@echo "\e[1mViewing testbench waves for testbench: \e[95m$(TBENCH)\e[0m"
	@echo "\e[1mPath: \e[95m$(OUTPUT_WAVES)\e[0m"

ifeq ($(SIMULATOR),verilator) # VERILATOR #########################################################

ifeq ($(WAVE_VIEWER),gtkwave)
	gtkwave $(OUTPUT_WAVES)
else
	@echo "Unsupported wave viewer: $(WAVE_VIEWER)"
endif

else ifeq ($(SIMULATOR),xsim) # XSIM ##############################################################

ifeq ($(WAVE_VIEWER),gtkwave)
	gtkwave $(OUTPUT_WAVES)
else
ifdef VIEW
	cd $(OUTPUT_DIR) && xsim --gui $(OUTPUT_WAVES) --view $(TBENCH_ROOT)/$(VIEW)
else
	cd $(OUTPUT_DIR) && xsim --gui $(OUTPUT_WAVES)
endif
endif

else ifeq ($(SIMULATOR),vsim) # VSIM ##############################################################

ifeq ($(WAVE_VIEWER),gtkwave)
	gtkwave $(OUTPUT_WAVES)
else
	cd $(OUTPUT_DIR) && vsim -view $(OUTPUT_WAVES)
endif

else
	$(error "Unsupported simulator: $(SIMULATOR)")
endif
	@echo "\e[1mFinished viewing testbench waves for testbench: \e[95m$(TBENCH)\e[0m"

.PHONY: clean
clean:
	@echo "\e[1mCleaning testbench: \e[96m$(TBENCH)\e[0m"
	rm -rf $(OUTPUT_DIR)
	@echo "\e[1mFinished cleaning testbench: \e[96m$(TBENCH)\e[0m"

$(OUTPUT_WAVES): $(OUTPUT_EXE)
	@echo "\e[1mSimulating testbench: \e[94m$(TBENCH)\e[0m"

ifeq ($(SIMULATOR),verilator) # VERILATOR #########################################################
	$(OUTPUT_EXE) +verilator+rand+reset+2

else ifeq ($(SIMULATOR),xsim) # XSIM ##############################################################

	cd $(OUTPUT_DIR) && xsim snapshot_$(TBENCH_TOP) --tclbatch $(XSIM_TCL)

else ifeq ($(SIMULATOR),vsim) # VSIM ##############################################################

	cd $(OUTPUT_DIR) && vsim -voptargs=+acc=npr -l transcript -c -do "vcd file $(OUTPUT_DIR)/vsim_waves.vcd; vcd add -r /*; run -all" $(TBENCH_TOP)
	-cd $(OUTPUT_DIR) && vcd2wlf $(OUTPUT_DIR)/vsim_waves.vcd $(OUTPUT_DIR)/vsim_waves.wlf

else
	$(error "Unsupported simulator: $(SIMULATOR)")
endif

	@echo "\e[1mFinished simulating testbench: \e[94m$(TBENCH)\e[0m"
	@echo "\e[1mWaves output: \e[94m$(OUTPUT_WAVES)\e[0m"

$(OUTPUT_EXE): $(SOURCES)
	@echo "\e[1mCompiling testbench: \e[92m$(TBENCH)\e[0m"
	@echo "\e[1mTop module: \e[92m$(TBENCH_TOP)\e[0m"

ifeq ($(SIMULATOR),verilator) # VERILATOR #########################################################

	verilator --exe --build --timing \
		--timescale $(TIMESCALE) +1800-2012ext+sv -sv -Wall -Wno-fatal -O3 -cc --assert \
		--trace-threads 2 --trace-structs --trace-fst \
		--build-jobs 4 \
		-DSIMULATION -DVERILATOR \
		-CFLAGS -O3 -CFLAGS -Wall -CFLAGS -Wextra \
		--top-module $(TBENCH_TOP) \
		-CFLAGS -DSV_TBENCH_NAME=$(TBENCH_TOP) -CFLAGS -DVERILATED_CLASS=V$(TBENCH_TOP) -CFLAGS -DVERILATED_HEADER=\"V$(TBENCH_TOP).h\" -CFLAGS -DWAVES_OUTPUT_PATH=$(OUTPUT_WAVES) \
		$(VERILATOR_WRAPPER) $(SOURCES) \
		--Mdir $(OUTPUT_DIR) \
		-o $(OUTPUT_EXE)

else ifeq ($(SIMULATOR),xsim) # XSIM ##############################################################

	mkdir -p $(OUTPUT_DIR)
	#TODO be more efficient by dong xvlog in parallel on all sources
	cd $(OUTPUT_DIR) && xvlog -d SIMULATION -d XSIM -sv $(SOURCES)
	cd $(OUTPUT_DIR) && xelab -timescale $(TIMESCALE) -debug all -top $(TBENCH_TOP) -snapshot snapshot_$(TBENCH_TOP)

else ifeq ($(SIMULATOR),vsim) # VSIM ##############################################################

	mkdir -p $(OUTPUT_DIR)
	cd $(OUTPUT_DIR) && vlog +define+SIMULATION +define+VSIM -lint -sv $(SOURCES)

else
	$(error "Unsupported simulator: $(SIMULATOR)")
endif

	@echo "\e[1mFinished compiling testbench: \e[92m$(TBENCH)\e[0m"
