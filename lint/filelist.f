# filelist.f
# Copyright (C) 2024 John Jekel
# See the LICENSE file at the root of the project for licensing info.
#
# Lint file list

templates/systemverilog.sv

####################################################################################################
# RTL
####################################################################################################

rtl/common/fifo/fifo_0r0w.sv
rtl/common/fifo/fifo_0r1w.sv
rtl/common/fifo/fifo_1r1w.sv
rtl/common/cdc/cdc_synchronizer.sv
rtl/common/axi/axi_pkg.sv
rtl/common/axi/axi_if.sv
rtl/common/axi/axi_buffer.sv

rtl/letc/letc_pkg.sv
rtl/letc/letc_top.sv

rtl/letc/core/letc_core_pkg.sv
rtl/letc/core/letc_core_top.sv
rtl/letc/core/letc_core_rf.sv
rtl/letc/core/letc_core_stage_f1.sv
rtl/letc/core/letc_core_stage_f2.sv
rtl/letc/core/letc_core_stage_d.sv
rtl/letc/core/letc_core_stage_e1.sv
rtl/letc/core/letc_core_stage_e2.sv
rtl/letc/core/letc_core_stage_w.sv
rtl/letc/core/letc_core_tghm.sv
rtl/letc/core/letc_core_cache.sv
rtl/letc/core/letc_core_tlb.sv
rtl/letc/core/letc_core_mmu.sv
rtl/letc/core/letc_core_csr.sv
rtl/letc/core/letc_core_limp_if.sv
rtl/letc/core/letc_core_tlb_if.sv
rtl/letc/core/letc_core_axi_fsm.sv

rtl/letc/matrix/letc_matrix_top.sv
rtl/letc/matrix/letc_matrix_switch.sv
rtl/letc/matrix/letc_matrix_default_subordinate.sv

rtl/letc/periph/letc_periph_gpio.sv
rtl/letc/periph/letc_periph_sram.sv

#We have to break convention here since we interact with AMD IP
#TODO fine-grained waivers
#rtl/fpga_wrapper/coraz7_top.sv

####################################################################################################
# Verif Non-UVM
####################################################################################################

verif/nonuvm/smoke_tb.sv

verif/nonuvm/common/fifo/fifo_0r1w/fifo_0r1w_tb.sv

verif/nonuvm/example/example_tb.sv

verif/nonuvm/letc/core/letc_core_tb.sv
verif/nonuvm/letc/core/alu/letc_core_alu_tb.sv
verif/nonuvm/letc/core/branch_comparator/letc_core_branch_comparator_tb.sv
verif/nonuvm/letc/core/stage_d/letc_core_stage_d_tb.sv
verif/nonuvm/letc/core/stage_e1/letc_core_stage_e1_tb.sv

verif/nonuvm/letc/periph/gpio/letc_periph_gpio_tb.sv
verif/nonuvm/letc/periph/sram/letc_periph_sram_tb.sv
