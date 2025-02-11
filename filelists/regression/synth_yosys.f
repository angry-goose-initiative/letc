/* vi: set filetype=c: */
#pragma once
//TODO wrap the modules that have top-level interfaces so sv2v can support them

//Non-LETC-specific
//filelists/rtl/common/axi/axi_buffer.f
filelists/rtl/common/fifo/fifo_0r1w.f
filelists/rtl/common/sram/amd_bram.f

//Examples
filelists/rtl/example/example_top.f

//LETC-specific
//filelists/rtl/letc/core/letc_core_adhesive.f
filelists/rtl/letc/core/letc_core_alu.f
filelists/rtl/letc/core/letc_core_branch_comparator.f
filelists/rtl/letc/core/letc_core_bubble_wrap.f
//filelists/rtl/letc/core/letc_core_forwarding_factory.f
filelists/rtl/letc/core/letc_core_csrf.f
filelists/rtl/letc/core/letc_core_multiplier.f
filelists/rtl/letc/core/letc_core_rf.f
//filelists/rtl/letc/core/letc_core_stage_fetch1.f
//filelists/rtl/letc/core/letc_core_stage_fetch2.f
filelists/rtl/letc/core/letc_core_stage_decode.f
//filelists/rtl/letc/core/letc_core_stage_execute.f
//filelists/rtl/letc/core/letc_core_stage_memory1.f
//filelists/rtl/letc/core/letc_core_stage_memory2.f
//filelists/rtl/letc/core/letc_core_stage_writeback.f
