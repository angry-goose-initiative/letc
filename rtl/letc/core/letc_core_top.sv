/*
 * File:    letc_core_top.sv
 * Brief:   Top of LETC Core
 *  _     _____ _____ ____    ____
 * | |   | ____|_   _/ ___|  / ___|___  _ __ ___
 * | |   |  _|   | || |     | |   / _ \| '__/ _ \
 * | |___| |___  | || |___  | |__| (_) | | |  __/
 * |_____|_____| |_| \____|  \____\___/|_|  \___|
 *
 * Copyright:
 *  Copyright (C) 2023-2024 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_top
    import letc_pkg::*;
    import letc_core_pkg::*;
(
    //Clock and reset
    input logic i_clk,
    input logic i_rst_n,

    //IO
    axi_if.manager          axi,
    input logic             i_timer_irq_pending,
    input logic             i_external_irq_pending,

    //Debug (Logic Analyzer)
    output logic [7:0]      o_debug
);

/* ------------------------------------------------------------------------------------------------
 * Connections
 * --------------------------------------------------------------------------------------------- */

//rd Write Port
reg_idx_t   rd_idx;
word_t      rd_wdata;
logic       rd_wen;

//rs1 Read Port
reg_idx_t   rs1_idx;
word_t      rs1_rdata;

//rs2 Read Port
reg_idx_t   rs2_idx;
word_t      rs2_rdata;

//Inter-stage connections
f1_to_f2_s  f1_to_f2;
f2_to_d_s   f2_to_d;
d_to_e1_s   d_to_e1;
e1_to_e2_s  e1_to_e2;
e2_to_w_s   e2_to_w;

//Branch signals
logic       branch_taken;
pc_word_t   branch_target;

//Hazard/backpressure signals
logic [5:0] stage_ready;
logic [5:0] stage_flush;
logic [5:0] stage_stall;

//Bypass signals
//d1
logic  stage_d_bypass_rs1;
logic  stage_d_bypass_rs2;
word_t stage_d_bypass_rs1_rdata;
word_t stage_d_bypass_rs2_rdata;
//e1
logic  stage_e1_bypass_rs1;
logic  stage_e1_bypass_rs2;
word_t stage_e1_bypass_rs1_rdata;
word_t stage_e1_bypass_rs2_rdata;
//TODO any other stages that need bypassing

//Memory requests to the AXI FSM
letc_core_limp_if axi_fsm_limp[2:0](.*);

//Implicitly read CSRs by LETC Core logic, always valid
csr_implicit_rdata_s csr_implicit_rdata;

//Interface for CSRs whose state (at least partially) exists outside of letc_core_csr
//TODO

//CSR explicit software read interface
logic       csr_explicit_ren;
csr_idx_t   csr_explicit_ridx;
word_t      csr_explicit_rdata;
logic       csr_explicit_rill;

//CSR explicit software read interface
logic           csr_explicit_wen;
csr_idx_t       csr_explicit_widx;
word_t          csr_explicit_wdata;
logic           csr_explicit_will;

//Cache interfaces
letc_core_limp_if l1icache_limp(.*);
letc_core_limp_if l1dcache_limp(.*);

//TLB interfaces
letc_core_tlb_if itlb_if(.*);
letc_core_tlb_if dtlb_if(.*);

//Signal to flush all caches and TLBs
//TODO how to detect if the flush is complete?
logic global_cache_flush;

assign o_debug = d_to_e1[7:0];//TESTING

/* ------------------------------------------------------------------------------------------------
 * Module Instantiations
 * --------------------------------------------------------------------------------------------- */

letc_core_rf rf (
    .*,

    //rd Write Port
    .i_rd_idx(rd_idx),
    .i_rd_wdata(rd_wdata),
    .i_rd_wen(rd_wen),

    //rs1 Read Port
    .i_rs1_idx(rs1_idx),
    .o_rs1_rdata(rs1_rdata),

    //rs2 Read Port
    .i_rs2_idx(rs2_idx),
    .o_rs2_rdata(rs2_rdata)
);

letc_core_stage_f1 stage_f1 (
    .*,

    //TODO

    //Branch signals
    .i_branch_taken(branch_taken),
    .i_branch_target(branch_target),

    //TLB interface
    .itlb_if(itlb_if),

    //Hazard/backpressure signals
    .o_stage_ready(stage_ready[0]),
    .i_stage_flush(stage_flush[0]),
    .i_stage_stall(stage_stall[0]),

    //To F2
    .o_f1_to_f2(f1_to_f2)
);

letc_core_stage_f2 stage_f2 (
    .*,

    //TODO

    //Hazard/backpressure signals
    .o_stage_ready(stage_ready[1]),
    .i_stage_flush(stage_flush[1]),
    .i_stage_stall(stage_stall[1]),

    //From F1
    .i_f1_to_f2(f1_to_f2),

    //To D
    .o_f2_to_d(f2_to_d)
);

//FIXME why does XSIM act like stage_ready has multiple drivers
//unless we do this indirect assignment instead?
logic xsim_workaround_stage_d_ready;
assign stage_ready[2] = xsim_workaround_stage_d_ready;

letc_core_stage_d stage_d (
    .*,

    //Hazard/backpressure signals
    //.o_stage_ready(stage_ready[2]),
    .o_stage_ready(xsim_workaround_stage_d_ready),
    .i_stage_flush(stage_flush[2]),
    .i_stage_stall(stage_stall[2]),

    //rs1 Read Port
    .o_rs1_idx(rs1_idx),
    .i_rs1_rdata(rs1_rdata),

    //rs2 Read Port
    .o_rs2_idx(rs2_idx),
    .i_rs2_rdata(rs2_rdata),

    //Bypass signals
    .i_bypass_rs1(stage_d_bypass_rs1),
    .i_bypass_rs2(stage_d_bypass_rs2),
    .i_bypass_rs1_rdata(stage_d_bypass_rs1_rdata),
    .i_bypass_rs2_rdata(stage_d_bypass_rs2_rdata),

    //CSR Read Port
    .o_csr_explicit_ren(csr_explicit_ren),
    .o_csr_explicit_ridx(csr_explicit_ridx),
    .i_csr_explicit_rdata(csr_explicit_rdata),
    .i_csr_explicit_rill(csr_explicit_rill),

    //Branch signals
    .o_branch_taken(branch_taken),
    .o_branch_target(branch_target),

    //TODO signals for exceptions/cache flushing/etc
    //TODO any needed implicitly read CSRs

    //From F2
    .i_f2_to_d(f2_to_d),

    //To E1
    .o_d_to_e1(d_to_e1)
);

letc_core_stage_e1 stage_e1 (
    .*,

    //TLB interface (TODO)
    .dtlb_if(dtlb_if),

    //Bypass signals
    .i_bypass_rs1(stage_e1_bypass_rs1),
    .i_bypass_rs2(stage_e1_bypass_rs2),
    .i_bypassed_rs1_data(stage_e1_bypass_rs1_rdata),
    .i_bypassed_rs2_data(stage_e1_bypass_rs2_rdata),

    //Hazard/backpressure signals
    .o_stage_ready(stage_ready[3]),
    .i_stage_flush(stage_flush[3]),
    .i_stage_stall(stage_stall[3]),

    //From D
    .i_d_to_e1(d_to_e1),

    //To E2
    .o_e1_to_e2(e1_to_e2)
);

letc_core_stage_e2 stage_e2 (
    .*,

    //TODO

    //Hazard/backpressure signals
    .o_stage_ready(stage_ready[4]),
    .i_stage_flush(stage_flush[4]),
    .i_stage_stall(stage_stall[4]),

    //From E1
    .i_e1_to_e2(e1_to_e2),

    //To W
    .o_e2_to_w(e2_to_w)
);

letc_core_stage_w stage_w (
    .*,

    //TODO

    //Hazard/backpressure signals
    .o_stage_ready(stage_ready[5]),
    .i_stage_flush(stage_flush[5]),
    .i_stage_stall(stage_stall[5]),

    //rd Write Port
    .o_rd_idx(rd_idx),
    .o_rd_wdata(rd_wdata),
    .o_rd_wen(rd_wen),

    //CSR Write Port
    .o_csr_explicit_wen(csr_explicit_wen),
    .o_csr_explicit_widx(csr_explicit_widx),
    .o_csr_explicit_wdata(csr_explicit_wdata),
    .i_csr_explicit_will(csr_explicit_will),

    //From E2
    .i_e2_to_w(e2_to_w)
);

letc_core_tghm tghm (
    .*,

    //Interrupts
    //Passed through via .* above

    //Hazard/backpressure signals
    .i_stage_ready(stage_ready),
    .o_stage_flush(stage_flush),
    .o_stage_stall(stage_stall),

    //Register index signals for hazard detection
    //Even if we aren't actually reading registers, to be safe, we will still bypass/stall
    .i_stage_d_valid(f2_to_d.valid),
    .i_stage_d_rs1_idx(rs1_idx),
    .i_stage_d_rs2_idx(rs2_idx),
    .i_stage_e1_valid(d_to_e1.valid),
    .i_stage_e1_rs1_idx(d_to_e1.rs1_idx),
    .i_stage_e1_rs2_idx(d_to_e1.rs2_idx),
    .i_stage_e1_rd_we(d_to_e1.rd_we),
    .i_stage_e1_rd_idx(d_to_e1.rd_idx),
    .i_stage_e2_valid(e1_to_e2.valid),
    .i_stage_e2_rd_we(e1_to_e2.rd_we),
    .i_stage_e2_rd_idx(e1_to_e2.rd_idx),
    .i_stage_w_valid(e2_to_w.valid),
    .i_stage_w_rd_we(e2_to_w.rd_we),
    .i_stage_w_rd_idx(e2_to_w.rd_idx),

    //Bypass signals
    .o_stage_d_bypass_rs1(stage_d_bypass_rs1),
    .o_stage_d_bypass_rs2(stage_d_bypass_rs2),
    .o_stage_d_bypass_rs1_rdata(stage_d_bypass_rs1_rdata),
    .o_stage_d_bypass_rs2_rdata(stage_d_bypass_rs2_rdata),
    .o_stage_e1_bypass_rs1(stage_e1_bypass_rs1),
    .o_stage_e1_bypass_rs2(stage_e1_bypass_rs2),
    .o_stage_e1_bypass_rs1_rdata(stage_e1_bypass_rs1_rdata),
    .o_stage_e1_bypass_rs2_rdata(stage_e1_bypass_rs2_rdata),
    .i_stage_e2_alu_result(e1_to_e2.alu_result),
    .i_stage_w_rd_wdata(rd_wdata),

    //Signal to flush all caches and TLBs
    .o_global_cache_flush(global_cache_flush),

    //Branch snooping (to flush earlier stages on a branch)
    .i_branch_taken(branch_taken)

    //TODO
);

letc_core_cache l1icache (//TODO perhaps parameters for read only?
    .*,

    //Signal to flush all cache lines
    .i_flush_cache(global_cache_flush),

    //Cache interface (LIMP)
    .stage_limp(l1icache_limp),

    //LIMP interface to AXI FSM
    .axi_fsm_limp(axi_fsm_limp[0])
);

letc_core_cache l1dcache (
    .*,

    //Signal to flush all cache lines
    .i_flush_cache(global_cache_flush),

    //Cache interface (LIMP)
    .stage_limp(l1dcache_limp),

    //LIMP interface to AXI FSM
    .axi_fsm_limp(axi_fsm_limp[1])
);

letc_core_tlb itlb (
    .*,

    //TODO signal to flush

    //TLB interface
    .tlb_if(itlb_if)

    //TODO TLB interface to MMU
);

letc_core_tlb dtlb (
    .*,

    //TODO signal to flush

    //TLB interface
    .tlb_if(dtlb_if)

    //TODO TLB interface to MMU
);

letc_core_mmu mmu (
    .*,

    //TODO design MMU interfaces

    //LIMP interface
    .limp(axi_fsm_limp[2])
);

letc_core_csr csr (
    .*,

    //Implicitly read CSRs by LETC Core logic, always valid
    .o_csr_implicit_rdata(csr_implicit_rdata),

    //Interface for CSRs whose state (at least partially) exists outside of this module
    //TODO

    //CSR explicit software read interface
    .i_csr_explicit_ren(csr_explicit_ren),
    .i_csr_explicit_ridx(csr_explicit_ridx),
    .o_csr_explicit_rdata(csr_explicit_rdata),
    .o_csr_explicit_rill(csr_explicit_rill),

    //CSR explicit software read interface
    .i_csr_explicit_wen(csr_explicit_wen),
    .i_csr_explicit_widx(csr_explicit_widx),
    .i_csr_explicit_wdata(csr_explicit_wdata),
    .o_csr_explicit_will(csr_explicit_will)
);

letc_core_axi_fsm axi_fsm (
    .*,

    //Core IO
    //axi connected thanks to .* above

    //Internal Core Connections
    .limp(axi_fsm_limp)
);

endmodule : letc_core_top
