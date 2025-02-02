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
 *  Copyright (C) 2023-2025 John Jekel
 *  Copyright (C) 2025 Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_top
    import riscv_pkg::*;
    import letc_pkg::*;
    import letc_core_pkg::*;
# (
    parameter STUB_MSS = 0//TODO use this parameter to decide to stub out the MSS blocks for verif
) (
    //Clock and reset
    input logic clk,
    input logic rst_n,

    //IO
    axi_if.manager          axi_instr,
    axi_if.manager          axi_data,
    input logic             timer_irq_pending,
    input logic             external_irq_pending,

    //Debug (Logic Analyzer)
    output logic [7:0]      o_debug
);

/* ------------------------------------------------------------------------------------------------
 * Connections
 * --------------------------------------------------------------------------------------------- */

//rd Write Port
reg_idx_t   rd_idx;
word_t      rd_val;
logic       rd_wen;

//rs1 Read Port
reg_idx_t   rs1_idx;
word_t      rs1_val;

//rs2 Read Port
reg_idx_t   rs2_idx;
word_t      rs2_val;

//Explicit CSR access
csr_idx_t    csr_de_expl_idx;
word_t       csr_de_expl_rdata;
logic        csr_de_expl_rill;
logic        csr_de_expl_will;

//Inter-stage connections
logic f1_to_f2_valid;
logic f2_to_d_valid;
logic d_to_e_valid;
logic e_to_m1_valid;
logic m1_to_m2_valid;
logic m2_to_w_valid;
f1_to_f2_s  f1_to_f2;
f2_to_d_s   f2_to_d;
d_to_e_s    d_to_e;
e_to_m1_s   e_to_m1;
m1_to_m2_s  m1_to_m2;
m2_to_w_s   m2_to_w;

//Implicitly read CSRs by LETC Core logic, always valid
csr_implicit_rdata_s csr_implicit_rdata;

//Hazard/backpressure signals
logic [6:0] stage_ready;
logic [6:0] stage_flush;
logic [6:0] stage_stall;

//MSS Interfaces
letc_core_imss_if imss_if (.*);
letc_core_dmss_if dmss_if (.*);

//Change the PC (useful for branches, exceptions, etc)
logic       pc_load_en;
pc_word_t   pc_load_val;

/*

//Branch signals
logic       branch_taken;
pc_word_t   branch_target;

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

*/

//assign o_debug = d_to_e1[7:0];//TESTING

/* ------------------------------------------------------------------------------------------------
 * Module Instantiations
 * --------------------------------------------------------------------------------------------- */

letc_core_rf rf (.*);

letc_core_imss imss (.*);

letc_core_dmss dmss (.*);

letc_core_stage_fetch1 stage_fetch1 (
    .*,

    //Hazard/backpressure signals
    .f1_ready(stage_ready[0]),
    .f1_flush(stage_flush[0]),
    .f1_stall(stage_stall[0])
);

letc_core_stage_fetch2 stage_fetch2 (
    .*,

    //Hazard/backpressure signals
    .f2_ready(stage_ready[1]),
    .f2_flush(stage_flush[1]),
    .f2_stall(stage_stall[1])
);

//FIXME why does XSIM act like stage_ready has multiple drivers
//unless we do this indirect assignment instead?
//logic xsim_workaround_stage_d_ready;
//assign stage_ready[2] = xsim_workaround_stage_d_ready;

letc_core_stage_decode stage_decode (
    .*,

    //Hazard/backpressure signals
    .d_ready(stage_ready[2]),
    .d_flush(stage_flush[2]),
    .d_stall(stage_stall[2]),

    // Register file read ports
    //TODO change letc_core_rf to match these names so we can just use .* for this too
    .rf_rs1_idx(rs1_idx),
    .rf_rs1_val(rs1_val),
    .rf_rs2_idx(rs2_idx),
    .rf_rs2_val(rs2_val)
);

letc_core_stage_execute stage_execute (
    .*,

    //Hazard/backpressure signals
    .e_ready(stage_ready[3]),
    .e_flush(stage_flush[3]),
    .e_stall(stage_stall[3])
);

letc_core_stage_memory1 stage_memory1 (
    .*,

    //Hazard/backpressure signals
    .m1_ready(stage_ready[4]),
    .m1_flush(stage_flush[4]),
    .m1_stall(stage_stall[4])
);

letc_core_stage_memory2 stage_memory2 (
    .*,

    //Hazard/backpressure signals
    .m2_ready(stage_ready[5]),
    .m2_flush(stage_flush[5]),
    .m2_stall(stage_stall[5])
);

/*
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
*/

endmodule : letc_core_top
