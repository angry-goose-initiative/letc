/*
 * File:    letc_core_top.sv
 * Brief:   Top of LETC Core
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

//Hazard/backpressure signals
logic [5:0] stage_ready;
logic [5:0] stage_flush;
logic [5:0] stage_stall;

//Memory requests
//TODO probably make this into an interface
logic   [2:0]   valid;
logic   [2:0]   ready;
logic   [2:0]   wen_nren;//Write enable and not read enable
size_e  [2:0]   size;
paddr_t [2:0]   addr;
word_t  [2:0]   rdata;
word_t  [2:0]   wdata;

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

letc_core_stage_d stage_d (
    .*,

    //TODO

    //Hazard/backpressure signals
    .o_stage_ready(stage_ready[2]),
    .i_stage_flush(stage_flush[2]),
    .i_stage_stall(stage_stall[2]),

    //rs1 Read Port
    .o_rs1_idx(rs1_idx),
    .i_rs1_rdata(rs1_rdata),

    //rs2 Read Port
    .o_rs2_idx(rs2_idx),
    .i_rs2_rdata(rs2_rdata),

    //From F2
    .i_f2_to_d(f2_to_d),

    //To E1
    .o_d_to_e1(d_to_e1)
);

letc_core_stage_e1 stage_e1 (
    .*,

    //TODO

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
    .i_rd_idx(rd_idx),
    .i_rd_wdata(rd_wdata),
    .i_rd_wen(rd_wen),

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
    .o_stage_stall(stage_stall)

    //TODO
);

letc_core_cache l1icache (//TODO perhaps parameters for read only?
    .*

    //TODO design cache interface. Is it as simple as buffering LIMP accesses or something?
);

letc_core_cache l1dcache (
    .*

    //TODO design cache interface. Is it as simple as buffering LIMP accesses or something?
);

letc_core_tlb itlb (
    .*

    //TODO TLB interface to F1

    //TODO TLB interface to MMU
);

letc_core_tlb dtlb (
    .*

    //TODO TLB interface to E1

    //TODO TLB interface to MMU
);

letc_core_mmu mmu (
    .*

    //TODO design MMU interfaces
);

letc_core_axi_fsm axi_fsm (
    .*,

    .i_valid(valid),
    .o_ready(ready),
    .i_wen_nren(wen_nren),
    .i_size(size),
    .i_addr(addr),
    .o_rdata(rdata),
    .i_wdata(wdata)
);

endmodule : letc_core_top
