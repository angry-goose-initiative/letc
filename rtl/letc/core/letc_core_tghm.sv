/*
 * File:    letc_core_tghm.sv
 * Brief:   The Great Hazard Mitigator
 *
 * Copyright:
 *  Copyright (C) 2024 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * Deals with various pipeline hazards and mitigates them through stalling,
 * bypassing, and other means as appropriate.
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_tghm
    import letc_pkg::*;
    import letc_core_pkg::*;
(
    //Clock and reset
    input logic i_clk,
    input logic i_rst_n,

    //Interrupts
    input logic i_timer_irq_pending,
    input logic i_external_irq_pending,

    //Hazard/backpressure signals
    input  logic [5:0] i_stage_ready,
    output logic [5:0] o_stage_flush,
    output logic [5:0] o_stage_stall

    //Register index signals for hazard detection
    /*
    input logic     i_stage_d_rs1_ren,
    input reg_idx_t i_stage_d_rs1_idx,
    input logic     i_stage_d_rs2_ren,
    input reg_idx_t i_stage_d_rs2_idx,
    input logic     i_stage_d_rd_wen,
    input reg_idx_t i_stage_d_rd_idx,
    input logic     i_stage_e1_rs1_ren,
    input reg_idx_t i_stage_e1_rs1_idx,
    input logic     i_stage_e1_rs2_ren,
    input reg_idx_t i_stage_e1_rs2_idx,
    input logic     i_stage_e1_rd_wen,
    input reg_idx_t i_stage_e1_rd_idx,
    input logic     i_stage_e2_rs1_ren,
    input reg_idx_t i_stage_e2_rs1_idx,
    input logic     i_stage_e2_rs2_ren,
    input reg_idx_t i_stage_e2_rs2_idx,
    input logic     i_stage_e2_rd_wen,
    input reg_idx_t i_stage_e2_rd_idx,
    input logic     i_stage_w_rs1_ren,
    input reg_idx_t i_stage_w_rs1_idx,
    input logic     i_stage_w_rs2_ren,
    input reg_idx_t i_stage_w_rs2_idx,
    input logic     i_stage_w_rd_wen,
    input reg_idx_t i_stage_w_rd_idx
    */

    //TODO bypass signals for perf optimizations down the road

    //TODO others
);

//TODO this stalling logic may need to be made more complicated in the future
//(ex. stalling for hazards, not just downstream-stage-readiness)
logic [5:0] stage_stall;
always_comb begin
    stage_stall[5] = 1'b0;
    for (int ii = 4; ii >= 0; --ii) begin
        stage_stall[ii] = stage_stall[ii+1] | !i_stage_ready[ii+1];
    end
    o_stage_stall = stage_stall;
end

endmodule : letc_core_tghm
