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
    //FIXME move these to a seperate interrupt controller module
    input logic i_timer_irq_pending,
    input logic i_external_irq_pending,

    //Hazard/backpressure signals
    input  logic [5:0] i_stage_ready,
    output logic [5:0] o_stage_flush,
    output logic [5:0] o_stage_stall,

    //Register index signals for hazard detection
    //Even if we aren't actually reading registers, to be safe, we will still bypass/stall
    input logic     i_stage_d_valid,//Decode is currently processing something (valid INTO d)
    input reg_idx_t i_stage_d_rs1_idx,
    input reg_idx_t i_stage_d_rs2_idx,
    input logic     i_stage_e1_valid,//Similar
    input reg_idx_t i_stage_e1_rs1_idx,
    input reg_idx_t i_stage_e1_rs2_idx,
    input logic     i_stage_e1_rd_we,
    input reg_idx_t i_stage_e1_rd_idx,
    input logic     i_stage_e2_valid,//Similar
    input logic     i_stage_e2_rd_we,
    input reg_idx_t i_stage_e2_rd_idx,
    input logic     i_stage_w_valid,//Similar
    input logic     i_stage_w_rd_we,
    input reg_idx_t i_stage_w_rd_idx,

    //Bypass signals
    //Only for general purpose registers; we will use stalling for CSR hazards
    output logic    o_stage_d_bypass_rs1,
    output logic    o_stage_d_bypass_rs2,
    output word_t   o_stage_d_bypass_rs1_rdata,
    output word_t   o_stage_d_bypass_rs2_rdata,
    output logic    o_stage_e1_bypass_rs1,
    output logic    o_stage_e1_bypass_rs2,
    output word_t   o_stage_e1_bypass_rs1_rdata,
    output word_t   o_stage_e1_bypass_rs2_rdata,
    input  word_t   i_stage_e2_alu_result,
    input  word_t   i_stage_w_rd_wdata,

    //Branch snooping (to flush earlier stages on a branch)
    input logic     i_branch_taken,

    //Signal to flush all caches and TLBs
    output logic o_global_cache_flush

    //TODO others
);

/* ------------------------------------------------------------------------------------------------
 * Exception Logic
 * --------------------------------------------------------------------------------------------- */

//TODO

/* ------------------------------------------------------------------------------------------------
 * CSR Stall/Flush Logic
 * --------------------------------------------------------------------------------------------- */

//TODO

/* ------------------------------------------------------------------------------------------------
 * Flush Logic
 * --------------------------------------------------------------------------------------------- */

//TODO deal with CSR flushing, fence/fence.i flushing
//always_comb begin//TODO flush F1, F2 on branches
assign o_stage_flush = '0;
//end

//TODO
assign o_global_cache_flush = 1'b0;

/* ------------------------------------------------------------------------------------------------
 * GPR Hazard Detection
 * --------------------------------------------------------------------------------------------- */

//See https://github.com/angry-goose-initiative/wiki/wiki/LETC-Core-Hazards#register-raw-hazards

//TODO as an additional optimization in the future, add register READ enables
//to avoid false positives. False hazards don't make things incorrect but will slow things down.
//The timing impact of read enable checking should be investigated.

//FIXME fundamentally broken, potentially each operand has a hazard from a different stage,
//but this doesn't allow for that!

logic stage_d_rs1_hazard_from_e1;
logic stage_d_rs2_hazard_from_e1;
logic stage_d_rs1_hazard_from_e2;
logic stage_d_rs2_hazard_from_e2;
//No hazards from w since the RF is guaranteed to read new data as opposed to old data
always_comb begin
    if (i_stage_d_valid && i_stage_e1_valid && i_stage_e1_rd_we && (i_stage_e1_rd_idx != 5'b0)) begin
        stage_d_rs1_hazard_from_e1 = (i_stage_d_rs1_idx == i_stage_e1_rd_idx);
        stage_d_rs2_hazard_from_e1 = (i_stage_d_rs2_idx == i_stage_e1_rd_idx);
    end else begin
        stage_d_hazard_from_e1 = 1'b0;
    end

    if (i_stage_d_valid && i_stage_e2_valid && i_stage_e2_rd_we && (i_stage_e2_rd_idx != 5'b0)) begin
        stage_d_hazard_from_e2 =
            (i_stage_d_rs1_idx == i_stage_e2_rd_idx) ||
            (i_stage_d_rs2_idx == i_stage_e2_rd_idx);
    end else begin
        stage_d_hazard_from_e2 = 1'b0;
    end
end

logic stage_e1_hazard_from_e2;
logic stage_e1_hazard_from_w;
always_comb begin
    if (i_stage_e1_valid && i_stage_e2_valid && i_stage_e2_rd_we && (i_stage_e2_rd_idx != 5'b0)) begin
        stage_e1_hazard_from_e2 =
            (i_stage_e1_rs1_idx == i_stage_e2_rd_idx) ||
            (i_stage_e1_rs2_idx == i_stage_e2_rd_idx);
    end else begin
        stage_e1_hazard_from_e2 = 1'b0;
    end

    if (i_stage_e1_valid && i_stage_w_valid && i_stage_w_rd_we && (i_stage_w_rd_idx != 5'b0)) begin
        stage_e1_hazard_from_w =
            (i_stage_e1_rs1_idx == i_stage_w_rd_idx) ||
            (i_stage_e1_rs2_idx == i_stage_w_rd_idx);
    end else begin
        stage_e1_hazard_from_w = 1'b0;
    end
end

/* ------------------------------------------------------------------------------------------------
 * GPR Bypass Logic
 * --------------------------------------------------------------------------------------------- */

//See https://github.com/angry-goose-initiative/wiki/wiki/LETC-Core-Hazards#register-raw-hazards

//FIXME fundamentally broken, potentially each operand has a hazard from a different stage,
//but this doesn't allow for that!

always_comb begin
    //We only ever bypass from the e1->e2 flop stage, so no need for a mux here!
    o_stage_d_bypass_rs1_rdata = i_stage_e2_alu_result;
    o_stage_d_bypass_rs2_rdata = i_stage_e2_alu_result;
    if (stage_d_hazard_from_e2) begin
        o_stage_d_bypass_rs1 = i_stage_d_rd_idx == i_stage_e2_rs1_idx;
        o_stage_d_bypass_rs2 = i_stage_d_rd_idx == i_stage_e2_rs2_idx;
    end else begin
        o_stage_d_bypass_rs1 = 1'b0;
        o_stage_d_bypass_rs2 = 1'b0;
    end

    //It's possible e1 has hazards with both e2 and w! If so, we always want
    //the newest data, so we priortize e2 over w here
    if (stage_e1_hazard_from_e2) begin
        o_stage_e1_bypass_rs1 = i_stage_e1_rd_idx == i_stage_e2_rs1_idx;
        o_stage_e1_bypass_rs2 = i_stage_e1_rd_idx == i_stage_e2_rs2_idx;

        o_stage_e1_bypass_rs1_rdata = i_stage_e2_alu_result;
        o_stage_e1_bypass_rs2_rdata = i_stage_e2_alu_result;
    end else if (stage_e1_hazard_from_w) begin
        o_stage_e1_bypass_rs1 = i_stage_e1_rd_idx == i_stage_w_rd_idx;
        o_stage_e1_bypass_rs2 = i_stage_e1_rd_idx == i_stage_w_rd_idx;

        o_stage_e1_bypass_rs1_rdata = i_stage_w_rd_wdata;
        o_stage_e1_bypass_rs2_rdata = i_stage_w_rd_wdata;
    end else begin
        o_stage_e1_bypass_rs1 = 1'b0;
        o_stage_e1_bypass_rs2 = 1'b0;

        o_stage_e1_bypass_rs1_rdata = '0;
        o_stage_e1_bypass_rs2_rdata = '0;
    end
end

/* ------------------------------------------------------------------------------------------------
 * Stalling Logic and Backpressure
 * --------------------------------------------------------------------------------------------- */

//Determine which stages need to be stalled individually
logic [5:0] stage_stalls;
always_comb begin
    //The base stalling criteria: stall a stage if it isn't ready
    stage_stalls = ~i_stage_ready;

    //TODO register hazard stalling may change in the future once bypassing is implemented

    //Decode stall criteria
    /*
    if (i_stage_d_valid) begin
        //TODO
    end
    */

    //TODO this stalling logic may need to be made more complicated in the future
    //(ex. stalling for hazards, not just downstream-stage-readiness)
end

//Propagate stalls backwards to backpressure stages and avoid losing data
logic [5:0] backpressured_stage_stall;
always_comb begin
    backpressured_stage_stall[5] = stage_stalls[5];
    for (int ii = 4; ii >= 0; --ii) begin
        backpressured_stage_stall[ii] = backpressured_stage_stall[ii+1] | stage_stalls[ii];
    end

    o_stage_stall = backpressured_stage_stall;
end

endmodule : letc_core_tghm
