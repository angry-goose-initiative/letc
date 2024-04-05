/*
 * File:    letc_core_stage_e2.sv
 * Brief:   LETC Core 2nd Execute Stage
 *
 * Copyright:
 *  Copyright (C) 2024 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_stage_e2
    import letc_pkg::*;
    import letc_core_pkg::*;
(
    //Clock and reset
    input logic i_clk,
    input logic i_rst_n,

    //TODO

    //Hazard/backpressure signals
    output logic o_stage_ready,
    input  logic i_stage_flush,
    input  logic i_stage_stall,

    //From E1
    input e1_to_e2_s i_e1_to_e2,

    //To W
    output e2_to_w_s o_e2_to_w
);

/* ------------------------------------------------------------------------------------------------
 * Memory Access Logic
 * --------------------------------------------------------------------------------------------- */

logic memory_ready;
assign memory_ready = 1'b1;//TODO

//TODO implement data cache access stuffs here!
word_t memory_rdata;
assign memory_rdata = 32'hDEADBEEF;//TODO

/* ------------------------------------------------------------------------------------------------
 * Stage Readiness Logic
 * --------------------------------------------------------------------------------------------- */

logic stage_ready;
always_comb begin
    //TODO how do the flush/stall signals play into this?
    if (i_e1_to_e2.valid && (i_e1_to_e2.memory_op != MEM_OP_NOP) && !memory_ready) begin
        stage_ready = 1'b0;
    end else begin
        stage_ready = 1'b1;
    end

    o_stage_ready = stage_ready;
end

/* ------------------------------------------------------------------------------------------------
 * Output Flop Stage
 * --------------------------------------------------------------------------------------------- */

always_ff @(posedge i_clk) begin
    if (!i_rst_n) begin
        o_e2_to_w.valid <= 1'b0;
    end else begin
        if (!i_stage_stall) begin
            if (i_stage_flush || !stage_ready) begin//Invalidate the output/output isn't ready yet
                o_e2_to_w.valid <= 1'b0;
            end else begin//Chugging along, pun intended :)
                o_e2_to_w.valid <= i_e1_to_e2.valid;
            end
        end
    end
end

always_ff @(posedge i_clk) begin
    //Save resources by not resetting the datapath; which is fine since `valid` above is reset
    //if (i_f2_to_d.valid & !i_stage_stall) begin//More power efficient but worse for timing and area
    if (!i_stage_stall) begin
        o_e2_to_w.rd_src    <= i_e1_to_e2.rd_src;
        o_e2_to_w.rd_idx    <= i_e1_to_e2.rd_idx;
        o_e2_to_w.rd_we     <= i_e1_to_e2.rd_we;

        o_e2_to_w.csr_op    <= i_e1_to_e2.csr_op;
        o_e2_to_w.csr_idx   <= i_e1_to_e2.csr_idx;

        o_e2_to_w.old_csr_value <= i_e1_to_e2.old_csr_value;
        o_e2_to_w.alu_result    <= i_e1_to_e2.alu_result;
        o_e2_to_w.memory_rdata  <= memory_rdata;
    end
end

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

assert property (@(posedge i_clk) disable iff (!i_rst_n) !(i_stage_flush && i_stage_stall));

//TODO

`endif //SIMULATION

endmodule : letc_core_stage_e2
