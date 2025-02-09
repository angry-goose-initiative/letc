/*
 * File:    letc_core_multiplier.sv
 * Brief:   LETC Core Multiplier
 *
 * Copyright:
 *  Copyright (C) 2024 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * Simple 32-bit multiplier for LETC Core (64-bit product).
 *
 * Uses DSP slices to make this more feasible. Takes five cycles to compute results:
 * one input flop stage, and four multiplier stages.
 *
 * TODO support signed operands as well
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_multiplier
    import letc_pkg::*;
    import letc_core_pkg::*;
    import riscv_pkg::*;
(
    //Clock
    input logic i_clk,

    //Operands
    input logic         i_valid,
    input word_t [1:0]  i_operands,

    //Output
    output logic        o_valid,
    output word_t       o_result_upper,
    output word_t       o_result_lower
);

logic [4:0] stage_valid;

/* ------------------------------------------------------------------------------------------------
 * Input Flop Stage
 * --------------------------------------------------------------------------------------------- */

word_t [1:0] stage0_operands;

always_ff @(posedge i_clk) begin
    stage_valid[0]  <= i_valid;
    stage0_operands <= i_operands;
end

/* ------------------------------------------------------------------------------------------------
 * Multiplier
 * --------------------------------------------------------------------------------------------- */

logic [4:1] [63:0] stage_result;

always_ff @(posedge i_clk) begin
    stage_valid[1]  <= stage_valid[0];
    //Note, signed'(...) * unsigned DOES NOT WORK; verilog will treat both as
    //unsigned. Only signed * signed or unsigned * unsigned works unless we
    //explicitly do some sign stuff.
    stage_result[1] <= stage0_operands[0] * stage0_operands[1];

    for (int ii = 2; ii < 5; ++ii) begin
        stage_valid[ii]     <= stage_valid[ii-1];
        stage_result[ii]    <= stage_result[ii-1];
    end
end

/* ------------------------------------------------------------------------------------------------
 * Output
 * --------------------------------------------------------------------------------------------- */

always_comb begin
    o_valid         = stage_valid[4];
    o_result_upper  = stage_result[4][63:32];
    o_result_lower  = stage_result[4][31:0];
end

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

//TODO

`endif //SIMULATION

endmodule : letc_core_multiplier
