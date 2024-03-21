/*
 * File:    letc_core_stage_f2.sv
 * Brief:   LETC Core 1st Fetch Stage
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

module letc_core_stage_f2
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

    //From F1
    input  f1_to_f2_s i_f1_to_f2,

    //To D
    output f2_to_d_s o_f2_to_d
);

//TESTING for starters, instead of a cache, we'll just have an instruction memory
//Two mem stages to ease timing
logic [31:0] instr_mem [1023:0];

logic [31:0] intermediate_mem_stage;

always_ff @(posedge i_clk) begin
    //TODO stalling logic
    //For testing preload the instruction mem with a test program
    intermediate_mem_stage <= instr_mem[i_f1_to_f2.fetch_addr[9:0]];
end

always_ff @(posedge i_clk) begin
    o_f2_to_d.instr <= intermediate_mem_stage[31:2];
end

initial begin
    //TEMPORARY for testing preload the instruction mem with a test program
    instr_mem[0] = 32'h00000013; //addi x0, x0, 0
end

endmodule : letc_core_stage_f2
