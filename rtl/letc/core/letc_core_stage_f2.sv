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

always_ff @(posedge i_clk) begin
    //TODO stalling logic
    //For testing preload the instruction mem with a test program
    if (!i_rst_n) begin
        o_f2_to_d.valid <= 1'b0;
    end else begin
        o_f2_to_d.valid <= i_f1_to_f2.valid;
    end
end

always_ff @(posedge i_clk) begin
    o_f2_to_d.pc_word <= i_f1_to_f2.pc_word;
    o_f2_to_d.instr <= instr_mem[i_f1_to_f2.fetch_addr[11:2]][31:2];
end

initial begin//TESTING this is not synthesizable (except on FPGA kinda sorta)
    for (int i = 0; i < 1024; ++i) begin
        instr_mem[i] = 32'hDEADBEEF;
    end

    //TEMPORARY for testing preload the instruction mem with a test program
    instr_mem[0] = 32'h00000013;//addi x0, x0, 0
    instr_mem[1] = 32'habcd1117;//auipc sp, 0xabcd1
    instr_mem[2] = 32'hfc20e6e3;//bltu x1, x2, offset -0x34
end

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

word_t nice_instr_out = {o_f2_to_d.instr, 2'b11};

assert property (@(posedge i_clk) disable iff (!i_rst_n) !(i_stage_flush && i_stage_stall));

//TODO more

`endif //SIMULATION

endmodule : letc_core_stage_f2
