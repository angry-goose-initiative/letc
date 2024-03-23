/*
 * File:    letc_core_stage_f1.sv
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

module letc_core_stage_f1
    import letc_pkg::*;
    import letc_core_pkg::*;
(
    //Clock and reset
    input logic i_clk,
    input logic i_rst_n,

    //TODO others

    //Branch signals
    input logic     i_branch_taken,
    input pc_word_t i_branch_target,

    //TLB interface
    letc_core_tlb_if.stage itlb_if,

    //Hazard/backpressure signals
    output logic o_stage_ready,
    input  logic i_stage_flush,
    input  logic i_stage_stall,

    //To F2
    output f1_to_f2_s o_f1_to_f2
);

//TODO stall PC logic if tlb not ready
//TODO stall logic if F2 not ready

/* ------------------------------------------------------------------------------------------------
 * PC Logic
 * --------------------------------------------------------------------------------------------- */

pc_word_t pc_word, next_pc_word, next_seq_pc_word;

assign next_seq_pc_word = pc_word + 29'h1;

always_comb begin
    next_pc_word = next_seq_pc_word;//TODO this will vary
end

always_ff @(posedge i_clk) begin
    if (~i_rst_n) begin
        pc_word <= RESET_PC_WORD;
    end else begin
        pc_word <= next_pc_word;
    end
end

/* ------------------------------------------------------------------------------------------------
 * Virtual Address Translation
 * --------------------------------------------------------------------------------------------- */

//To mask latency it should be a function of next_pc_word

paddr_t translated_fetch_addr;

//TODO
assign translated_fetch_addr = {pc_word, 2'h0};//TEMPORARY

/* ------------------------------------------------------------------------------------------------
 * Output To F2
 * --------------------------------------------------------------------------------------------- */

//FIXME is this latency correct or should it be delayed by a cycle?
always_comb begin
    o_f1_to_f2.valid        = 1'b1;//TODO deassert if tlb not ready
    o_f1_to_f2.pc_word      = pc_word;
    o_f1_to_f2.fetch_addr   = translated_fetch_addr;
end

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

word_t pc, next_seq_pc;//Useful for debugging
assign pc = {pc_word, 2'h0};
assign next_seq_pc = {next_seq_pc_word, 2'h0};

//TODO

//TODO also in simulation init registers to 32'hDEADBEEF to aid debugging

`endif

endmodule : letc_core_stage_f1
