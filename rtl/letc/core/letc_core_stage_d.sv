/*
 * File:    letc_core_stage_d.sv
 * Brief:   LETC Core Decode Stage
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

module letc_core_stage_d
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

    //rs1 Read Port
    output reg_idx_t    o_rs1_idx,//Also goes to TGHM
    input  word_t       i_rs1_rdata,

    //rs2 Read Port
    output reg_idx_t    o_rs2_idx,//Also goes to TGHM
    input  word_t       i_rs2_rdata,

    //CSR Read Port
    output logic        o_csr_explicit_ren,
    output logic [11:0] o_csr_explicit_raddr,
    input  word_t       i_csr_explicit_rdata,
    output logic        o_csr_explicit_rill,

    //Branch signals
    output logic        o_branch_taken,
    output pc_word_t    o_branch_target,

    //From F2
    input f2_to_d_s i_f2_to_d,

    //To E1
    output d_to_e1_s o_d_to_e1
);

/* ------------------------------------------------------------------------------------------------
 * Instruction Field Extraction
 * --------------------------------------------------------------------------------------------- */

opcode_e opcode;
reg_idx_t rd_idx, rs1_idx, rs2_idx;
funct3_t funct3;
funct7_t funct7;

always_comb begin
    opcode  = opcode_e'(i_f2_to_d.instr[6:2]);

    rd_idx  = i_f2_to_d.instr[11:7];
    rs1_idx = i_f2_to_d.instr[19:15];
    rs2_idx = i_f2_to_d.instr[24:20];

    funct3  = i_f2_to_d.instr[14:12];
    funct7  = i_f2_to_d.instr[31:25];
end

/* ------------------------------------------------------------------------------------------------
 * RF Access
 * --------------------------------------------------------------------------------------------- */

always_comb begin
    o_rs1_idx = rs1_idx;
    o_rs2_idx = rs2_idx;
end

/* ------------------------------------------------------------------------------------------------
 * Output Flop Stage
 * --------------------------------------------------------------------------------------------- */

always_ff @(posedge i_clk) begin
    if (~i_rst_n) begin
        o_d_to_e1.valid <= 1'b0;
    end else begin
        o_d_to_e1.valid <= i_f2_to_d.valid;
    end
end

always_ff @(posedge i_clk) begin
    //TODO stall logic
    o_d_to_e1.pc_word   <= i_f2_to_d.pc_word;
    o_d_to_e1.rs1_rdata <= i_rs1_rdata;
    o_d_to_e1.rs2_rdata <= i_rs2_rdata;
    //TODO immediate
    //TODO opcode/other control signals
end

endmodule : letc_core_stage_d
