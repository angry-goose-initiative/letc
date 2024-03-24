/*
 * File:    letc_core_stage_e1.sv
 * Brief:   LETC Core 1st Execute Stage
 *
 * Copyright:
 *  Copyright (C) 2024 John Jekel
 *  Copytight (C) 2024 Eric Jessee
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_stage_e1
    import letc_pkg::*;
    import letc_core_pkg::*;
(
    //Clock and reset
    input logic i_clk,
    input logic i_rst_n,

    //TODO

    //TLB interface
    letc_core_tlb_if.stage dtlb_if,

    //Hazard/backpressure signals
    output logic o_stage_ready,
    input  logic i_stage_flush,
    input  logic i_stage_stall,

    //From D
    input d_to_e1_s i_d_to_e1,

    //To E2
    output e1_to_e2_s o_e1_to_e2
);

//Temporary stubs
assign o_e1_to_e2.valid = 1'b0;//TODO

//ALU
letc_core_alu alu(.*);

word_t[1:0] i_alu_operands;
alu_op_e i_alu_operation;
word_t o_alu_result;

always_ff @(posedge i_clk) begin
    if (i_d_to_e1.valid) begin
        i_alu_operation <= ALU_OP_ADD;
        i_alu_operands[1] <= i_d_to_e1.rs2_rdata;
        i_alu_operands[0] <= i_d_to_e1.rs1_rdata;
        o_e1_to_e2.alu_result <= o_alu_result;
    end
    else begin
        i_alu_operation <= ALU_OP_DO_NOTHING; //should output 0xdeadbeef
        i_alu_operands[0] <= 32'h0;
        i_alu_operands[1] <= 32'h0;
        o_e1_to_e2.alu_result <= o_alu_result;
    end
end

endmodule : letc_core_stage_e1
