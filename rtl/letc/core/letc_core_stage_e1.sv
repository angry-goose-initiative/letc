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
    output logic  o_stage_ready,
    input  logic  i_stage_flush,
    input  logic  i_stage_stall,

    //bypass signals
    input  logic  i_bypass_rs1,
    input  logic  i_bypass_rs2,
    input  word_t i_bypassed_rs1_data,
    input  word_t i_bypassed_rs2_data,

    //From D
    input d_to_e1_s i_d_to_e1,

    //To E2
    output e1_to_e2_s o_e1_to_e2
);

//ALU
letc_core_alu alu(.*);

word_t[1:0] i_alu_operands;
alu_op_e    i_alu_operation;
word_t      o_alu_result;

//rs1 and rs2 bypass muxing
word_t rs1;
word_t rs2;
always_comb begin
    rs1 = i_bypass_rs1 ? i_bypassed_rs1_data : i_d_to_e1.rs1_rdata;
    rs2 = i_bypass_rs1 ? i_bypassed_rs2_data : i_d_to_e1.rs2_rdata;
end

//ALU connections
//op1
always_comb begin
    unique case (i_d_to_e1.alu_op1_src)
        ALU_OP1_SRC_RS1:  i_alu_operands[0] = rs1;
        ALU_OP1_SRC_PC:   i_alu_operands[0] = i_d_to_e1.pc_word;
        ALU_OP1_SRC_CSR:  i_alu_operands[0] = i_d_to_e1.csr_rdata;
        ALU_OP1_SRC_ZERO: i_alu_operands[0] = 32'h0;
    endcase
end
//op2
always_comb begin
    unique case (i_d_to_e1.alu_op2_src)
        ALU_OP2_SRC_RS1:  i_alu_operands[1] = rs1;
        ALU_OP2_SRC_RS2:  i_alu_operands[1] = rs2;
        ALU_OP2_SRC_IMM:  i_alu_operands[1] = i_d_to_e1.immediate;
        ALU_OP2_SRC_FOUR: i_alu_operands[1] = 32'h4;
    endcase
end
//operation
always_comb begin
    i_alu_operation = i_d_to_e1.alu_op;
end

//tlb interface
//TODO tlb if logic will provide ready signal
//rest of stage is always ready
assign o_stage_ready = 1'b1;

//output flops
always_ff @(posedge i_clk) begin
    if (!i_rst_n) begin
        o_e1_to_e2.valid <= 1'b0;
    end else begin
        if (i_stage_flush) begin
            o_e1_to_e2.valid <= 1'b0;
        end else if (!i_stage_stall) begin
            o_e1_to_e2.valid <= i_d_to_e1.valid;
        end
    end
end

always_ff @(posedge i_clk) begin
    if (!i_stage_stall) begin
        //passthroughs
        o_e1_to_e2.rd_src <= i_d_to_e1.rd_src;
        o_e1_to_e2.rd_idx <= i_d_to_e1.rd_idx;
        o_e1_to_e2.rd_we  <= i_d_to_e1.rd_we;

        o_e1_to_e2.csr_op <= i_d_to_e1.csr_op;
        o_e1_to_e2.csr_idx <= i_d_to_e1.csr_idx;
        o_e1_to_e2.old_csr_value <= i_d_to_e1.csr_rdata;

        o_e1_to_e2.memory_op <= i_d_to_e1.memory_op;
        o_e1_to_e2.memory_signed <= i_d_to_e1.memory_signed;
        o_e1_to_e2.memory_size <= i_d_to_e1.memory_size;
        o_e1_to_e2.rs2_rdata <= i_d_to_e1.rs2_rdata;
        //modified outputs
        o_e1_to_e2.alu_result <= o_alu_result;
    end
end

`ifdef SIMULATION

assert property (@(posedge i_clk) disable iff (!i_rst_n) !(i_stage_flush && i_stage_stall));

`endif //SIMULATION

endmodule : letc_core_stage_e1
