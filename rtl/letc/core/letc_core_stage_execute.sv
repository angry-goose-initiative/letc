/*
 * File:    letc_core_stage_execute.sv
 * Brief:   LETC Core Execute Stage
 *
 * Copyright:
 *  Copyright (C) 2024-2025 John Jekel
 *  Copytight (C) 2024 Eric Jessee
 *  Copytight (C) 2025 Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_stage_execute
    import riscv_pkg::*;
    import letc_pkg::*;
    import letc_core_pkg::*;
(
    //Clock and reset
    input logic clk,
    input logic rst_n,

    //TODO forwarding IF

    //Hazard/backpressure signals
    output logic e_ready,
    input  logic e_flush,
    input  logic e_stall,

    //From D
    input   logic       d_to_e_valid,
    input   d_to_e_s    d_to_e,

    //To E2
    output  logic       e_to_m1_valid,
    output  e_to_m1_s   e_to_m1
);

/* ------------------------------------------------------------------------------------------------
 * Input Flop Stage
 * --------------------------------------------------------------------------------------------- */

logic    d_to_e_valid_ff;
d_to_e_s d_to_e_ff;

always_ff @(posedge clk) begin
    if (!rst_n) begin
        d_to_e_valid_ff <= 1'b0;
    end else begin
        if (!e_stall) begin
            d_to_e_valid_ff <= d_to_e_valid;
        end
    end
end

always_ff @(posedge clk) begin
    if (!e_stall) begin
        d_to_e_ff <= d_to_e;
    end
end

assign e_ready = 1'b1; // TODO: Will not be ready during multicycle multiply

/* ------------------------------------------------------------------------------------------------
 * Arithmetic
 * --------------------------------------------------------------------------------------------- */

//ALU
word_t  [1:0]   alu_operands;
alu_op_e        alu_operation;
word_t          alu_result;

letc_core_alu alu (.*);

//rs1 and rs2 bypass muxing
word_t rs1_val;
word_t rs2_val;
always_comb begin
    //TODO bypass logic
    rs1_val = /* bypass_rs1 ? bypassed_rs1_data : */ d_to_e_ff.rs1_val;
    rs2_val = /* bypass_rs1 ? bypassed_rs2_data : */ d_to_e_ff.rs2_val;
end

//ALU connections
//op1
always_comb begin
    unique case (d_to_e_ff.alu_op1_src)
        ALU_OP1_SRC_RS1:  alu_operands[0] = rs1_val;
        ALU_OP1_SRC_PC:   alu_operands[0] = {d_to_e_ff.pc_word, 2'h0};
        ALU_OP1_SRC_CSR:  alu_operands[0] = d_to_e_ff.csr_old_val;
        ALU_OP1_SRC_ZERO: alu_operands[0] = 32'h0;
    endcase
end
//op2
always_comb begin
    unique case (d_to_e_ff.alu_op2_src)
        ALU_OP2_SRC_RS1:  alu_operands[1] = rs1_val;
        ALU_OP2_SRC_RS2:  alu_operands[1] = rs2_val;
        ALU_OP2_SRC_IMM:  alu_operands[1] = d_to_e_ff.immediate;
        ALU_OP2_SRC_FOUR: alu_operands[1] = 32'h4;
    endcase
end
//operation
always_comb begin
    alu_operation = d_to_e_ff.alu_op;
end

/* ------------------------------------------------------------------------------------------------
 * Branch Logic
 * --------------------------------------------------------------------------------------------- */

//Branch Comparator
logic cmp_result;

letc_core_branch_comparator branch_comparator (
    .cmp_operation(d_to_e_ff.cmp_op),
    .*
);

/* ------------------------------------------------------------------------------------------------
 * CSR Updating Logic
 * --------------------------------------------------------------------------------------------- */

//CSR Operand Mux
word_t csr_operand;
always_comb begin
    unique case (d_to_e_ff.csr_op_src)
        CSR_OP_SRC_RS1:     csr_operand = rs1_val;
        CSR_OP_SRC_ZIMM:    csr_operand = {27'h0, d_to_e_ff.csr_zimm};
        default:            csr_operand = 32'hDEADBEEF;
    endcase
end

//Modify the CSR value
word_t csr_new_val;
always_comb begin
    unique case (d_to_e_ff.csr_alu_op)
        CSR_ALU_OP_PASSTHRU:    csr_new_val = csr_operand;
        CSR_ALU_OP_BITSET:      csr_new_val = d_to_e_ff.csr_old_val |  csr_operand;
        CSR_ALU_OP_BITCLEAR:    csr_new_val = d_to_e_ff.csr_old_val & ~csr_operand;
        default:                csr_new_val = 32'hDEADBEEF;
    endcase
end

/* ------------------------------------------------------------------------------------------------
 * Output Connections
 * --------------------------------------------------------------------------------------------- */

always_comb begin
    e_to_m1_valid = d_to_e_valid_ff && !e_flush && !e_stall;

    e_to_m1 = '{
        pc_word:        d_to_e_ff.pc_word,
        rd_src:         d_to_e_ff.rd_src,
        rd_idx:         d_to_e_ff.rd_idx,
        rd_we:          d_to_e_ff.rd_we,
        csr_expl_wen:   d_to_e_ff.csr_expl_wen,
        csr_idx:        d_to_e_ff.csr_idx,
        csr_old_val:    d_to_e_ff.csr_old_val,
        csr_new_val:    csr_new_val,
        rs1_idx:        d_to_e_ff.rs1_idx,
        rs2_idx:        d_to_e_ff.rs2_idx,
        alu_result:     alu_result,
        mem_op:         d_to_e_ff.mem_op,
        mem_signed:     d_to_e_ff.mem_signed,
        mem_size:       d_to_e_ff.mem_size,
        amo_alu_op:     d_to_e_ff.amo_alu_op,
        rs2_val:        rs2_val,
        branch_taken:   cmp_result
    };
end

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

//TODO

//assert property (@(posedge clk) disable iff (!rst_n) !(stage_flush && stage_stall));

`endif //SIMULATION

endmodule : letc_core_stage_execute
