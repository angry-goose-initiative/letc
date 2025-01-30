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

    //TODO

    //Hazard/backpressure signals
    output logic  stage_ready,
    input  logic  stage_flush,
    input  logic  stage_stall,

    /*
    //bypass signals
    input  logic  bypass_rs1,
    input  logic  bypass_rs2,
    input  word_t bypassed_rs1_data,
    input  word_t bypassed_rs2_data,
    */

    //From D
    // verilator lint_save
    // verilator lint_off UNUSEDSIGNAL
    input   logic       d_to_e_valid,
    // verilator lint_restore
    input   d_to_e_s    d_to_e,

    //To E2
    output  logic       e_to_m_valid,
    output  e_to_m_s    e_to_m
);

/* ------------------------------------------------------------------------------------------------
 * Input Flop Stage
 * --------------------------------------------------------------------------------------------- */

// verilator lint_save
// verilator lint_off UNUSEDSIGNAL
logic ff_in_valid;
// verilator lint_restore
always_ff @(posedge clk) begin
    if (!rst_n) begin
        ff_in_valid <= 1'b0;
    end else if (!stage_stall) begin
        ff_in_valid <= d_to_e_valid;
    end
end

// verilator lint_save
// verilator lint_off UNUSEDSIGNAL
d_to_e_s ff_in;
// verilator lint_restore
always_ff @(posedge clk) begin
    if (!stage_stall) begin
       ff_in <= d_to_e;
    end
end

assign stage_ready = 1'b1; // TODO: Will not be ready during multicycle multiply

logic out_valid;
assign out_valid = ff_in_valid && !stage_flush && !stage_stall;

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
    rs1_val = /* bypass_rs1 ? bypassed_rs1_data : */ ff_in.rs1_val;
    rs2_val = /* bypass_rs1 ? bypassed_rs2_data : */ ff_in.rs2_val;
end

//ALU connections
//op1
always_comb begin
    unique case (ff_in.alu_op1_src)
        ALU_OP1_SRC_RS1:  alu_operands[0] = rs1_val;
        ALU_OP1_SRC_PC:   alu_operands[0] = ff_in.pc_word;
        ALU_OP1_SRC_CSR:  alu_operands[0] = ff_in.csr_old_val;
        ALU_OP1_SRC_ZERO: alu_operands[0] = 32'h0;
    endcase
end
//op2
always_comb begin
    unique case (ff_in.alu_op2_src)
        ALU_OP2_SRC_RS1:  alu_operands[1] = rs1_val;
        ALU_OP2_SRC_RS2:  alu_operands[1] = rs2_val;
        ALU_OP2_SRC_IMM:  alu_operands[1] = ff_in.immediate;
        ALU_OP2_SRC_FOUR: alu_operands[1] = 32'h4;
    endcase
end
//operation
always_comb begin
    alu_operation = ff_in.alu_op;
end

/* ------------------------------------------------------------------------------------------------
 * Branch Logic
 * --------------------------------------------------------------------------------------------- */

//Branch Comparator
logic cmp_result;

letc_core_branch_comparator branch_comparator (
    .cmp_operation(ff_in.cmp_op),
    .*
);

/* ------------------------------------------------------------------------------------------------
 * CSR Updating Logic
 * --------------------------------------------------------------------------------------------- */

//CSR Operand Mux
word_t csr_operand;
always_comb begin
    unique case (ff_in.csr_op_src)
        CSR_OP_SRC_RS1:     csr_operand = rs1_val;
        CSR_OP_SRC_UIMM:    csr_operand = {27'h0, ff_in.csr_zimm};
        default:        csr_operand = 32'hDEADBEEF;
    endcase
end

//Modify the CSR value
word_t new_csr_value;
always_comb begin
    unique case (ff_in.csr_alu_op)
        CSR_ALU_OP_PASSTHRU:    new_csr_value = csr_operand;
        CSR_ALU_OP_BITSET:      new_csr_value = ff_in.csr_old_val |  csr_operand;
        CSR_ALU_OP_BITCLEAR:    new_csr_value = ff_in.csr_old_val & ~csr_operand;
        default:                new_csr_value = 32'hDEADBEEF;
    endcase
end

/* ------------------------------------------------------------------------------------------------
 * Output Connections
 * --------------------------------------------------------------------------------------------- */

always_comb begin
    e_to_m_valid = out_valid;

    e_to_m = '{
        pc_word:        ff_in.pc_word,
        rd_src:         ff_in.rd_src,
        rd_idx:         ff_in.rd_idx,
        rd_we:          ff_in.rd_we,
        csr_idx:        ff_in.csr_idx,
        csr_old_val:    ff_in.csr_old_val,
        csr_new_val:    new_csr_value,
        rs1_idx:        ff_in.rs1_idx,
        rs2_idx:        ff_in.rs2_idx,
        alu_result:     alu_result,
        memory_op:      ff_in.memory_op,
        memory_signed:  ff_in.memory_signed,
        memory_size:    ff_in.memory_size,
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
