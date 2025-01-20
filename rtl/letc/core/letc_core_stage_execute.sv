/*
 * File:    letc_core_stage_execute.sv
 * Brief:   LETC Core Execute Stage
 *
 * Copyright:
 *  Copyright (C) 2024-2025 John Jekel
 *  Copytight (C) 2024 Eric Jessee
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
    /*
    output logic  stage_ready,
    input  logic  stage_flush,
    input  logic  stage_stall,

    //bypass signals
    input  logic  bypass_rs1,
    input  logic  bypass_rs2,
    input  word_t bypassed_rs1_data,
    input  word_t bypassed_rs2_data,
    */

    //From D
    input d_to_e_s d_to_e,

    //To E2
    output e_to_m_s e_to_m
);

/* ------------------------------------------------------------------------------------------------
 * Input Flop Stage
 * --------------------------------------------------------------------------------------------- */

d_to_e_s d_to_e_ff;

always_ff @(posedge clk) begin
    if (!rst_n) begin
        d_to_e_ff.valid <= 1'b0;
    end else begin
        //TODO control signals to conditionally flop this or invalidate if stalled/flushed
        /*
        if (stage_flush) begin
            d_to_e_ff.valid <= 1'b0;
        end else if (!stage_stall) begin
            d_to_e_ff.valid <= d_to_e.valid;
        end
        */
       d_to_e_ff <= d_to_e;
    end
end

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
    rs1_val = /* bypass_rs1 ? bypassed_rs1_data : */ d_to_e_ff.rs1_rdata;
    rs2_val = /* bypass_rs1 ? bypassed_rs2_data : */ d_to_e_ff.rs2_rdata;
end

//ALU connections
//op1
always_comb begin
    unique case (d_to_e_ff.alu_op1_src)
        ALU_OP1_SRC_RS1:  alu_operands[0] = rs1_val;
        ALU_OP1_SRC_PC:   alu_operands[0] = {d_to_e_ff.pc_word, 2'b00};
        ALU_OP1_SRC_CSR:  alu_operands[0] = d_to_e_ff.csr_rdata;
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
        CSR_OP_SRC_UIMM:    csr_operand = {27'h0, d_to_e_ff.csr_uimm};
        default:        csr_operand = 32'hDEADBEEF;
    endcase
end

//Modify the CSR value
word_t new_csr_value;
always_comb begin
    unique case (d_to_e_ff.csr_op)
        CSR_OP_RW:  new_csr_value = csr_operand;
        CSR_OP_RS:  new_csr_value = d_to_e_ff.csr_rdata |  csr_operand;
        CSR_OP_RC:  new_csr_value = d_to_e_ff.csr_rdata & ~csr_operand;
        default:    new_csr_value = 32'hDEADBEEF;
    endcase
end

/* ------------------------------------------------------------------------------------------------
 * Output Connections
 * --------------------------------------------------------------------------------------------- */

always_comb begin
    //TODO if flushed or stalled my need to invalidate output
    e_to_m.valid = d_to_e_ff.valid;

    e_to_m.rd_src = d_to_e_ff.rd_src;
    e_to_m.rd_idx = d_to_e_ff.rd_idx;
    e_to_m.rd_we  = d_to_e_ff.rd_we;

    e_to_m.csr_op           = d_to_e_ff.csr_op;
    e_to_m.csr_idx          = d_to_e_ff.csr_idx;
    e_to_m.old_csr_value    = d_to_e_ff.csr_rdata;
    e_to_m.new_csr_value    = new_csr_value;

    e_to_m.rs1_idx = d_to_e_ff.rs1_idx;
    e_to_m.rs2_idx = d_to_e_ff.rs2_idx;

    e_to_m.alu_result = alu_result;

    e_to_m.memory_op        = d_to_e_ff.memory_op;
    e_to_m.memory_signed    = d_to_e_ff.memory_signed;
    e_to_m.memory_size      = d_to_e_ff.memory_size;
    e_to_m.rs2_rdata        = rs2_val;

    e_to_m.branch_taken = cmp_result;
end

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

//TODO

//assert property (@(posedge clk) disable iff (!rst_n) !(stage_flush && stage_stall));

`endif //SIMULATION

endmodule : letc_core_stage_execute
