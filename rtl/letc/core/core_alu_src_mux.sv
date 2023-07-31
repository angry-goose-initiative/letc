/*
 * File:    core_alu_src_mux.sv
 * Brief:   The ALU source mux
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

module core_alu_src_mux
    import letc_pkg::*;
(
    // op1
    input logic [2:0] op1_sel,
    input word_t reg1, // value in rs1
    input word_t data_mem, // data memory
    input word_t pc // program counter
    output word_t op1, // Operand 1

    // op2
    input logic [2:0] op2_sel,
    input word_t reg2, // value in rs2
    input word_t saved_reg2,
    input word_t imm, // immediate value
    input word_t csr, // CSR
    output word_t op2 // Operand 2
);

endmodule : core_alu_src_mux
