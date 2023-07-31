/*
 * File:    core_alu.sv
 * Brief:   The ALU
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

module core_alu
    import letc_pkg::*;
(
    input clk,
    input rst_n,
    input word_t op1, // Operand 1
    input word_t op2, // Operand 2
    input logic [3:0] opcode,
    output word_t result
    // TODO other ports
);

endmodule : core_alu
