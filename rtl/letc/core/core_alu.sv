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

module core_alu (
    input clk,
    input rst_n,
    input logic [31:0] op1, // Operand 1
    input logic [31:0] op2, // Operand 2
    input logic [3:0] opcode,
    output logic [31:0] result
    // TODO other ports
);

endmodule
