/*
 * File:    core_s2_alu.sv
 * Brief:   The ALU
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

module core_s2_alu
    import core_pkg::*;
(
    input word_t alu_operand_1,
    input word_t alu_operand_2,
    input aluop_e alu_operation,
    output word_t alu_result
);

endmodule : core_s2_alu
