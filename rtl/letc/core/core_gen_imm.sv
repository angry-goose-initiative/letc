/*
 * File:    core_gen_imm.sv
 * Brief:   Generates the immediate value
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

module core_gen_imm
    import core_pkg::*;
(
    input  word_t instruction,//TODO we should let decode do more of the work for us
    output word_t immediate
    // TODO other ports
);

word_t imm_i;
word_t imm_s;
word_t imm_b;
word_t imm_u;
word_t imm_j;
word_t uimm;

assign imm_i = {{20{instruction[31]}}, instruction[31:20]};
assign imm_s = {{20{instruction[31]}}, instruction[31:25], instruction[11:7]};
assign imm_b = {{19{instruction[31]}}, instruction[31],    instruction[7],  instruction[30:25], instruction[11:8], 1'b0};
assign imm_u = {instruction[31:12], 12'h000};
assign imm_j = {{12{instruction[31]}}, instruction[19:12], instruction[20], instruction[30:21], 1'b0};
assign uimm  = {'0, instruction[19:15]};//NOT sign extended

//TODO immediate mux based on instruction format

endmodule : core_gen_imm
