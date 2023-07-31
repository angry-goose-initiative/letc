/*
 * File:    core_decode.sv
 * Brief:   TODO
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

module core_decode
    import letc_pkg::*;
(
    input clk,
    input rst_n,

    //Instruction in
    input instr_t instruction,

    //Decoded info out
    //TODO others
    output word_t immediate
);

//TODO the inner goodness
core_gen_imm core_gen_imm_instance (.*);

endmodule : core_decode
