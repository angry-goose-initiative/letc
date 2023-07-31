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
    import letc_pkg::*;
(
    input instr_t instruction,//TODO we should let decode do more of the work for us
    output word_t immediate
    // TODO other ports
);

endmodule : core_gen_imm
