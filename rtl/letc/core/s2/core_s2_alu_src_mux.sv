/*
 * File:    core_s2_alu_src_mux.sv
 * Brief:   The ALU source mux
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

module core_s2_alu_src_mux
    import letc_pkg::*;
    import core_pkg::*;
(
    //ALU operand 1 mux IO
    input   alu_op1_src_e   alu_op1_src,
    input   word_t          rs1_ff,
    input   word_t          pc_ff,
    input   word_t          csr_uimm,
    input   word_t          dcache_data_out,
    output  word_t          alu_operand_1,

    //ALU operand 2 mux IO
    input   alu_op2_src_e   alu_op2_src,
    input   word_t          rs2_ff,
    input   word_t          imm,
    input   word_t          csr_data_out,
    output  word_t          alu_operand_2
);

//ALU operand 1 mux
//TODO

//ALU operand 2 mux
//TODO

endmodule : core_s2_alu_src_mux
