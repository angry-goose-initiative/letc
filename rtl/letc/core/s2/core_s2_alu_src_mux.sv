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
    input   word_t          rs1,
    input   word_t          dcache_data_out,
    input   word_t          current_pc,
    output  word_t          alu_operand_1,

    //ALU operand 2 mux IO
    input   alu_op2_src_e   alu_op2_src,
    input   word_t          rs2,
    input   word_t          saved_rs2,//Temporary register for atomics NOTE we will likely remove this since we will only do the write back when the instruction finishes
    input   word_t          immediate,
    input   word_t          csr_data_out,
    output  word_t          alu_operand_2
);

//ALU operand 1 mux
//TODO

//ALU operand 2 mux
//TODO

endmodule : core_s2_alu_src_mux
