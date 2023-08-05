/*
 * File:    core_top.sv
 * Brief:   TODO
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

module core_top
    import core_pkg::*;
(
    input clk,
    input rst_n

    //TODO other ports

);

/* ------------------------------------------------------------------------------------------------
 * Connections
 * --------------------------------------------------------------------------------------------- */

//?
word_t current_pc;//PC?
word_t next_seq_pc;//PC?
word_t saved_rs2;//?
logic  halt_req;//Control?

//Memory
word_t dcache_data_out;

//Register file
reg_index_t rd_index;
word_t      rd;
logic       rd_write_enable;
reg_index_t rs1_index;
word_t      rs1;
reg_index_t rs2_index;
word_t      rs2;

//Register file source mux
rd_src_e rd_src;

//CSRs
logic [11:0] csr_sel;//TODO should we make an enum for this?
word_t csr_data_out;
word_t csr_mstatus;

//Decode
word_t instruction;
word_t immediate;
word_t uimm;
logic  illegal_instr;
//TODO others

//ALU
word_t  alu_operand_1;
word_t  alu_operand_2;
aluop_e alu_operation;
word_t  alu_result;

//ALU source mux
alu_op1_src_e alu_op1_src;
alu_op1_src_e alu_op2_src;

/* ------------------------------------------------------------------------------------------------
 * Module Instantiations
 * --------------------------------------------------------------------------------------------- */

core_s1       core_s1_inst (.*);
core_s2       core_s2_inst (.*);

core_mmu      core_mmu_instance      (.*);
core_csr_file core_csr_file_instance (.*);

endmodule : core_top
