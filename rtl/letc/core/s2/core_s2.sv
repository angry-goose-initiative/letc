/*
 * File:    core_s2.sv
 * Brief:   TODO
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

module core_s2
    import letc_pkg::*;
    import core_pkg::*;
(
    input   logic   clk,
    input   logic   rst_n

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
reg_idx_t   rd_idx;
word_t      rd_wd;
logic       rd_we;
reg_idx_t   rs1_idx;
word_t      rs1_ff;
reg_idx_t   rs2_idx;
word_t      rs2_ff;

//Register file source mux
rd_src_e rd_src;

//CSRs
logic [11:0] csr_sel;//TODO should we make an enum for this?
word_t csr_data_out;

//Control
word_t instruction;
word_t imm;
word_t csr_uimm;
logic  illegal_instr;
//TODO others

//ALU
word_t  alu_operand_1;
word_t  alu_operand_2;
aluop_e alu_operation;
word_t  alu_result;

//ALU source mux
alu_op1_src_e alu_op1_src;
alu_op2_src_e alu_op2_src;

/* ------------------------------------------------------------------------------------------------
 * Module Instantiations
 * --------------------------------------------------------------------------------------------- */

core_s2_control          core_s2_control_inst          (.*);
core_s2_alu_src_mux      core_s2_alu_src_mux_inst      (.*);
core_s2_alu              core_s2_alu_inst              (.*);
core_s2_reg_file_src_mux core_s2_reg_file_src_mux_inst (.*);
core_s2_reg_file         core_s2_reg_file_inst         (.*);

endmodule : core_s2
