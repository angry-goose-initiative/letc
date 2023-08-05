/*
 * File:    core_s2_top.sv
 * Brief:   TODO
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

module core_s2_top
    import core_pkg::*;
(
    input clk,
    input rst_n

    //TODO other ports

);

/* ------------------------------------------------------------------------------------------------
 * Connections
 * --------------------------------------------------------------------------------------------- */

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

core_control            core_control_instance           (.*);
core_alu_src_mux        core_alu_src_mux_instance       (.*);
core_alu                core_alu_instance               (.*);
core_decode             core_decode_instance            (.*);
core_reg_file_src_mux   core_reg_file_src_mux_instance  (.*);
core_reg_file           core_reg_file_instance          (.*);
core_mmu                core_mmu_instance               (.*);
core_csr_file           core_csr_file_instance          (.*);

endmodule : core_s2_top
