/*
 * File:    core_s1_top.sv
 * Brief:   TODO
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

module core_s1_top
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

endmodule : core_s1_top
