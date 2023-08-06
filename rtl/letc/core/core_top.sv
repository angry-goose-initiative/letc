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

//CSRs
logic [11:0] csr_sel;//TODO should we make an enum for this?
word_t csr_data_out;
word_t csr_mstatus;

/* ------------------------------------------------------------------------------------------------
 * Module Instantiations
 * --------------------------------------------------------------------------------------------- */

core_s1_top             core_s1_top_inst    (.*);
sore_s2_top             core_s2_top_inst    (.*);
core_mmu                core_mmu_inst       (.*);
core_csr_file           core_csr_file_inst  (.*);

endmodule : core_top
