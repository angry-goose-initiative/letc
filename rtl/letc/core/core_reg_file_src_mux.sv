/*
 * File:    core_reg_file_src_mux.sv
 * Brief:   The register file source mux
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

module core_reg_file_src_mux
    import core_pkg::*;
(
    input  rd_src_e rd_src,
    input  word_t data_mem,
    input  word_t pc_plus_4,
    input  word_t alu,
    input  word_t csr,
    output word_t rd,
);

endmodule : core_reg_file_src_mux
