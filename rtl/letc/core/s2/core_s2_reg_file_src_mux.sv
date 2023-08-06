/*
 * File:    core_s2_reg_file_src_mux.sv
 * Brief:   The register file source mux
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

module core_s2_reg_file_src_mux
    import core_pkg::*;
(
    input   rd_src_e    rd_src,
    input   word_t      dcache_data_out,
    input   word_t      next_seq_pc,
    input   word_t      alu_result,
    input   word_t      csr_data_out,
    output  word_t      rd
);

//TODO

endmodule : core_s2_reg_file_src_mux
