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
    import letc_pkg::*;
(
    input logic [1:0] sel,
    input word_t data_mem,
    input word_t pc_plus_4,
    input word_t alu,
    input word_t csr,
    output word_t dout,
);

endmodule : core_reg_file_src_mux
