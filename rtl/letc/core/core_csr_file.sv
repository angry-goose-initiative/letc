/*
 * File:    core_csr_file.sv
 * Brief:   The CSR file
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

module core_csr_file
    import letc_pkg::*;
(
    input clk,
    input rst_n,
    input logic [11:0] csr_sel,
    output word_t csr_out,
    
    // Implicitly read CSRs
    output word_t csr_mstatus
);

endmodule : core_csr_file
