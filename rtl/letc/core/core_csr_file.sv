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
    import core_pkg::*;
(
    input   logic           clk,
    input   logic           rst_n,
    input   logic [11:0]    csr_sel,//TODO should we make an enum for this?
    output  word_t          csr_data_out,
    
    // Implicitly read CSRs
    output  word_t          csr_mstatus
    output  word_t          csr_satp

    //TODO others
);

endmodule : core_csr_file
