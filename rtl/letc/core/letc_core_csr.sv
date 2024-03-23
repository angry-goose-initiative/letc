/*
 * File:    letc_core_csr.sv
 * Brief:   The CSR file
 *
 * Copyright:
 *  Copyright (C) 2023      Nick Chan
 *  Copyright (C) 2023-2024 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_csr
    import letc_pkg::*;
    import letc_core_pkg::*;
(
    //Clock and reset
    input logic i_clk,
    input logic i_rst_n,

    //Implicitly read CSRs by LETC Core logic, always valid
    output csr_implicit_rdata_s o_csr_implicit_rdata,

    //Interface for CSRs whose state (at least partially) exists outside of this module
    //TODO

    //CSR explicit software read interface
    input  logic        i_csr_explicit_ren,
    input  csr_idx_t    i_csr_explicit_ridx,
    output word_t       o_csr_explicit_rdata,
    output logic        o_csr_explicit_rill,

    //CSR explicit software read interface
    input  logic        i_csr_explicit_wen,
    input  csr_idx_t    i_csr_explicit_widx,
    input  word_t       i_csr_explicit_wdata,
    output logic        o_csr_explicit_will
);

assign o_csr_explicit_rdata = 32'hDEADBEEF;//TESTING

//Detecting illegal CSR accesses for security/to catch SW bugs is a low priority
assign o_csr_explicit_rill = 1'b0;
assign o_csr_explicit_will = 1'b0;

endmodule : letc_core_csr
