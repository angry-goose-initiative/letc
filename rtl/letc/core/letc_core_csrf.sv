/*
 * File:    letc_core_csrf.sv
 * Brief:   The CSR file
 *
 * Copyright:
 *  Copyright (C) 2023-2025 Nick Chan
 *  Copyright (C) 2023-2024 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_csrf
    import letc_pkg::*;
    import letc_core_pkg::*;
(
    // Clock and reset
    input logic clk,
    input logic rst_n,

    // Implicitly read CSRs by LETC Core logic, always valid
    output csr_implicit_rdata_s csr_implicit_rdata,

    //Interface for CSRs whose state (at least partially) exists outside of this module
    //TODO

    // CSR explicit software read interface
    input  logic        csr_explicit_ren,
    input  csr_idx_t    csr_explicit_ridx,
    output word_t       csr_explicit_rdata,
    output logic        csr_explicit_rill,

    // CSR explicit software write interface
    input  logic        csr_explicit_wen,
    input  csr_idx_t    csr_explicit_widx,
    input  word_t       csr_explicit_wdata,
    // NOTE(Nick): When writing back to CSR's (in WB), the instruction is
    // already assumed valid, need this to be checked earlier (in ID)
    output logic        csr_explicit_will
);

assign o_csr_explicit_rdata = 32'hDEADBEEF;//TESTING

//Detecting illegal CSR accesses for security/to catch SW bugs is a low priority
assign csr_explicit_rill = 1'b0;
assign csr_explicit_will = 1'b0;

endmodule : letc_core_csrf
