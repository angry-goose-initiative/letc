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
    import riscv_pkg::*;
(
    // Clock and reset
    input logic clk,
    input logic rst_n,

    // Implicitly read CSRs by LETC Core logic, always valid
    output csr_implicit_rdata_s csr_implicit_rdata,

    //Interface for CSRs whose state (at least partially) exists outside of this module
    //TODO

    // CSR explicit software interface with decode stage
    input  logic        csr_explicit_ren,
    input  csr_idx_t    csr_explicit_idx,
    output word_t       csr_explicit_rdata,
    input  logic        csr_explicit_wcheck,
    output logic        csr_explicit_illegal,

    // CSR explicit software interface with writeback stage
    input  logic        csr_explicit_wen,
    input  csr_idx_t    csr_explicit_widx,
    input  word_t       csr_explicit_wdata,
);

assign csr_explicit_rdata = 32'hDEADBEEF;//TESTING

//Detecting illegal CSR accesses for security/to catch SW bugs is a low priority
assign csr_explicit_illegal = 1'b0;

endmodule : letc_core_csrf
