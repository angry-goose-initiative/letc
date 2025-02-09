/*
 * File:    letc_core_csrf.sv
 * Brief:   The CSR file
 *
 * Copyright:
 *  Copyright (C) 2023-2025 Nick Chan
 *  Copyright (C) 2023-2024 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
*/

// verilator lint_save
// verilator lint_off UNUSEDSIGNAL

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

    // Interface for CSRs whose state (at least partially) exists outside of this module
    // TODO

    // CSR explicit software interface with decode stage
    input   csr_idx_t   d_csr_expl_idx,
    output  word_t      d_csr_expl_rdata,
    output  logic       d_csr_expl_rill,
    output  logic       d_csr_expl_will,

    // CSR explicit software interface with writeback stage
    input   csr_idx_t   w_csr_expl_idx,
    input   logic       w_csr_expl_we,
    input   word_t      w_csr_expl_wdata
);

// TODO
assign d_csr_expl_rdata = 32'hDEADBEEF;
assign d_csr_expl_rill = 1'b0;
assign d_csr_expl_will = 1'b0;
assign csr_implicit_rdata = '0;

endmodule : letc_core_csrf
