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

`ifdef IMPORTS_IN_MODULE_SCOPE_UNSUPPORTED
import letc_pkg::*;
import core_pkg::*;
`endif

module core_csr_file
`ifndef IMPORTS_IN_MODULE_SCOPE_UNSUPPORTED
    import letc_pkg::*;
    import core_pkg::*;
`endif
(
    input   logic           clk,
    input   logic           rst_n,
    input   logic [11:0]    csr_sel,//TODO should we make an enum for this?
    output  word_t          csr_data_out,

    //Privilege mode
    output  prv_mode_t      prv_mode_ff,
    input   prv_mode_t      prv_mode_wd,
    input   logic           prv_mode_we,
    
    //Implicitly read CSRs (ordered by address ascending)
    //TODO move these into a struct
    output  word_t          csr_sie_ff,
    output  word_t          csr_stvec_ff,
    //TODO sip?
    output  word_t          csr_satp_ff,
    output  word_t          csr_mstatus_ff,
    output  word_t          csr_medeleg_ff,
    output  word_t          csr_mideleg_ff,
    output  word_t          csr_mie_ff,
    output  word_t          csr_mtvec_ff,
    //TODO mip?
    //TODO minst?
    //TODO others

    //Implicitly written CSRs (ordered by address ascending)
    //TODO move these into a struct
    input   word_t          csr_sepc_wd,
    input   logic           csr_sepc_we,
    input   word_t          csr_scause_wd,
    input   logic           csr_scause_we,
    input   word_t          csr_stval_wd,//TODO maybe not have this?
    input   logic           csr_stval_we,//TODO ^
    //TODO sip?
    input   word_t          csr_mstatus_wd,//TODO this likely needs to be broken into its individual fields
    input   logic           csr_mstatus_we,
    input   word_t          csr_mepc_wd,
    input   logic           csr_mepc_we,
    input   word_t          csr_mcause_wd,
    input   logic           csr_mcause_we
    //TODO mtval?
    //TODO mip?
    //TODO minst?
    //TODO others
);

assign csr_data_out = 32'hDEADBEEF;//TESTING

endmodule : core_csr_file
