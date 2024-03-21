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

    /*
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
    */

    //CSR explicit software read interface
    input  logic        i_csr_explicit_ren,
    input  logic [11:0] i_csr_explicit_raddr,
    output word_t       o_csr_explicit_rdata,
    output logic        o_csr_explicit_rill,

    //CSR explicit software read interface
    input  logic        i_csr_explicit_wen,
    input  logic [11:0] i_csr_explicit_waddr,
    input  word_t       i_csr_explicit_wdata,
    output logic        o_csr_explicit_will
);

assign o_csr_explicit_rdata = 32'hDEADBEEF;//TESTING

//Detecting illegal CSR accesses for security/to catch SW bugs is a low priority
assign o_csr_explicit_rill = 1'b0;
assign o_csr_explicit_will = 1'b0;

endmodule : letc_core_csr
