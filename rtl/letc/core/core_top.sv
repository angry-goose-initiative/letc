/*
 * File:    core_top.sv
 * Brief:   TODO
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

module core_top
    import letc_pkg::*;
    import core_pkg::*;
(
    input   logic   clk,
    input   logic   rst_n

    //TODO other ports

);

/* ------------------------------------------------------------------------------------------------
 * Connections
 * --------------------------------------------------------------------------------------------- */

/* ---------- CSRs ----------------------------------------------------------------------------- */

logic [11:0]    csr_sel;//TODO should we make an enum for this?
word_t          csr_data_out;

//Privilege mode
prv_mode_t      prv_mode;
prv_mode_t      prv_mode_in;
logic           prv_mode_we;

//Implicitly read CSRs (ordered by address ascending)
word_t          csr_sie;
word_t          csr_stvec;
word_t          csr_satp;
word_t          csr_mstatus;
word_t          csr_medeleg;
word_t          csr_mideleg;
word_t          csr_mie;
word_t          csr_mtvec;

//Implicitly written CSRs (ordered by address ascending)
word_t          csr_sepc_in;
logic           csr_sepc_we;
word_t          csr_scause_in;
logic           csr_scause_we;
word_t          csr_stval_in;//TODO maybe not have this?
logic           csr_stval_we;//TODO ^
//TODO sip?
word_t          csr_mstatus_in;//TODO this likely needs to be broken into its individual fields
logic           csr_mstatus_we;
word_t          csr_mepc_in;
logic           csr_mepc_we;
word_t          csr_mcause_in;
logic           csr_mcause_we;
//TODO mtval?
//TODO mip?
//TODO minst?
//TODO others

/* ------------------------------------------------------------------------------------------------
 * Module Instantiations
 * --------------------------------------------------------------------------------------------- */

core_s1         core_s1_inst        (.*);
core_s2         core_s2_inst        (.*);
core_mmu        core_mmu_inst       (.*);
core_csr_file   core_csr_file_inst  (.*);

endmodule : core_top
