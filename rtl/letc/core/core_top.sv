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

`ifdef IMPORTS_IN_MODULE_SCOPE_UNSUPPORTED
import letc_pkg::*;
import core_pkg::*;
`endif

module core_top
`ifndef IMPORTS_IN_MODULE_SCOPE_UNSUPPORTED
    import letc_pkg::*;
    import core_pkg::*;
`endif
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
prv_mode_t      prv_mode_ff;
prv_mode_t      prv_mode_wd;
logic           prv_mode_we;

//Implicitly read CSRs (ordered by address ascending)
word_t          csr_sie_ff;
word_t          csr_stvec_ff;
word_t          csr_satp_ff;
word_t          csr_mstatus_ff;
word_t          csr_medeleg_ff;
word_t          csr_mideleg_ff;
word_t          csr_mie_ff;
word_t          csr_mtvec_ff;

//Implicitly written CSRs (ordered by address ascending)
word_t          csr_sepc_wd;
logic           csr_sepc_we;
word_t          csr_scause_wd;
logic           csr_scause_we;
word_t          csr_stval_wd;//TODO maybe not have this?
logic           csr_stval_we;//TODO ^
//TODO sip?
word_t          csr_mstatus_wd;//TODO this likely needs to be broken into its individual fields
logic           csr_mstatus_we;
word_t          csr_mepc_wd;
logic           csr_mepc_we;
word_t          csr_mcause_wd;
logic           csr_mcause_we;
//TODO mtval?
//TODO mip?
//TODO minst?
//TODO others

//Data from s1 to s2
word_t          s1_to_s2_pc;
word_t          s1_to_s2_instr;

logic           invalidate_fetch;

word_t          branch_target;
logic           branch_en;

//?
word_t          csr_wd;
logic           csr_we;

//?
logic           s2_busy;//Means s2 is NOT ready to accept a new instruction from s1 this cycle
logic           halt_req;//LETC.EXIT instruction encountered in M-mode

/* ------------------------------------------------------------------------------------------------
 * Module Instantiations
 * --------------------------------------------------------------------------------------------- */

core_master_control core_master_control_inst    (.*);
core_s1             core_s1_inst                (.*);
core_s2             core_s2_inst                (.*);
core_mmu            core_mmu_inst               (.*);
core_csr_file       core_csr_file_inst          (.*);

endmodule : core_top
