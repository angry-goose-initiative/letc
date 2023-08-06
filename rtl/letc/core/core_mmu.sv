/*
 * File:    core_mmu.sv
 * Brief:   The memory management unit
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

module core_mmu
    import letc_pkg::*;
    import core_pkg::*;
(
    input   logic   clk,
    input   logic   rst_n,

    //Implicitly read CSRs
    input   word_t  csr_mstatus_val,
    input   word_t  csr_satp_val

    //TODO other ports
);

endmodule : core_mmu
