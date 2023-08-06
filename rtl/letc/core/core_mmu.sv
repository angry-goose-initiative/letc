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

module core_mmu (
    input   logic   clk,
    input   logic   rst_n,

    //CSR
    input   word_t  csr_mstatus,
    input   word_t  csr_satp

    //TODO other ports
);

endmodule : core_mmu
