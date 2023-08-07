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

`ifdef IMPORTS_IN_MODULE_SCOPE_UNSUPPORTED
import letc_pkg::*;
import core_pkg::*;
`endif

module core_mmu
`ifndef IMPORTS_IN_MODULE_SCOPE_UNSUPPORTED
    import letc_pkg::*;
    import core_pkg::*;
`endif
(
    input   logic   clk,
    input   logic   rst_n,

    //Implicitly read CSRs
    input   word_t  csr_mstatus_ff,
    input   word_t  csr_satp_ff

    //TODO other ports
);

endmodule : core_mmu
