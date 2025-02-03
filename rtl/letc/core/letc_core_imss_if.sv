/*
 * File:    letc_core_imss_if.sv
 * Brief:   Fetch stage <-> Instruction memory subsystem interface
 *
 * Copyright:
 *  Copyright (C) 2023-2025 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Interface Definition
 * --------------------------------------------------------------------------------------------- */

interface letc_core_imss_if
    import riscv_pkg::*;
    import letc_pkg::*;
    import letc_core_pkg::*;
(
    /*
    input logic clk,
    input logic rst_n
    */
);

/* ------------------------------------------------------------------------------------------------
 * Connections
 * --------------------------------------------------------------------------------------------- */

//TODO remove this waiver in the future when we can
//verilator lint_save
//verilator lint_off UNUSEDSIGNAL

//Fetc 1 <-> Memory Subsystem
logic  req_valid;
word_t req_virtual_addr;
//TODO also req_illegal in reverse

//Fetch 2 <-> Memory Subsystem
logic  rsp_valid;
logic  rsp_illegal;
word_t rsp_virtual_addr;
word_t rsp_data;

//TODO what about things needed for exception handling (like the physical address?)?

//verilator lint_restore

/* ------------------------------------------------------------------------------------------------
 * Modports
 * --------------------------------------------------------------------------------------------- */

modport fetch1 (
    output req_valid,
    output req_virtual_addr
);

modport fetch2 (
    input  rsp_valid,
    input  rsp_illegal,
    input  rsp_virtual_addr,
    input  rsp_data
);

modport subsystem (
    input  req_valid,
    input  req_virtual_addr,

    output rsp_valid,
    output rsp_illegal,
    output rsp_virtual_addr,
    output rsp_data
);

/* ------------------------------------------------------------------------------------------------
 * Functions
 * --------------------------------------------------------------------------------------------- */

//TODO

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

//TODO

`endif //SIMULATION

endinterface : letc_core_imss_if
