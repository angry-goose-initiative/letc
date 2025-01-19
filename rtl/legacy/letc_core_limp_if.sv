/*
 * File:    letc_core_limp_if.sv
 * Brief:   LETC LIMP interface definition
 *
 * Copyright:
 *  Copyright (C) 2024 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * LIMP is the LETC Internal Memory Protocol
 *
 * A simple data-valid-ready interface for communication betwen caches,
 * etc, and the AXI FSM to the outside world within LETC Core
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Interface Definition
 * --------------------------------------------------------------------------------------------- */

interface letc_core_limp_if
    import letc_pkg::*;
    import letc_core_pkg::*;
    import riscv_pkg::*;
(
    //Global signals
    input logic i_clk,
    input logic i_rst_n
);

/* ------------------------------------------------------------------------------------------------
 * Connections
 * --------------------------------------------------------------------------------------------- */

logic   valid;
logic   ready;
logic   wen_nren;//Write enable and not read enable
logic   uncacheable;
size_e  size;
paddr_t addr;
word_t  rdata;
word_t  wdata;
//TODO fault signal if unaligned, AXI errors, etc
/* ------------------------------------------------------------------------------------------------
 * Modports
 * --------------------------------------------------------------------------------------------- */

modport requestor (
    output valid,
    input  ready,
    output wen_nren,
    output uncacheable,
    output size,
    output addr,
    input  rdata,
    output wdata
);

modport servicer (
    input  valid,
    output ready,
    input  wen_nren,
    input  uncacheable,
    input  size,
    input  addr,
    output rdata,
    input  wdata
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

endinterface : letc_core_limp_if
