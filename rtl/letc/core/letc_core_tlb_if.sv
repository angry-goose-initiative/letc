/*
 * File:    letc_core_tlb_if.sv
 * Brief:   LETC cache interface
 *
 * Copyright:
 *  Copyright (C) 2024 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Interface Definition
 * --------------------------------------------------------------------------------------------- */

interface letc_core_tlb_if
    import letc_pkg::*;
    import letc_core_pkg::*;
(
    //Global signals
    input logic i_clk,
    input logic i_rst_n
);

/* ------------------------------------------------------------------------------------------------
 * Connections
 * --------------------------------------------------------------------------------------------- */

logic valid;
//TODO design tlb interface

/* ------------------------------------------------------------------------------------------------
 * Modports
 * --------------------------------------------------------------------------------------------- */

modport stage (
    output valid
    //TODO
);

modport tlb (
    input  valid
    //TODO
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

endinterface : letc_core_tlb_if