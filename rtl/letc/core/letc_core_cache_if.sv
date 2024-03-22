/*
 * File:    letc_core_cache_if.sv
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

interface letc_core_cache_if
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
//TODO design cache interface. Is it as simple as buffering LIMP accesses or something?

/* ------------------------------------------------------------------------------------------------
 * Modports
 * --------------------------------------------------------------------------------------------- */

modport stage (
    output valid
    //TODO
);

modport cache (
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

`endif

endinterface : letc_core_cache_if
