/*
 * File:    letc_core_cache.sv
 * Brief:   Cache module used for both LETC Core instruction and data caches
 *
 * Copyright:
 *  Copyright (C) 2024 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_cache
    import letc_pkg::*;
    import letc_core_pkg::*;
(//TODO perhaps parameters for read only caches?
    //Clock and reset
    input logic i_clk,
    input logic i_rst_n

    //TODO design cache interface. Is it as simple as buffering LIMP accesses or something?
);

logic TODO;

endmodule : letc_core_cache
