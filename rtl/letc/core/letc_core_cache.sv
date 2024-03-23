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
    input logic i_rst_n,

    //Cache interface
    letc_core_cache_if.cache cache_if,

    //LIMP interface
    letc_core_limp_if.requestor limp
);

assign limp.valid = 1'b0;//TODO

endmodule : letc_core_cache
