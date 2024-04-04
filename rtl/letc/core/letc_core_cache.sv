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

    //Signal to flush all cache lines
    //TODO how to convey if the flush is not yet complete?
    input i_flush_cache,

    //Cache interface (LIMP)
    letc_core_limp_if.servicer stage_limp,

    //LIMP interface to AXI FSM
    letc_core_limp_if.requestor axi_fsm_limp
);

assign stage_limp.ready     = 1'b0;//TODO
assign axi_fsm_limp.valid   = 1'b0;//TODO

endmodule : letc_core_cache
