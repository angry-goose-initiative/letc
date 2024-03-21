/*
 * File:    letc_core_mmu.sv
 * Brief:   LETC Core MMU
 *
 * Copyright:
 *  Copyright (C) 2024 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_mmu
    import letc_pkg::*;
    import letc_core_pkg::*;
(
    //Clock and reset
    input logic i_clk,
    input logic i_rst_n,

    //TODO design MMU interfaces
    
    //LIMP interface
    letc_core_limp_if.requestor limp
);

assign limp.valid = 1'b0;//TODO

endmodule : letc_core_mmu
