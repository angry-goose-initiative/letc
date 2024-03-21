/*
 * File:    letc_core_tlb.sv
 * Brief:   TLB module used for both LETC Core instruction and data TLBs
 *
 * Copyright:
 *  Copyright (C) 2024 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_tlb
    import letc_pkg::*;
    import letc_core_pkg::*;
(//TODO perhaps parameters?
    //Clock and reset
    input logic i_clk,
    input logic i_rst_n

    //TODO design TLB interface to F1 and E1

    //TODO design TLB interface to MMU
);

logic TODO;

endmodule : letc_core_tlb
