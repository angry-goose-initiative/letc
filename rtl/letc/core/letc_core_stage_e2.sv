/*
 * File:    letc_core_stage_e2.sv
 * Brief:   LETC Core 2nd Execute Stage
 *
 * Copyright:
 *  Copyright (C) 2024 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_stage_e2
    import letc_pkg::*;
    import letc_core_pkg::*;
(
    //Clock and reset
    input logic i_clk,
    input logic i_rst_n,

    //TODO

    //Hazard/backpressure signals
    output logic o_stage_ready,
    input  logic i_stage_flush,
    input  logic i_stage_stall,

    //From E1
    input e1_to_e2_s i_e1_to_e2,
    
    //To W
    output e2_to_w_s o_e2_to_w
);

logic TODO;

endmodule : letc_core_stage_e2
