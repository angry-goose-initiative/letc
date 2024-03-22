/*
 * File:    letc_core_stage_e1.sv
 * Brief:   LETC Core 1st Execute Stage
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

module letc_core_stage_e1
    import letc_pkg::*;
    import letc_core_pkg::*;
(
    //Clock and reset
    input logic i_clk,
    input logic i_rst_n,

    //TODO

    //TLB interface
    letc_core_tlb_if.stage dtlb_if,

    //Hazard/backpressure signals
    output logic o_stage_ready,
    input  logic i_stage_flush,
    input  logic i_stage_stall,

    //From D
    input d_to_e1_s i_d_to_e1,

    //To E2
    output e1_to_e2_s o_e1_to_e2
);

assign o_e1_to_e2.valid = 1'b0;//TODO

endmodule : letc_core_stage_e1
