/*
 * File:    letc_core_stage_w.sv
 * Brief:   LETC Core Writeback Stage
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

module letc_core_stage_w
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

    //rd Write Port
    output reg_idx_t    i_rd_idx,
    output word_t       i_rd_wdata,
    output logic        i_rd_wen,

    //From E2
    input  e2_to_w_s    i_e2_to_w
);

logic TODO;

endmodule : letc_core_stage_w
