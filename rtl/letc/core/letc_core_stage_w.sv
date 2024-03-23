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
    output reg_idx_t    o_rd_idx,
    output word_t       o_rd_wdata,
    output logic        o_rd_wen,

    //CSR Write Port
    output logic        o_csr_explicit_wen,
    output csr_idx_t    o_csr_explicit_widx,
    output word_t       o_csr_explicit_wdata,
    input  logic        i_csr_explicit_will,

    //From E2
    input  e2_to_w_s    i_e2_to_w
);

logic todo;

endmodule : letc_core_stage_w
