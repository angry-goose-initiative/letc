/*
 * File:    letc_core_stage_w.sv
 * Brief:   LETC Core Writeback Stage
 *
 * Copyright:
 *  Copyright (C) 2024 John Jekel
 *  Copyright (C) 2024 Sam Graham
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
    input  logic        i_clk, // unused
    input  logic        i_rst_n, // unused

    //Hazard/backpressure signals
    output logic        o_stage_ready,
    input  logic        i_stage_flush, // unused
    input  logic        i_stage_stall, // unused

    //rd Write Port
    output reg_idx_t    o_rd_idx,
    output word_t       o_rd_wdata,
    output logic        o_rd_wen,

    //CSR Write Port
    output logic        o_csr_explicit_wen,
    output csr_idx_t    o_csr_explicit_widx,
    output word_t       o_csr_explicit_wdata,
    input  logic        i_csr_explicit_will, // unused

    //From E2
    input  e2_to_w_s    i_e2_to_w
);

assign o_stage_ready = 1'b1;

assign o_csr_explicit_wen = (i_e2_to_w.csr_op == CSR_OP_ACCESS ? 1'b1 : 1'b0) && i_e2_to_w.valid;
assign o_csr_explicit_widx = i_e2_to_w.csr_idx;
assign o_csr_explicit_wdata = i_e2_to_w.alu_result;

assign o_rd_idx = i_e2_to_w.rd_idx;

always_comb begin : rd_mux
    unique case (i_e2_to_w.rd_src)
        RD_SRC_ALU: o_rd_wdata = i_e2_to_w.alu_result;
        RD_SRC_MEM: o_rd_wdata = i_e2_to_w.old_csr_value;
        RD_SRC_CSR: o_rd_wdata = i_e2_to_w.memory_rdata;
        default:    o_rd_wdata = 32'h0;
    endcase
end : rd_mux

assign o_rd_wen = i_e2_to_w.rd_we && i_e2_to_w.valid;

// TODO handle exceptions

endmodule : letc_core_stage_w
