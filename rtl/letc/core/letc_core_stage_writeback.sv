/*
 * File:    letc_core_stage_writeback.sv
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

module letc_core_stage_writeback
    import letc_pkg::*;
    import letc_core_pkg::*;
    import riscv_pkg::*;
(
    //Clock and reset
    input  logic        clk,
    input  logic        rst_n,

    //Hazard/backpressure signals
    output logic        stage_ready,
    input  logic        stage_flush, // unused
    input  logic        stage_stall, // unused

    //rd Write Port
    output reg_idx_t    rd_idx,
    output word_t       rd_val,
    output logic        rd_wen,

    //CSR Write Port
    output logic        csr_explicit_wen,
    output csr_idx_t    csr_explicit_widx,
    output word_t       csr_explicit_wdata,
    input  logic        csr_explicit_will, // unused

    //From E2
    input  e2_to_w_s    e2_to_w
);

assign stage_ready = 1'b1;

assign csr_explicit_wen = (e2_to_w.csr_op == CSR_OP_ACCESS ? 1'b1 : 1'b0) && e2_to_w.valid;
assign csr_explicit_widx = e2_to_w.csr_idx;
assign csr_explicit_wdata = e2_to_w.alu_result;

assign rd_idx = e2_to_w.rd_idx;

always_comb begin : rd_mux
    unique case (e2_to_w.rd_src)
        RD_SRC_ALU: rd_val = e2_to_w.alu_result;
        RD_SRC_MEM: rd_val = e2_to_w.old_csr_value;
        RD_SRC_CSR: rd_val = e2_to_w.memory_rdata;
        default:    rd_val = 32'h0;
    endcase
end : rd_mux

assign rd_wen = e2_to_w.rd_we && e2_to_w.valid;

// TODO handle exceptions

endmodule : letc_core_stage_writeback
