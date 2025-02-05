/**
 * File    letc_core_stage_writeback.sv
 * Brief   LETC Core Memory 2 Stage
 *
 * Copyright:
 *  Copyright (C) 2025 Nick Chan
 *  Copyright (C) 2025 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
*/

module letc_core_stage_writeback
    import letc_pkg::*;
    import letc_core_pkg::*;
    import riscv_pkg::*;
(
    input   logic       clk,
    input   logic       rst_n,

    output  logic       w_ready,
    input   logic       w_flush,
    input   logic       w_stall,

    output  reg_idx_t   rf_rd_idx,
    output  word_t      rf_rd_val,
    output  logic       rf_rd_we,

    input   logic       m2_to_w_valid,
    input   m2_to_w_s   m2_to_w,

    letc_core_dmss_if.writeback dmss_if
);

logic ff_in_valid;
always_ff @(posedge clk) begin
    if (!rst_n) begin
        ff_in_valid <= 1'b0;
    end else if (!w_stall) begin
        ff_in_valid <= m2_to_w_valid;
    end
end

// verilator lint_save
// verilator lint_off UNUSEDSIGNAL
m2_to_w_s ff_in;
// verilator lint_restore
always_ff @(posedge clk) begin
    if (!w_stall) begin
        ff_in <= m2_to_w;
    end
end

assign w_ready = 1'b1; // TODO: Would there ever be a cache write miss?

logic out_valid;
assign out_valid = ff_in_valid && !w_flush && !w_stall;

word_t rd_val;
always_comb begin
    unique case (ff_in.rd_src)
        RD_SRC_ALU: rd_val = ff_in.alu_result;
        RD_SRC_MEM: rd_val = ff_in.mem_rdata;
        RD_SRC_CSR: rd_val = ff_in.csr_old_val;
        default:    rd_val = 32'hDEADBEEF;
    endcase

    rf_rd_val = rd_val;
    rf_rd_idx = ff_in.rd_idx;
    rf_rd_we = ff_in.rd_we && out_valid;
end

endmodule : letc_core_stage_writeback
