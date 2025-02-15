/*
 * File:    letc_core_stage_writeback.sv
 * Brief:   LETC Core Writeback Stage
 *
 * Copyright:
 *  Copyright (C) 2025 Nick Chan
 *  Copyright (C) 2025 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
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
    input   logic       clk,
    input   logic       rst_n,

    output  logic       w_ready,
    input   logic       w_flush,
    input   logic       w_stall,

    output  reg_idx_t   rf_rd_idx,
    output  word_t      rf_rd_val,
    output  logic       rf_rd_we,

    output  csr_idx_t   w_csr_expl_idx,
    output  logic       w_csr_expl_we,
    output  word_t      w_csr_expl_wdata,

    input   logic       m2_to_w_valid,
    input   m2_to_w_s   m2_to_w,

    letc_core_dmss_if.writeback dmss_if,

    letc_core_forwarder_if.stage w_forwarder
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

/* ------------------------------------------------------------------------------------------------
 * DMSS
 * --------------------------------------------------------------------------------------------- */

word_t store_data;
word_t storing_byte;
word_t storing_hw;
word_t storing_word;

always_comb begin
    unique case (ff_in.alu_result[1:0])
        2'b00:      storing_byte = {ff_in.mem_rdata[31:8], ff_in.rs2_val[7:0]};
        2'b01:      storing_byte = {ff_in.mem_rdata[31:16], ff_in.rs2_val[7:0], ff_in.mem_rdata[7:0]};
        2'b10:      storing_byte = {ff_in.mem_rdata[31:24], ff_in.rs2_val[7:0], ff_in.mem_rdata[15:0]};
        default:    storing_byte = {ff_in.rs2_val[7:0], ff_in.mem_rdata[23:0]};
    endcase
    storing_hw = (ff_in.alu_result[1])
        ? {ff_in.rs2_val[15:0], ff_in.mem_rdata[15:0]}
        : {ff_in.mem_rdata[31:16], ff_in.rs2_val[15:0]};
    storing_word = ff_in.rs2_val;
    unique case (ff_in.mem_size)
        MEM_SIZE_BYTE:      store_data = storing_byte;
        MEM_SIZE_HALFWORD:  store_data = storing_hw;
        default:            store_data = storing_word;
    endcase
end

assign dmss_if.dmss2_req_commit = ff_in.mem_op == MEM_OP_STORE && out_valid;
assign dmss_if.dmss2_req_store_data = store_data;

/* ------------------------------------------------------------------------------------------------
 * RD mux
 * --------------------------------------------------------------------------------------------- */

word_t rd_val;
always_comb begin
    unique case (ff_in.rd_src)
        RD_SRC_ALU: rd_val = ff_in.alu_result;
        RD_SRC_MEM: rd_val = ff_in.mem_rdata;
        RD_SRC_CSR: rd_val = ff_in.csr_old_val;
        default:    rd_val = 32'hDEADBEEF;
    endcase
end

/* ------------------------------------------------------------------------------------------------
 * RF/CSRF port
 * --------------------------------------------------------------------------------------------- */

always_comb begin
    w_csr_expl_idx      = ff_in.csr_idx;
    w_csr_expl_we       = ff_in.csr_expl_wen;
    w_csr_expl_wdata    = ff_in.csr_new_val;

    rf_rd_val   = rd_val;
    rf_rd_idx   = ff_in.rd_idx;
    rf_rd_we    = ff_in.rd_we && out_valid;
end

/* ------------------------------------------------------------------------------------------------
 * Forwarding
 * --------------------------------------------------------------------------------------------- */

// Forwarder
always_comb begin
    w_forwarder.instr_produces_rd = ff_in.rd_we && ff_in_valid;
    w_forwarder.rd_idx = ff_in.rd_idx;
    w_forwarder.rd_val_avail = 1'b1;
    w_forwarder.rd_val = rd_val;
end

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

//TODO

//The testbench uses this
//verilator lint_save
//verilator lint_off UNUSEDSIGNAL
logic sim_should_exit;
assign sim_should_exit = ff_in_valid && ff_in.sim_exit_req;
//verilator lint_restore

`endif //SIMULATION

endmodule : letc_core_stage_writeback
