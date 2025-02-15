/*
 * File:    letc_core_stage_writeback_tb.sv
 * Brief:   Testing the LETC core writeback stage
 *
 * Copyright:
 *  Copyright (C) 2025 Nick Chan
 *  Copyright (C) 2025 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
*/

// verilator lint_save
// verilator lint_off UNUSEDSIGNAL
// verilator lint_off INITIALDLY

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_stage_writeback_tb;

import riscv_pkg::*;
import letc_pkg::*;
import letc_core_pkg::*;

/* ------------------------------------------------------------------------------------------------
 * DUT
 * --------------------------------------------------------------------------------------------- */

logic       clk;
logic       rst_n;
logic       w_ready;
logic       w_flush;
logic       w_stall;
reg_idx_t   rf_rd_idx;
word_t      rf_rd_val;
logic       rf_rd_we;
csr_idx_t   w_csr_expl_idx;
logic       w_csr_expl_we;
word_t      w_csr_expl_wdata;
logic       m2_to_w_valid;
m2_to_w_s   m2_to_w;
letc_core_dmss_if dmss_if();
letc_core_forwarder_if w_forwarder();

letc_core_stage_writeback dut(.*);

/* ------------------------------------------------------------------------------------------------
 * Clocking
 * --------------------------------------------------------------------------------------------- */

localparam CLOCK_PERIOD = 10;

clock_generator #(
    .PERIOD(CLOCK_PERIOD)
) clock_gen_inst (
    .clk(clk)
);

/* ------------------------------------------------------------------------------------------------
 * Tasks
 * --------------------------------------------------------------------------------------------- */

task test_mem_with_params(
    input   mem_size_e  mem_size,
    input   word_t      addr,
    input   word_t      mem_rdata,
    input   word_t      rs2_val,
    input   word_t      expected
);
    m2_to_w.mem_size <= mem_size;
    m2_to_w.alu_result <= addr;
    m2_to_w.mem_rdata <= mem_rdata;
    m2_to_w.rs2_val <= rs2_val;
    @(negedge clk);
    assert(dmss_if.dmss2_req_store_data == expected);
endtask

task test_store_data_gen();
    m2_to_w.mem_op <= MEM_OP_STORE;

    test_mem_with_params(
        .mem_size(MEM_SIZE_WORD),
        .addr(32'h0),
        .mem_rdata(32'h11223344),
        .rs2_val(32'h55667788),
        .expected(32'h55667788)
    );
    test_mem_with_params(
        .mem_size(MEM_SIZE_HALFWORD),
        .addr(32'h0),
        .mem_rdata(32'h11223344),
        .rs2_val(32'h55667788),
        .expected(32'h11227788)
    );
    test_mem_with_params(
        .mem_size(MEM_SIZE_HALFWORD),
        .addr(32'h2),
        .mem_rdata(32'h11223344),
        .rs2_val(32'h55667788),
        .expected(32'h77883344)
    );
    test_mem_with_params(
        .mem_size(MEM_SIZE_BYTE),
        .addr(32'h0),
        .mem_rdata(32'h11223344),
        .rs2_val(32'h55667788),
        .expected(32'h11223388)
    );
    test_mem_with_params(
        .mem_size(MEM_SIZE_BYTE),
        .addr(32'h1),
        .mem_rdata(32'h11223344),
        .rs2_val(32'h55667788),
        .expected(32'h11228844)
    );
    test_mem_with_params(
        .mem_size(MEM_SIZE_BYTE),
        .addr(32'h2),
        .mem_rdata(32'h11223344),
        .rs2_val(32'h55667788),
        .expected(32'h11883344)
    );
    test_mem_with_params(
        .mem_size(MEM_SIZE_BYTE),
        .addr(32'h3),
        .mem_rdata(32'h11223344),
        .rs2_val(32'h55667788),
        .expected(32'h88223344)
    );
endtask

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

initial begin
    rst_n <= 1'b0;
    w_flush <= 1'b0;
    w_stall <= 1'b0;
    m2_to_w_valid <= 1'b0;
    m2_to_w <= '0;

    @(negedge clk);

    rst_n <= 1'b1;
    m2_to_w_valid <= 1'b1;

    @(negedge clk);

    assert(!$isunknown(w_forwarder.instr_produces_rd));
    assert(!$isunknown(w_forwarder.rd_idx));
    assert(!$isunknown(w_forwarder.rd_val_avail));
    assert(!$isunknown(w_forwarder.rd_val));


    @(negedge clk);

    test_store_data_gen();

    @(negedge clk);

    $finish;
end

endmodule : letc_core_stage_writeback_tb
