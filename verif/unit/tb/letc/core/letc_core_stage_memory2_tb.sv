/*
 * File:    letc_core_stage_memory2_tb.sv
 * Brief:   Testing the LETC core memory 2 stage
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

module letc_core_stage_memory2_tb;

import riscv_pkg::*;
import letc_pkg::*;
import letc_core_pkg::*;

/* ------------------------------------------------------------------------------------------------
 * DUT
 * --------------------------------------------------------------------------------------------- */

logic       clk;
logic       rst_n;
logic       m2_ready;
logic       m2_flush;
logic       m2_stall;
logic       m1_to_m2_valid;
m1_to_m2_s  m1_to_m2;
logic       m2_to_w_valid;
m2_to_w_s   m2_to_w;
letc_core_dmss_if dmss_if();
letc_core_forwarder_if m2_forwarder();
letc_core_forwardee_if m2_forwardee_rs2();

letc_core_stage_memory2 dut(.*);

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
    input   logic       mem_signed,
    input   word_t      addr,
    input   word_t      data,
    input   word_t      expected
);
    m1_to_m2.mem_size <= mem_size;
    m1_to_m2.mem_signed <= mem_signed;
    m1_to_m2.alu_result <= addr;
    dmss_if.dmss1_rsp_ready <= 1'b1;
    @(negedge clk);
    dmss_if.dmss1_rsp_load_data <= data;
    #1;
    assert(m2_to_w.mem_rdata == expected);
endtask

task test_loads();
    m1_to_m2.mem_op <= MEM_OP_LOAD;
    dmss_if.dmss1_rsp_ready <= 1'b1;

    test_mem_with_params(
        .mem_size(MEM_SIZE_WORD),
        .mem_signed(1'b0),
        .addr(32'h00000000),
        .data(32'h11223344),
        .expected(32'h11223344)
    );
    test_mem_with_params(
        .mem_size(MEM_SIZE_HALFWORD),
        .mem_signed(1'b0),
        .addr(32'h00000000),
        .data(32'h11223344),
        .expected(32'h00003344)
    );
    test_mem_with_params(
        .mem_size(MEM_SIZE_HALFWORD),
        .mem_signed(1'b0),
        .addr(32'h00000002),
        .data(32'h11223344),
        .expected(32'h00001122)
    );
    test_mem_with_params(
        .mem_size(MEM_SIZE_BYTE),
        .mem_signed(1'b0),
        .addr(32'h00000000),
        .data(32'h11223344),
        .expected(32'h00000044)
    );
    test_mem_with_params(
        .mem_size(MEM_SIZE_BYTE),
        .mem_signed(1'b0),
        .addr(32'h00000001),
        .data(32'h11223344),
        .expected(32'h00000033)
    );
    test_mem_with_params(
        .mem_size(MEM_SIZE_BYTE),
        .mem_signed(1'b0),
        .addr(32'h00000002),
        .data(32'h11223344),
        .expected(32'h00000022)
    );
    test_mem_with_params(
        .mem_size(MEM_SIZE_BYTE),
        .mem_signed(1'b0),
        .addr(32'h00000003),
        .data(32'h11223344),
        .expected(32'h00000011)
    );
    test_mem_with_params(
        .mem_size(MEM_SIZE_HALFWORD),
        .mem_signed(1'b1),
        .addr(32'h00000000),
        .data(32'h00008000),
        .expected(32'hFFFF8000)
    );
    test_mem_with_params(
        .mem_size(MEM_SIZE_BYTE),
        .mem_signed(1'b1),
        .addr(32'h00000000),
        .data(32'h00000080),
        .expected(32'hFFFFFF80)
    );
endtask

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

initial begin
    rst_n <= 1'b0;
    m2_flush <= 1'b0;
    m2_stall <= 1'b0;
    m1_to_m2_valid <= 1'b0;
    m1_to_m2 <= '0;
    m2_forwardee_rs2.use_fwd <= 1'b0;
    m2_forwardee_rs2.fwd_val <= '0;
    dmss_if.dmss1_rsp_ready <= 1'b0;
    dmss_if.dmss1_rsp_load_data <= '0;

    @(negedge clk);

    rst_n <= 1'b1;
    m1_to_m2_valid <= 1'b1;

    @(negedge clk);

    assert(!$isunknown(m2_forwarder.instr_produces_rd));
    assert(!$isunknown(m2_forwarder.rd_idx));
    assert(!$isunknown(m2_forwarder.rd_val_avail));
    assert(!$isunknown(m2_forwarder.rd_val));
    assert(!$isunknown(m2_forwardee_rs2.stage_uses_reg));
    assert(!$isunknown(m2_forwardee_rs2.reg_idx));

    @(negedge clk);

    test_loads();

    @(negedge clk);

    $finish;
end

endmodule : letc_core_stage_memory2_tb
