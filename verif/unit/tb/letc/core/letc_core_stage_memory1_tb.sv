/**
 * File    letc_core_stage_memory1_tb.sv
 * Brief   Testing the LETC core memory 1 stage
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

module letc_core_stage_memory1_tb;

import riscv_pkg::*;
import letc_pkg::*;
import letc_core_pkg::*;

/* ------------------------------------------------------------------------------------------------
 * DUT
 * --------------------------------------------------------------------------------------------- */

logic       clk;
logic       rst_n;
logic       m1_ready;
logic       m1_flush;
logic       m1_stall;
logic       branch_taken;
word_t      branch_target;
logic       e_to_m1_valid;
e_to_m1_s   e_to_m1;
logic       m1_to_m2_valid;
m1_to_m2_s  m1_to_m2;
letc_core_dmss_if dmss_if();
letc_core_forwarder_if m1_forwarder();
letc_core_forwardee_if m1_forwardee_rs2();

letc_core_stage_memory1 dut(.*);

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
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

initial begin
    rst_n <= 1'b0;
    m1_flush <= 1'b0;
    m1_stall <= 1'b0;
    e_to_m1_valid <= 1'b0;
    e_to_m1 <= '0;
    e_to_m1.alu_result <= 32'd9;
    m1_forwardee_rs2.use_fwd <= 1'b0;
    m1_forwardee_rs2.fwd_val <= '0;

    @(negedge clk);

    rst_n <= 1'b1;

    @(negedge clk);

    assert(!$isunknown(m1_forwarder.instr_produces_rd));
    assert(!$isunknown(m1_forwarder.rd_idx));
    assert(!$isunknown(m1_forwarder.rd_val_avail));
    assert(!$isunknown(m1_forwarder.rd_val));
    assert(!$isunknown(m1_forwardee_rs2.stage_uses_reg));
    assert(!$isunknown(m1_forwardee_rs2.reg_idx));

    $finish;
end

endmodule : letc_core_stage_memory1_tb
