/*
 * File:    letc_core_forwarding_factory_tb.sv
 * Brief:   Testing the forwarding factory
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

module letc_core_forwarding_factory_tb;

import riscv_pkg::*;
import letc_pkg::*;
import letc_core_pkg::*;

/* ------------------------------------------------------------------------------------------------
 * DUT
 * --------------------------------------------------------------------------------------------- */

letc_core_forwardee_if  e_forwardee_rs1();
letc_core_forwardee_if  e_forwardee_rs2();
letc_core_forwardee_if m1_forwardee_rs2();
letc_core_forwardee_if m2_forwardee_rs2();

letc_core_forwarder_if m1_forwarder();
letc_core_forwarder_if m2_forwarder();
letc_core_forwarder_if  w_forwarder();

logic e_unforwardable_hazard;
logic m1_unforwardable_hazard;
logic m2_unforwardable_hazard;

letc_core_forwarding_factory dut(.*);

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

initial begin
    e_forwardee_rs1.stage_uses_reg <= 1'b1;
    m1_forwardee_rs2.stage_uses_reg <= 1'b1;
    e_forwardee_rs2.stage_uses_reg <= 1'b1;
    m2_forwardee_rs2.stage_uses_reg <= 1'b1;
    m1_forwarder.rd_val_avail <= 1'b1;
    m2_forwarder.rd_val_avail <= 1'b1;
    w_forwarder.rd_val_avail <= 1'b1;

    // These values won't change during the test
    m1_forwarder.rd_val <= 32'h11111111;
    m2_forwarder.rd_val <= 32'h22222222;
    w_forwarder.rd_val <= 32'h33333333;

    e_forwardee_rs1.reg_idx <= 5'd10;

    e_forwardee_rs2.reg_idx <= 5'd11;

    m1_forwardee_rs2.reg_idx <= 5'd12;

    m2_forwardee_rs2.reg_idx <= 5'd13;

    m1_forwarder.rd_idx <= 5'd10;
    m1_forwarder.instr_produces_rd <= 1'b0;

    m2_forwarder.rd_idx <= 5'd11;
    m2_forwarder.instr_produces_rd <= 1'b0;

    w_forwarder.rd_idx <= 5'd12;
    w_forwarder.instr_produces_rd <= 1'b0;

    #10;

    assert(e_forwardee_rs1.use_fwd == 1'b0);

    $finish;
end

endmodule : letc_core_forwarding_factory_tb
