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
logic       e_to_m1_valid;
e_to_m1_s   e_to_m1;
logic       m1_to_m2_valid;
m1_to_m2_s  m1_to_m2;
letc_core_dmss_if dmss_if();

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
    rst_n = 1'b0;
    m1_flush = 1'b0;
    m1_stall = 1'b0;
    e_to_m1_valid = 1'b0;
    e_to_m1 = '0;
    e_to_m1.alu_result = 32'd9;

    $finish;
end

endmodule : letc_core_stage_memory1_tb
