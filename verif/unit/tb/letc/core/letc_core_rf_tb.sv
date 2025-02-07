/**
 * File    letc_core_rf_tb.sv
 * Brief   TODO
 *
 * Copyright:
 *  Copyright (C) 2024-2025 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_rf_tb;

import riscv_pkg::*;
import letc_pkg::*;
import letc_core_pkg::*;

/* ------------------------------------------------------------------------------------------------
 * Parameters
 * --------------------------------------------------------------------------------------------- */

localparam CLOCK_PERIOD = 10;

/* ------------------------------------------------------------------------------------------------
 * DUT Connections
 * --------------------------------------------------------------------------------------------- */

//Clock and reset
logic clk;

//rd Write Port
reg_idx_t   rf_rd_idx;
word_t      rf_rd_val;
logic       rf_rd_we;

//rs1 Read Port
reg_idx_t   rf_rs1_idx;
word_t      rf_rs1_val;

//rs2 Read Port
reg_idx_t   rf_rs2_idx;
word_t      rf_rs2_val;

/* ------------------------------------------------------------------------------------------------
 * DUT
 * --------------------------------------------------------------------------------------------- */

letc_core_rf dut (.*);

/* ------------------------------------------------------------------------------------------------
 * Clocking
 * --------------------------------------------------------------------------------------------- */

clock_generator #(
    .PERIOD(CLOCK_PERIOD)
) clock_gen_inst (
    .clk(clk)
);

/* ------------------------------------------------------------------------------------------------
 * Tasks
 * --------------------------------------------------------------------------------------------- */

//verilator lint_save
//verilator lint_off INITIALDLY

//Note: due to quirks with Verilator, sadly we should try to avoid waiting for the next posedge in tasks

task setup();
begin
    //Set initial input states
    rf_rd_idx  <= '0;
    rf_rd_val  <= '0;
    rf_rd_we   <= 1'b0;
    rf_rs1_idx <= '0;
    rf_rs2_idx <= '0;
end
endtask

task write(input reg_idx_t new_rd_idx, input word_t new_rd_wdata);
begin
    rf_rd_idx  <= new_rd_idx;
    rf_rd_val  <= new_rd_wdata;
    rf_rd_we   <= 1'b1;
end
endtask

task nowrite();
begin
    rf_rd_idx  <= 'x;
    rf_rd_val  <= 'x;
    rf_rd_we   <= 1'b0;
end
endtask

//verilator lint_restore

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

initial begin
    //verilator lint_save
    //verilator lint_off INITIALDLY
    setup();
    @(negedge clk);

    //Some writes
    write(5'h1A, 32'hABCD1234);
    @(negedge clk);//One cycle for the write to happen
    write(5'h0, 32'h55555555);//Should get ignored
    @(negedge clk);
    write(5'hB, 32'hBBBBBBBB);
    @(negedge clk);
    nowrite();
    repeat(3) @(negedge clk);

    //Some reads
    rf_rs1_idx <= 5'h1A;
    rf_rs2_idx <= 5'h0;
    @(negedge clk);
    rf_rs1_idx <= 'x;
    rf_rs2_idx <= 'x;
    assert(rf_rs1_val == 32'hABCD1234);
    assert(rf_rs2_val == '0);//x0 is always 0
    repeat(3) @(negedge clk);

    //Reads and writes in the same cycle
    rf_rs1_idx <= 5'h10;
    rf_rs2_idx <= 5'hB;
    write(5'h10, 32'h12345678);
    #1;
    assert(rf_rs1_val == 32'h12345678);//Write should be forwarded to read (read NEW data)
    assert(rf_rs2_val == 32'hBBBBBBBB);//This should NOT be forwarded
    @(negedge clk);//Now the write has happened
    repeat(3) @(negedge clk);

    repeat(5) @(negedge clk);
    $finish;
    //verilator lint_restore
end

endmodule : letc_core_rf_tb
