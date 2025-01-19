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
reg_idx_t   rd_idx;
word_t      rd_val;
logic       rd_wen;

//rs1 Read Port
reg_idx_t   rs1_idx;
word_t      rs1_val;

//rs2 Read Port
reg_idx_t   rs2_idx;
word_t      rs2_val;

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
    rd_idx  <= '0;
    rd_val  <= '0;
    rd_wen  <= 1'b0;
    rs1_idx <= '0;
    rs2_idx <= '0;
end
endtask

task write(input reg_idx_t new_rd_idx, input word_t new_rd_wdata);
begin
    rd_idx  <= new_rd_idx;
    rd_val  <= new_rd_wdata;
    rd_wen  <= 1'b1;
end
endtask

task nowrite();
begin
    rd_idx  <= 'x;
    rd_val  <= 'x;
    rd_wen  <= 1'b0;
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
    rs1_idx <= 5'h1A;
    rs2_idx <= 5'h0;
    @(negedge clk);
    rs1_idx <= 'x;
    rs2_idx <= 'x;
    assert(rs1_val == 32'hABCD1234);
    assert(rs2_val == '0);//x0 is always 0
    repeat(3) @(negedge clk);

    //Reads and writes in the same cycle
    rs1_idx <= 5'h10;
    rs2_idx <= 5'hB;
    write(5'h10, 32'h12345678);
    #1;
    assert(rs1_val == 32'h12345678);//Write should be forwarded to read (read NEW data)
    assert(rs2_val == 32'hBBBBBBBB);//This should NOT be forwarded
    @(negedge clk);//Now the write has happened
    repeat(3) @(negedge clk);

    repeat(5) @(negedge clk);
    $finish;
    //verilator lint_restore
end

endmodule : letc_core_rf_tb
