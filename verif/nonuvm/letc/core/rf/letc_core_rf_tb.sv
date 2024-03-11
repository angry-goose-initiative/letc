/**
 * File    letc_core_rf_tb.sv
 * Brief   TODO
 * 
 * Copyright:
 *  Copyright (C) 2024 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 * 
 * TODO longer description
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_rf_tb;

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
logic i_clk;

//rd Write Port
reg_idx_t   i_rd_idx;
word_t      i_rd_wdata;
logic       i_rd_wen;

//rs1 Read Port
reg_idx_t   i_rs1_idx;
word_t      o_rs1_rdata;

//rs2 Read Port
reg_idx_t   i_rs2_idx;
word_t      o_rs2_rdata;

/* ------------------------------------------------------------------------------------------------
 * DUT
 * --------------------------------------------------------------------------------------------- */

letc_core_rf dut (.*);

/* ------------------------------------------------------------------------------------------------
 * Clocking
 * --------------------------------------------------------------------------------------------- */

initial begin
    forever begin
        i_clk = 1'b0;
        #(CLOCK_PERIOD / 2);
        i_clk = 1'b1;
        #(CLOCK_PERIOD / 2);
    end
end

default clocking cb @(posedge i_clk);
    //Not sure why Verilator complains...
    /* verilator lint_off UNUSEDSIGNAL */

    //rd Write Port
    output  i_rd_idx;
    output  i_rd_wdata;
    output  i_rd_wen;

    //rs1 Read Port
    output  i_rs1_idx;
    input   o_rs1_rdata;

    //rs2 Read Port
    output  i_rs2_idx;
    input   o_rs2_rdata;

    /* verilator lint_on UNUSEDSIGNAL */
endclocking

/* ------------------------------------------------------------------------------------------------
 * Tasks
 * --------------------------------------------------------------------------------------------- */

//Note: due to quirks with Verilator, sadly we should try to avoid waiting for the next posedge in tasks

task setup();
begin
    //Set initial input states
    cb.i_rd_idx     <= '0;
    cb.i_rd_wdata   <= '0;
    cb.i_rd_wen     <= 1'b0;
    cb.i_rs1_idx    <= '0;
    cb.i_rs2_idx    <= '0;
end
endtask

task write(input reg_idx_t rd_idx, input word_t rd_wdata);
begin
    cb.i_rd_idx     <= rd_idx;
    cb.i_rd_wdata   <= rd_wdata;
    cb.i_rd_wen     <= 1'b1;
end
endtask

task nowrite();
begin
    cb.i_rd_idx     <= 'x;
    cb.i_rd_wdata   <= 'x;
    cb.i_rd_wen     <= 1'b0;
end
endtask

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

initial begin
    setup();
    ##1;

    //Some writes
    write(5'h1A, 32'hABCD1234);
    ##1;//One cycle for the inputs to be sent (testbench delay)
    nowrite();
    ##1;//One cycle for the write to happen
    write(5'h0, 32'h55555555);//Should get ignored
    ##1;
    write(5'hB, 32'hBBBBBBBB);
    ##1;
    nowrite();
    ##3;

    //Some reads
    cb.i_rs1_idx <= 5'h1A;
    cb.i_rs2_idx <= 5'h0;
    ##1;//So the idx being set actually takes effect
    cb.i_rs1_idx <= 'x;
    cb.i_rs2_idx <= 'x;
    assert(cb.o_rs1_rdata == 32'hABCD1234);
    assert(cb.o_rs2_rdata == '0);//x0 is always 0
    ##3;

    //Reads and writes in the same cycle
    cb.i_rs1_idx <= 5'h10;
    cb.i_rs2_idx <= 5'hB;
    write(5'h10, 32'h12345678);
    ##1;//So the idxs being set actually takes effect, and the write inputs are sent. But the write hasn't happened yet
    cb.i_rs1_idx <= 'x;
    cb.i_rs2_idx <= 'x;
    nowrite();
    assert(cb.o_rs1_rdata == 32'h12345678);//Write should be forwarded to read
    assert(cb.o_rs2_rdata == 32'hBBBBBBBB);//This should NOT be forwarded
    ##1;//Now the write has happened
    ##3;

    ##5;
    $finish;
end

endmodule : letc_core_rf_tb
