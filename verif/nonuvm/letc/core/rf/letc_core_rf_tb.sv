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
logic i_rst_n;

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
    i_rd_idx    <= '0;
    i_rd_wdata  <= '0;
    i_rd_wen    <= 1'b0;
    i_rs1_idx   <= '0;
    i_rs2_idx   <= '0;
end
endtask

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

initial begin
    setup();

    //Reset things
    i_rst_n = 1'b0;
    ##2;
    i_rst_n = 1'b1;
    ##2;

    //TODO

    ##5;
    $finish;
end

endmodule : letc_core_rf_tb
