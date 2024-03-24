/**
 * File    letc_core_stage_e1_tb.sv
 * Brief   Testbench for LETC Core 1st Execute stage
 * 
 * Copyright:
 *  Copyright (C) 2024 John Jekel
 *  Copyright (C) 2024 Eric Jessee
 * See the LICENSE file at the root of the project for licensing info.
 * 
 * TODO Longer description
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_stage_e1_tb;

import letc_pkg::*;
import letc_core_pkg::*;

/* ------------------------------------------------------------------------------------------------
 * Parameters:
 *
 * --------------------------------------------------------------------------------------------- */

localparam CLOCK_PERIOD = 10;

/* ------------------------------------------------------------------------------------------------
 * DUT Connections
 * --------------------------------------------------------------------------------------------- */

//Clock and reset
logic i_clk;
logic i_rst_n;

//IO
letc_core_tlb_if dtlb_if(.i_clk(i_clk), .i_rst_n(i_rst_n));
d_to_e1_s i_d_to_e1;
e1_to_e2_s o_e1_to_e2;

//Hazards
logic o_stage_ready;
logic i_stage_flush;
logic i_stage_stall;

//Debug
logic [7:0] o_debug;

/* ------------------------------------------------------------------------------------------------
 * DUT
 * --------------------------------------------------------------------------------------------- */

letc_core_stage_e1 dut (.*);

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

    output i_rst_n;

    //IO
    output i_d_to_e1;
    input o_e1_to_e2;

    //Hazards 
    input o_stage_ready;
    output i_stage_flush;
    output i_stage_stall;

    //Debug
    input   o_debug;

    /* verilator lint_on UNUSEDSIGNAL */
endclocking

/* ------------------------------------------------------------------------------------------------
 * Tasks
 * --------------------------------------------------------------------------------------------- */

//Note: due to quirks with Verilator, sadly we should try to avoid waiting for the next posedge in tasks

task setup();

    //Set initial input states
    cb.i_stage_stall <= 1'b0;
    cb.i_stage_flush <= 1'b0;
    cb.i_d_to_e1.valid <= 1'b0;
    cb.i_d_to_e1.rs1_rdata <= 32'h5;
    cb.i_d_to_e1.rs2_rdata <= 32'h5;
endtask

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

initial begin
    setup();

    //Reset things
    cb.i_rst_n <= 1'b0;
    ##2;
    cb.i_rst_n <= 1'b1;
    ##2;
    cb.i_d_to_e1.valid <= 1'b1;
    ##5;
    $finish;
end

endmodule : letc_core_stage_e1_tb
