/*
 * File:    example_tb.sv
 * Brief:   An example SystemVerilog package file
 *
 * Copyright:
 *  Copyright (C) 2024 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * This file is part of a set of example files used to demonstrate
 * hardware/RTL/SystemVerilog concepts to those new to digital logic design.
 *
 * Testbenches drive test signals into a DUT (Device Under Test) and check the outputs.
 *
 * Run this testbench with `make waves TBENCH=example` from the `verif/nonuvm` directory.
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module example_tb;

import example_pkg::*;

/* ------------------------------------------------------------------------------------------------
 * Parameters
 * --------------------------------------------------------------------------------------------- */

localparam CLOCK_PERIOD = 10;

/* ------------------------------------------------------------------------------------------------
 * DUT Connections
 * --------------------------------------------------------------------------------------------- */

//verilator lint_save
//verilator lint_off UNUSEDSIGNAL

//Clock and reset lines
logic i_clk;
logic i_rst_n;//_n means active low

//Inputs and outputs
logic    a1;
logic    b1;
logic    c1;

logic    a2;
logic    b2;
logic    c2;
logic    d2;

logic    a3;
logic    b3;
logic    c3;

//This type is defined in the example_pkg and is 5 bits wide
example_type_t counter_out;

logic a4;
logic b4;

//verilator lint_restore

/* ------------------------------------------------------------------------------------------------
 * DUT
 * --------------------------------------------------------------------------------------------- */

//We insanciate the device under test (DUT), in this case our example_top module, here!
example_top dut (
    .*//Hook up all the inputs and outputs to their corresponding signals in the testbench
);

/* ------------------------------------------------------------------------------------------------
 * Clocking
 * --------------------------------------------------------------------------------------------- */

//Generate a clock signal for testing!
clock_generator #(
    .PERIOD(CLOCK_PERIOD)
) clock_gen_inst (
    .clk(i_clk)
);

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

initial begin
    //verilator lint_save
    //verilator lint_off INITIALDLY
    $display("Running the example_tb testbench!");

    //Set initial input values
    a1 <= 1'b0;
    b1 <= 1'b0;
    a2 <= 1'b0;
    b2 <= 1'b0;
    c2 <= 1'b0;
    a3 <= 1'b0;
    b3 <= 1'b0;
    a4 <= 1'b0;

    //Reset things
    i_rst_n <= 1'b0;
    repeat (5) @(negedge i_clk);//Wait 5 clock cycles
    //A couple of idle cycles before we begin
    i_rst_n <= 1'b1;
    repeat (5) @(negedge i_clk);//Wait 5 clock cycles

    //Try some different inputs
    a1 <= 1'b1;
    b1 <= 1'b1;
    a2 <= 1'b0;
    b2 <= 1'b1;
    c2 <= 1'b1;
    a3 <= 1'b0;
    b3 <= 1'b1;
    a4 <= 1'b1;
    repeat (2) @(negedge i_clk);//Wait 2 clock cycles

    //Try some different inputs
    a1 <= 1'b0;
    b1 <= 1'b1;
    a2 <= 1'b1;
    b2 <= 1'b0;
    c2 <= 1'b0;
    a3 <= 1'b1;
    b3 <= 1'b1;
    a4 <= 1'b0;
    repeat (2) @(negedge i_clk);//Wait 2 clock cycles

    repeat (30) @(negedge i_clk);//Wait 30 clock cycles to see more things happen and the counter wrap around
    $display("All done!");
    $finish;
    //verilator lint_restore
end

endmodule : example_tb
