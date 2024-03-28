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
initial begin
    forever begin
        i_clk = 1'b0;
        #(CLOCK_PERIOD / 2);
        i_clk = 1'b1;
        #(CLOCK_PERIOD / 2);
    end
end

//For advanced reasons that we won't get into now, when driving synchronous signals from a testbench,
//it's important to do so through a clocking block. Otherwise you may run into problems due to your
//signals being asynchronous to the clock.
default clocking cb @(posedge i_clk);
    //The directions are opposite that of the DUT
    output i_rst_n;

    output a1;
    output b1;
    input  c1;

    output a2;
    output b2;
    output c2;
    input  d2;

    output a3;
    output b3;
    input  c3;

    input  counter_out;

    output a4;
    input  b4;
endclocking

initial begin
    $display("Running the example_tb testbench!");

    //Set initial input values
    cb.a1 <= 1'b0;
    cb.b1 <= 1'b0;
    cb.a2 <= 1'b0;
    cb.b2 <= 1'b0;
    cb.c2 <= 1'b0;
    cb.a3 <= 1'b0;
    cb.b3 <= 1'b0;
    cb.a4 <= 1'b0;

    //Reset things
    cb.i_rst_n <= 1'b0;
    ##5;//Wait 5 clock cycles
    //A couple of idle cycles before we begin
    cb.i_rst_n <= 1'b1;
    ##5;//Wait 5 clock cycles

    //Try some different inputs
    cb.a1 <= 1'b1;
    cb.b1 <= 1'b1;
    cb.a2 <= 1'b0;
    cb.b2 <= 1'b1;
    cb.c2 <= 1'b1;
    cb.a3 <= 1'b0;
    cb.b3 <= 1'b1;
    cb.a4 <= 1'b1;
    ##2;//Wait two clock cycles

    //Try some different inputs
    cb.a1 <= 1'b0;
    cb.b1 <= 1'b1;
    cb.a2 <= 1'b1;
    cb.b2 <= 1'b0;
    cb.c2 <= 1'b0;
    cb.a3 <= 1'b1;
    cb.b3 <= 1'b1;
    cb.a4 <= 1'b0;
    ##2;//Wait two clock cycles

    ##30;//Wait 30 clock cycles to see more things happen and the counter wrap around
    $display("All done!");
    $finish;
end

endmodule : example_tb
