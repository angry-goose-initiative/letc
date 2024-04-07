/*
 * File:    shift_register_tb.sv
 * Brief:   Quick and dirty verif for the address_counter module
 *
 * Copyright:
 *  Copyright (C) 2024 Eric Jessee
 * See the LICENSE file at the root of the project for licensing info.
 *
 */

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module counter_tb;
import letc_pkg::*;

/* ------------------------------------------------------------------------------------------------
 * Parameters
 * --------------------------------------------------------------------------------------------- */

localparam CLOCK_PERIOD = 10;

/* ------------------------------------------------------------------------------------------------
 * DUT Connections
 * --------------------------------------------------------------------------------------------- */

logic i_clk;
logic i_rst_n;

//address in/out
logic [PADDR_WIDTH-1:0]  i_addr;
logic [PADDR_WIDTH-1:0]  o_addr;
//control signals
logic i_en;
logic i_load; // load == !count

/* ------------------------------------------------------------------------------------------------
 * DUT
 * --------------------------------------------------------------------------------------------- */

//We insanciate the device under test (DUT), in this case our example_top module, here!
counter #(
    .WIDTH(PADDR_WIDTH),
    .STEP(4)
) dut (
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
    output i_clk;
    output i_rst_n;
    //address in/out
    output i_addr;
    input  o_addr;
    //control signals
    output i_en;
    output i_load; // load == !count
endclocking

initial begin
    //Set initial input values
    cb.i_rst_n <= 0;
    cb.i_en <= 0;
    cb.i_load <= 0;
    ##1
    cb.i_rst_n <= 0;
    ##1
    cb.i_rst_n <= 1;
    ##1
    cb.i_addr <= 32'hdeef0000;
    cb.i_load <= 1;
    cb.i_en <= 1;
    ##1
    cb.i_load <= 0;
    ##5
    cb.i_en <= 0;
    ##5
    $finish;
end

endmodule : counter_tb
