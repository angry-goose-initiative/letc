/*
 * File:    shift_register_tb.sv
 * Brief:   Quick and dirty verif for the shift_register module
 *
 * Copyright:
 *  Copyright (C) 2024 Eric Jessee
 * See the LICENSE file at the root of the project for licensing info.
 *
 */

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module shift_register_tb;

/* ------------------------------------------------------------------------------------------------
 * Parameters
 * --------------------------------------------------------------------------------------------- */

localparam CLOCK_PERIOD = 10;
localparam SHIFT_REG_WIDTH = 8;

/* ------------------------------------------------------------------------------------------------
 * DUT Connections
 * --------------------------------------------------------------------------------------------- */

logic i_clk;
logic i_rst_n;

logic i_sdata;
logic i_shift;
logic i_load;
logic [SHIFT_REG_WIDTH-1:0] i_ldata;

logic [SHIFT_REG_WIDTH-1:0] o_data;
logic o_carryout;

/* ------------------------------------------------------------------------------------------------
 * DUT
 * --------------------------------------------------------------------------------------------- */

//We insanciate the device under test (DUT), in this case our example_top module, here!
shift_register #(
    .WIDTH(SHIFT_REG_WIDTH)
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

    output i_sdata;
    output i_shift;
    output i_load;
    output i_ldata;

    input o_data;
    input o_carryout;
endclocking

initial begin
    //Set initial input values
    cb.i_rst_n <= 0;
    cb.i_sdata <= 0;
    cb.i_shift <= 0;
    ##1
    cb.i_rst_n <= 0;
    ##1
    cb.i_rst_n <= 1;
    ##1
    cb.i_ldata <= 'b1;
    cb.i_load <= 1;
    ##1
    cb.i_load <= 0;
    cb.i_shift <= 1;
    ##(SHIFT_REG_WIDTH+2)
    cb.i_shift <= 0;
    ##5
    $finish;
end

endmodule : shift_register_tb
