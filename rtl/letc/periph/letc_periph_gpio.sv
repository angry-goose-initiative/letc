/*
 * File:    letc_periph_gpio.sv
 * Brief:   LETC AXI GPIO peripheral
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

module letc_periph_gpio
    import letc_pkg::*;
    import axi_pkg::*;
#(
    localparam NUM_LINES = WORD_WIDTH//Number of GPIO lines
) (
    //Clock and reset
    input logic i_clk,
    input logic i_rst_n,

    //AXI interface
    axi_if.subordinate axi,

    //GPIO interface (no bidirectionality for simplicity)
    input  logic [NUM_LINES-1:0] i_gpio,//Reads return the value on these lines
    output logic [NUM_LINES-1:0] o_gpio//Writes output the value on these lines
);

//TODO
assign o_gpio = '0;

endmodule : letc_periph_gpio
