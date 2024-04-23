/*
 * File:    letc_periph_sram.sv
 * Brief:   LETC AXI SRAM peripheral
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

module letc_periph_sram
    import letc_pkg::*;
    import axi_pkg::*;
#(
    parameter   DEPTH   = 1024,//Depth of the SRAM (in words)
    localparam  DWIDTH  = WORD_WIDTH,//Always 32-bits wide
    localparam  AWIDTH  = $clog2(DEPTH)//Address bits above this are ignored (aliasing/mirroring used)
) (
    //Clock and reset
    input logic i_clk,
    input logic i_rst_n,

    //AXI interface
    axi_if.subordinate axi
);

//TODO
assign axi.awready  = 1'b0;
assign axi.wready   = 1'b0;
assign axi.bvalid   = 1'b0;
assign axi.arready  = 1'b0;
assign axi.rvalid   = 1'b0;

endmodule : letc_periph_sram
