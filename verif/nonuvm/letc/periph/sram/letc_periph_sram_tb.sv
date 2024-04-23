/**
 * File    letc_periph_sram_tb.sv
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

module letc_periph_sram_tb;

import letc_pkg::*;
import axi_pkg::*;

/* ------------------------------------------------------------------------------------------------
 * Parameters
 * --------------------------------------------------------------------------------------------- */

localparam CLOCK_PERIOD = 10;

localparam DEPTH = 1024;//Depth of the SRAM (in words)

/* ------------------------------------------------------------------------------------------------
 * DUT Connections
 * --------------------------------------------------------------------------------------------- */

//Clock and reset
logic i_clk;
logic i_rst_n;

//AXI interface
axi_if axi(.i_aclk(i_clk), .i_arst_n(i_rst_n));

/* ------------------------------------------------------------------------------------------------
 * DUT
 * --------------------------------------------------------------------------------------------- */

letc_periph_sram #(
    .DEPTH(DEPTH)
) dut (
    .*
);

/* ------------------------------------------------------------------------------------------------
 * Interface Workaround
 * --------------------------------------------------------------------------------------------- */

//AW: Write Address Channel
logic                   awvalid;
logic                   awready;
logic [IDWIDTH-1:0]     awid;
logic [AWIDTH-1:0]      awaddr;
logic [LENWIDTH-1:0]    awlen;
axi_pkg::size_t         awsize;
axi_pkg::burst_e        awburst;

//W: Write Data Channel
logic                   wvalid;
logic                   wready;
logic [IDWIDTH-1:0]     wid;//Removed in AXI4; you may need to deal with/ignore this in your RTL
logic [DWIDTH-1:0]      wdata;
logic [WSTRBWIDTH-1:0]  wstrb;
logic                   wlast;

//B: Write Response Channel
logic                   bvalid;
logic                   bready;
logic [IDWIDTH-1:0]     bid;
axi_pkg::resp_e         bresp;

//AR: Read Address Channel
logic                   arvalid;
logic                   arready;
logic [IDWIDTH-1:0]     arid;
logic [AWIDTH-1:0]      araddr;
logic [LENWIDTH-1:0]    arlen;
axi_pkg::size_t         arsize;
axi_pkg::burst_e        arburst;

//R: Read Data Channel
logic                   rvalid;
logic                   rready;
logic [IDWIDTH-1:0]     rid;
logic [DWIDTH-1:0]      rdata;
axi_pkg::resp_e         rresp;
logic                   rlast;

always_comb begin
    axi.awvalid = awvalid;
    awready     = axi.awready;
    axi.awid    = awid;
    axi.awaddr  = awaddr;
    axi.awlen   = awlen;
    axi.awsize  = awsize;
    axi.awburst = awburst;

    axi.wvalid  = wvalid;
    wready      = axi.wready;
    axi.wid     = wid;
    axi.wdata   = wdata;
    axi.wstrb   = wstrb;
    axi.wlast   = wlast;

    bvalid      = axi.bvalid;
    axi.bready  = bready;
    bid         = axi.bid;
    bresp       = axi.bresp;

    axi.arvalid = arvalid;
    arready     = axi.arready;
    axi.arid    = arid;
    axi.araddr  = araddr;
    axi.arlen   = arlen;
    axi.arsize  = arsize;
    axi.arburst = arburst;

    rvalid      = axi.rvalid;
    axi.rready  = rready;
    rid         = axi.rid;
    rdata       = axi.rdata;
    rresp       = axi.rresp;
    rlast       = axi.rlast;
end

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

    //Reset
    output i_rst_n;

    //AXI interface
    //AW: Write Address Channel
    output awvalid;
    input  awready;
    output awid;
    output awaddr;
    output awlen;
    output awsize;
    output awburst;
    //W: Write Data Channel
    output wvalid;
    input  wready;
    output wid;//Removed in AXI4; you may need to deal with/ignore this in your RTL
    output wdata;
    output wstrb;
    output wlast;
    //B: Write Response Channel
    input  bvalid;
    output bready;
    input  bid;
    input  bresp;
    //AR: Read Address Channel
    output arvalid;
    input  arready;
    output arid;
    output araddr;
    output arlen;
    output arsize;
    output arburst;
    //R: Read Data Channel
    input  rvalid;
    output rready;
    input  rid;
    input  rdata;
    input  rresp;
    input  rlast;

    /* verilator lint_on UNUSEDSIGNAL */
endclocking

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

initial begin
    //Setup
    awvalid <= 1'b0;
    wvalid  <= 1'b0;
    bready  <= 1'b0;
    arvalid <= 1'b0;
    rready  <= 1'b0;

    //Reset things
    cb.i_rst_n <= 1'b0;
    ##2;
    cb.i_rst_n <= 1'b1;
    ##2;

    //TODO interesting bits here

    $finish;
end

endmodule : letc_periph_sram_tb
