/*
 * File:    axi_buffer.sv
 * Brief:   Bidirectional buffer for AXI requests
 *
 * Copyright:
 *  Copyright (C) 2024 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * NOT for CDC. The clocks and resets of both AXI interfaces must be identical.
 *
 * A synchronous reset is employed as this is tuned for FPGA use
 *
 * fifo_0r1w is perfect for this! This results in this buffer adding one cycle of latency.
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module axi_buffer
    import axi_pkg::*;
#(
    //FIXME need to be able to vary field widths just like axi_if from axi_pkg
    parameter AWDEPTH   = 2,
    parameter WDEPTH    = 2,
    parameter BDEPTH    = 2,
    parameter ARDEPTH   = 2,
    parameter RDEPTH    = 2
) (
    //Clock and reset
    input logic i_clk,
    input logic i_rst_n,

    //AXI ports
    axi_if.subordinate  from_manager,
    axi_if.manager      to_subordinate
);

/* ------------------------------------------------------------------------------------------------
 * AW Buffer
 * --------------------------------------------------------------------------------------------- */

logic awfifo_full, awfifo_empty;

typedef struct packed {
    id_t    awid;
    addr_t  awaddr;
    len_t   awlen;
    size_t  awsize;
    burst_e awburst;
} aw_s;

aw_s aw_from_manager, aw_to_subordinate;

always_comb begin
    from_manager.awready    = !awfifo_full;
    aw_from_manager.awid    = from_manager.awid;
    aw_from_manager.awaddr  = from_manager.awaddr;
    aw_from_manager.awlen   = from_manager.awlen;
    aw_from_manager.awsize  = from_manager.awsize;
    aw_from_manager.awburst = from_manager.awburst;

    to_subordinate.awvalid  = !awfifo_empty;
    to_subordinate.awid     = aw_to_subordinate.awid;
    to_subordinate.awaddr   = aw_to_subordinate.awaddr;
    to_subordinate.awlen    = aw_to_subordinate.awlen;
    to_subordinate.awsize   = aw_to_subordinate.awsize;
    to_subordinate.awburst  = aw_to_subordinate.awburst;
end

fifo_0r1w #(
    .DWIDTH($bits(aw_s)),
    .DEPTH(AWDEPTH)
) awfifo (
    //Clock and reset
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),

    //Write port (1-cycle latency)
    .i_push(from_manager.awvalid),
    .o_full(awfifo_full),
    .i_wdata(aw_from_manager),

    //Read port (0-cycle latency)
    .i_pop(to_subordinate.awready),
    .o_empty(awfifo_empty),
    .o_rdata(aw_to_subordinate)
);

/* ------------------------------------------------------------------------------------------------
 * W Buffer
 * --------------------------------------------------------------------------------------------- */

logic wfifo_full, wfifo_empty;

typedef struct packed {
    id_t    wid;
    data_t  wdata;
    wstrb_t wstrb;
    logic   wlast;
} w_s;

w_s w_from_manager, w_to_subordinate;

always_comb begin
    from_manager.wready     = !wfifo_full;
    w_from_manager.wid      = from_manager.wid;
    w_from_manager.wdata    = from_manager.wdata;
    w_from_manager.wstrb    = from_manager.wstrb;
    w_from_manager.wlast    = from_manager.wlast;

    to_subordinate.wvalid   = !wfifo_empty;
    to_subordinate.wid      = w_to_subordinate.wid;
    to_subordinate.wdata    = w_to_subordinate.wdata;
    to_subordinate.wstrb    = w_to_subordinate.wstrb;
    to_subordinate.wlast    = w_to_subordinate.wlast;
end

fifo_0r1w #(
    .DWIDTH($bits(w_s)),
    .DEPTH(WDEPTH)
) wfifo (
    //Clock and reset
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),

    //Write port (1-cycle latency)
    .i_push(from_manager.wvalid),
    .o_full(wfifo_full),
    .i_wdata(w_from_manager),

    //Read port (0-cycle latency)
    .i_pop(to_subordinate.wready),
    .o_empty(wfifo_empty),
    .o_rdata(w_to_subordinate)
);

/* ------------------------------------------------------------------------------------------------
 * B Buffer
 * --------------------------------------------------------------------------------------------- */

//"from_manager" and "to_subordinate" are misnomers for this since info flows the other way

logic bfifo_full, bfifo_empty;

typedef struct packed {
    id_t    bid;
    resp_e  bresp;
} b_s;//lol

b_s b_from_subordinate, b_to_manager;

always_comb begin
    to_subordinate.bready       = !bfifo_full;
    b_from_subordinate.bid      = to_subordinate.bid;
    b_from_subordinate.bresp    = to_subordinate.bresp;

    from_manager.bvalid         = !bfifo_empty;
    from_manager.bid            = b_to_manager.bid;
    from_manager.bresp          = b_to_manager.bresp;
end

fifo_0r1w #(
    .DWIDTH($bits(b_s)),
    .DEPTH(BDEPTH)
) bfifo (
    //Clock and reset
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),

    //Write port (1-cycle latency)
    .i_push(to_subordinate.bvalid),
    .o_full(bfifo_full),
    .i_wdata(b_from_subordinate),

    //Read port (0-cycle latency)
    .i_pop(from_manager.bready),
    .o_empty(bfifo_empty),
    .o_rdata(b_to_manager)
);

/* ------------------------------------------------------------------------------------------------
 * AR Buffer
 * --------------------------------------------------------------------------------------------- */

logic arfifo_full, arfifo_empty;

typedef struct packed {
    id_t    arid;
    addr_t  araddr;
    len_t   arlen;
    size_t  arsize;
    burst_e arburst;
} ar_s;

ar_s ar_from_manager, ar_to_subordinate;

always_comb begin
    from_manager.arready    = !arfifo_full;
    ar_from_manager.arid    = from_manager.arid;
    ar_from_manager.araddr  = from_manager.araddr;
    ar_from_manager.arlen   = from_manager.arlen;
    ar_from_manager.arsize  = from_manager.arsize;
    ar_from_manager.arburst = from_manager.arburst;

    to_subordinate.arvalid  = !awfifo_empty;
    to_subordinate.arid     = ar_to_subordinate.arid;
    to_subordinate.araddr   = ar_to_subordinate.araddr;
    to_subordinate.arlen    = ar_to_subordinate.arlen;
    to_subordinate.arsize   = ar_to_subordinate.arsize;
    to_subordinate.arburst  = ar_to_subordinate.arburst;
end

fifo_0r1w #(
    .DWIDTH($bits(ar_s)),
    .DEPTH(ARDEPTH)
) arfifo (
    //Clock and reset
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),

    //Write port (1-cycle latency)
    .i_push(from_manager.arvalid),
    .o_full(arfifo_full),
    .i_wdata(ar_from_manager),

    //Read port (0-cycle latency)
    .i_pop(to_subordinate.arready),
    .o_empty(arfifo_empty),
    .o_rdata(ar_to_subordinate)
);

/* ------------------------------------------------------------------------------------------------
 * R Buffer
 * --------------------------------------------------------------------------------------------- */

//"from_manager" and "to_subordinate" are misnomers for this since info flows the other way

logic rfifo_full, rfifo_empty;

typedef struct packed {
    id_t    rid;
    data_t  rdata;
    resp_e  rresp;
    logic   rlast;
} r_s;//lol

r_s r_from_subordinate, r_to_manager;

always_comb begin
    to_subordinate.rready       = !rfifo_full;
    r_from_subordinate.rid      = to_subordinate.rid;
    r_from_subordinate.rdata    = to_subordinate.rdata;
    r_from_subordinate.rresp    = to_subordinate.rresp;
    r_from_subordinate.rlast    = to_subordinate.rlast;

    from_manager.rvalid         = !rfifo_empty;
    from_manager.rid            = r_to_manager.rid;
    from_manager.rdata          = r_to_manager.rdata;
    from_manager.rresp          = r_to_manager.rresp;
    from_manager.rlast          = r_to_manager.rlast;
end

fifo_0r1w #(
    .DWIDTH($bits(r_s)),
    .DEPTH(RDEPTH)
) rfifo (
    //Clock and reset
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),

    //Write port (1-cycle latency)
    .i_push(to_subordinate.rvalid),
    .o_full(rfifo_full),
    .i_wdata(r_from_subordinate),

    //Read port (0-cycle latency)
    .i_pop(from_manager.rready),
    .o_empty(rfifo_empty),
    .o_rdata(r_to_manager)
);

endmodule : axi_buffer
