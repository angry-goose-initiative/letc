/*
 * File:    axi_pkg.sv
 * Brief:   AXI definitions and helper functions
 *
 * Copyright:
 *  Copyright (C) 2023-2024 John Jekel\n
 * See the LICENSE file at the root of the project for licensing info.
 *
 * Based on the old axi_pkg.svh
 *
 * Lock, cache, prot, qos, region, and user signals unsupported
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Interface Definition
 * --------------------------------------------------------------------------------------------- */

interface axi_if
    import axi_pkg::*;
(
    //Global signals
    input logic i_aclk,
    input logic i_arst_n
);

/* ------------------------------------------------------------------------------------------------
 * Connections
 * --------------------------------------------------------------------------------------------- */

//AW: Write Address Channel
logic   awvalid;
logic   awready;
id_t    awid;
addr_t  awaddr;
len_t   awlen;
size_t  awsize;
burst_e awburst;

//W: Write Data Channel
logic   wvalid;
logic   wready;
id_t    wid;//Removed in AXI4; you may need to deal with this in your RTL
data_t  wdata;
wstrb_t wstrb;
logic   wlast;

//B: Write Response Channel
logic   bvalid;
logic   bready;
id_t    bid;
resp_e  bresp;

//AR: Read Address Channel
logic   arvalid;
logic   arready;
id_t    arid;
addr_t  araddr;
len_t   arlen;
size_t  arsize;
burst_e arburst;

//R: Read Data Channel
logic   rvalid;
logic   rready;
id_t    rid;
data_t  rdata;
resp_e  rresp;
logic   rlast;

/* ------------------------------------------------------------------------------------------------
 * Modports
 * --------------------------------------------------------------------------------------------- */

modport manager (
    //AW: Write Address Channel
    output awvalid,
    input  awready,
    output awid,
    output awaddr,
    output awlen,
    output awsize,

    //W: Write Data Channel
    output wvalid,
    input  wready,
    output wid,
    output wdata,
    output wstrb,
    output wlast,

    //B: Write Response Channel
    input  bvalid,
    output bready,
    input  bid,
    input  bresp,

    //AR: Read Address Channel
    output arvalid,
    input  arready,
    output arid,
    output araddr,
    output arlen,
    output arsize,

    //R: Read Data Channel
    input  rvalid,
    output rready,
    input  rid,
    input  rdata,
    input  rresp,
    input  rlast
);

modport subordinate (
    //AW: Write Address Channel
    input  awvalid,
    output awready,
    input  awid,
    input  awaddr,
    input  awlen,
    input  awsize,

    //W: Write Data Channel
    input  wvalid,
    output wready,
    input  wid,
    input  wdata,
    input  wstrb,
    input  wlast,

    //B: Write Response Channel
    output bvalid,
    input  bready,
    output bid,
    output bresp,

    //AR: Read Address Channel
    input  arvalid,
    output arready,
    input  arid,
    input  araddr,
    input  arlen,
    input  arsize,

    //R: Read Data Channel
    output rvalid,
    input  rready,
    output rid,
    output rdata,
    output rresp,
    output rlast
);

/* ------------------------------------------------------------------------------------------------
 * Functions
 * --------------------------------------------------------------------------------------------- */

function logic aw_transfer_complete();//At next posedge
    return awvalid & awready;
endfunction

function logic w_transfer_complete();//At next posedge
    return wvalid & wready;
endfunction

function logic b_transfer_complete();//At next posedge
    return bvalid & bready;
endfunction

function logic ar_transfer_complete();//At next posedge
    return arvalid & arready;
endfunction

function logic r_transfer_complete();//At next posedge
    return rvalid & rready;
endfunction

function logic b_error_resp();
    return (bresp == AXI_RESP_SLVERR) | (bresp == AXI_RESP_DECERR);
endfunction

function logic r_error_resp();
    return (rresp == AXI_RESP_SLVERR) | (rresp == AXI_RESP_DECERR);
endfunction

function logic [LENWIDTH:0] aw_num_beats();
    return {1'b0, awlen} + (LENWIDTH + 1)'(1);
endfunction

function logic [LENWIDTH:0] ar_num_beats();
    return {1'b0, arlen} + (LENWIDTH + 1)'(1);
endfunction

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

//Good of a place as any for axi_pkg assertions
initial begin
    assert(AWIDTH > 0);
    assert(DWIDTH > 0);
    assert(IDWIDTH > 0);
    assert(LENWIDTH > 0);
    assert((DWIDTH % 8) == 0);
end

//Valid and ready signals shouldn't be unknown outside of reset
assert property (@(posedge i_aclk) disable iff (!i_arst_n) !$isunknown(awvalid));
assert property (@(posedge i_aclk) disable iff (!i_arst_n) !$isunknown(awready));
assert property (@(posedge i_aclk) disable iff (!i_arst_n) !$isunknown(wvalid));
assert property (@(posedge i_aclk) disable iff (!i_arst_n) !$isunknown(wready));
assert property (@(posedge i_aclk) disable iff (!i_arst_n) !$isunknown(bvalid));
assert property (@(posedge i_aclk) disable iff (!i_arst_n) !$isunknown(bready));
assert property (@(posedge i_aclk) disable iff (!i_arst_n) !$isunknown(arvalid));
assert property (@(posedge i_aclk) disable iff (!i_arst_n) !$isunknown(arready));
assert property (@(posedge i_aclk) disable iff (!i_arst_n) !$isunknown(rvalid));
assert property (@(posedge i_aclk) disable iff (!i_arst_n) !$isunknown(rready));

//When valid, signals shouldn't be unknown
assert property (@(posedge i_aclk) disable iff (!i_arst_n) (awvalid |-> !$isunknown(awid)));
assert property (@(posedge i_aclk) disable iff (!i_arst_n) (awvalid |-> !$isunknown(awaddr)));
assert property (@(posedge i_aclk) disable iff (!i_arst_n) (awvalid |-> !$isunknown(awlen)));
assert property (@(posedge i_aclk) disable iff (!i_arst_n) (awvalid |-> !$isunknown(awsize)));
assert property (@(posedge i_aclk) disable iff (!i_arst_n) (awvalid |-> !$isunknown(awburst)));
assert property (@(posedge i_aclk) disable iff (!i_arst_n) (wvalid |-> !$isunknown(wid)));
assert property (@(posedge i_aclk) disable iff (!i_arst_n) (wvalid |-> !$isunknown(wdata)));
assert property (@(posedge i_aclk) disable iff (!i_arst_n) (wvalid |-> !$isunknown(wstrb)));
assert property (@(posedge i_aclk) disable iff (!i_arst_n) (wvalid |-> !$isunknown(wlast)));
assert property (@(posedge i_aclk) disable iff (!i_arst_n) (bvalid |-> !$isunknown(bid)));
assert property (@(posedge i_aclk) disable iff (!i_arst_n) (bvalid |-> !$isunknown(bresp)));
assert property (@(posedge i_aclk) disable iff (!i_arst_n) (arvalid |-> !$isunknown(arid)));
assert property (@(posedge i_aclk) disable iff (!i_arst_n) (arvalid |-> !$isunknown(araddr)));
assert property (@(posedge i_aclk) disable iff (!i_arst_n) (arvalid |-> !$isunknown(arlen)));
assert property (@(posedge i_aclk) disable iff (!i_arst_n) (arvalid |-> !$isunknown(arsize)));
assert property (@(posedge i_aclk) disable iff (!i_arst_n) (arvalid |-> !$isunknown(arburst)));
assert property (@(posedge i_aclk) disable iff (!i_arst_n) (rvalid |-> !$isunknown(rid)));
assert property (@(posedge i_aclk) disable iff (!i_arst_n) (rvalid |-> !$isunknown(rdata)));
assert property (@(posedge i_aclk) disable iff (!i_arst_n) (rvalid |-> !$isunknown(rresp)));
assert property (@(posedge i_aclk) disable iff (!i_arst_n) (rvalid |-> !$isunknown(rlast)));

//AxBURST shouldn't be reserved
assert property (@(posedge i_aclk) disable iff (!i_arst_n) (awvalid |-> (awburst != AXI_BURST_RESERVED)));
assert property (@(posedge i_aclk) disable iff (!i_arst_n) (arvalid |-> (arburst != AXI_BURST_RESERVED)));

//TODO others

`endif

endinterface : axi_if
