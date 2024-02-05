/*
 * File:    axi_pkg.svh
 * Brief:   AXI definitions and helper functions / tasks
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * Currently targeting AXI3, but we'll try to leave flexibility for AXI4
 * in the future.
 *
 * TODO add support for lock, cache, prot, qos, region, and user signals
 *
*/

//OLD deprecated axi_pkg.svh

package axi_pkg;

/* ------------------------------------------------------------------------------------------------
 * Parameters
 * --------------------------------------------------------------------------------------------- */

//Adjust these as needed depending on the project
//TODO decide what this should be for LETC
parameter int AWIDTH = 32;
parameter int DWIDTH = 32;
parameter int ID_WIDTH = 8;

//Derived constants
parameter int WSTRB_WIDTH = DWIDTH / 8;

/* ------------------------------------------------------------------------------------------------
 * Other Typedefs
 * --------------------------------------------------------------------------------------------- */

typedef logic [AWIDTH - 1:0]    addr_t;
typedef logic [DWIDTH - 1:0]    data_t;
typedef logic [ID_WIDTH - 1:0]  id_t;
typedef logic [7:0]             len_t;//Only lower 3 bits are used for AXI3
typedef logic [2:0]             size_t;

typedef logic [WSTRB_WIDTH - 1:0] wstrb_t;

/* ------------------------------------------------------------------------------------------------
 * Enums
 * --------------------------------------------------------------------------------------------- */

typedef enum logic [1:0] {
    AXI_BURST_FIXED     = 2'b00,
    AXI_BURST_INCR      = 2'b01,
    AXI_BURST_WRAP      = 2'b10,
    AXI_BURST_RESERVED  = 2'b11
} burst_e;

typedef enum logic [1:0] {
    AXI_RESP_OKAY   = 2'b00,
    AXI_RESP_EXOKAY = 2'b01,
    AXI_RESP_SLVERR = 2'b10,
    AXI_RESP_DECERR = 2'b11
} resp_e;

/* ------------------------------------------------------------------------------------------------
 * Structs
 * --------------------------------------------------------------------------------------------- */

typedef struct packed {
    logic aclk;
    logic aresetn;
} global_s;

typedef struct packed {
    //Write address channel: manager -> subordinate
    id_t    awid;
    addr_t  awaddr;
    len_t   awlen;
    size_t  awsize;
    burst_e awburst;
    logic   awvalid;

    //Write data channel: manager -> subordinate
    id_t    wid;//Removed in AXI4
    data_t  wdata;
    wstrb_t wstrb;
    logic   wlast;
    logic   wvalid;

    //Write response channel: manager -> subordinate
    logic   bready;

    //Read address channel: manager -> subordinate
    id_t    arid;
    addr_t  araddr;
    len_t   arlen;
    size_t  arsize;
    burst_e arburst;
    logic   arvalid;

    //Read data channel: manager -> subordinate
    logic   rready;
} req_s;//Output of manager, input of subordinate

typedef struct packed {
    //Write address channel: subordinate -> manager
    logic   awready;

    //Write data channel: subordinate -> manager
    logic   wready;

    //Write response channel: subordinate -> manager
    id_t    bid;
    resp_e  bresp;
    logic   bvalid;

    //Read address channel: subordinate -> manager
    logic   arready;

    //Read data channel: subordinate -> manager
    id_t    rid;
    data_t  rdata;
    resp_e  rresp;
    logic   rlast;
    logic   rvalid;
} rsp_s;//Input of manager, output of subordinate

/* ------------------------------------------------------------------------------------------------
 * Helper functions
 * --------------------------------------------------------------------------------------------- */

function logic aw_transfer_complete(req_s req, rsp_s rsp);//At next positive edge
    return req.awvalid && rsp.awready;
endfunction

function logic w_transfer_complete(req_s req, rsp_s rsp);//At next positive edge
    return req.wvalid && rsp.wready;
endfunction

function logic b_transfer_complete(req_s req, rsp_s rsp);//At next positive edge
    return rsp.bvalid && req.bready;
endfunction

function logic ar_transfer_complete(req_s req, rsp_s rsp);//At next positive edge
    return req.arvalid && rsp.arready;
endfunction

function logic r_transfer_complete(req_s req, rsp_s rsp);//At next positive edge
    return rsp.rvalid && req.rready;
endfunction

endpackage
