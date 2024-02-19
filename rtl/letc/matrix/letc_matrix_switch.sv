/*
 * File:    letc_matrix_switch.sv
 * Brief:   TODO
 *
 * Copyright (C) 2024 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_matrix_switch
    import letc_pkg::*;
(
    //Clock and reset
    input logic i_clk,
    input logic i_rst_n,

    //AXI ports
    axi_if.subordinate  core,
    axi_if.manager      default_sub,
    axi_if.manager      ps_gp,
    axi_if.manager      ps_acp,
    axi_if.manager      aclint
);

//TODO

//TESTING just wire core directly to default_sub
always_comb begin
    default_sub.awvalid = core.awvalid;
    default_sub.awaddr  = core.awaddr;
    default_sub.awlen   = core.awlen;
    default_sub.awsize  = core.awsize;
    default_sub.awburst = core.awburst;
    default_sub.awid    = core.awid;
    core.awready        = default_sub.awready;

    default_sub.wvalid  = core.wvalid;
    default_sub.wdata   = core.wdata;
    default_sub.wstrb   = core.wstrb;
    default_sub.wlast   = core.wlast;
    default_sub.wid     = core.wid;
    core.wready         = default_sub.wready;
    
    core.bvalid         = default_sub.bvalid;
    core.bresp          = default_sub.bresp;
    core.bid            = default_sub.bid;
    default_sub.bready  = core.bready;

    default_sub.arvalid = core.arvalid;
    default_sub.araddr  = core.araddr;
    default_sub.arlen   = core.arlen;
    default_sub.arsize  = core.arsize;
    default_sub.arburst = core.arburst;
    default_sub.arid    = core.arid;
    core.arready        = default_sub.arready;

    core.rvalid         = default_sub.rvalid;
    core.rdata          = default_sub.rdata;
    core.rresp          = default_sub.rresp;
    core.rid            = default_sub.rid;
    core.rlast          = default_sub.rlast;
    default_sub.rready  = core.rready;
end

endmodule : letc_matrix_switch
