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

//TESTING just wire core directly to ps_gp (useful to get some initial synthesis numbers)
//TODO we need to choose between this, default_sub, and the aclint (and potentially others in the future)
always_comb begin
    ps_gp.awvalid   = core.awvalid;
    ps_gp.awaddr    = core.awaddr;
    ps_gp.awlen     = core.awlen;
    ps_gp.awsize    = core.awsize;
    ps_gp.awburst   = core.awburst;
    ps_gp.awid      = core.awid;
    core.awready    = ps_gp.awready;

    ps_gp.wvalid    = core.wvalid;
    ps_gp.wdata     = core.wdata;
    ps_gp.wstrb     = core.wstrb;
    ps_gp.wlast     = core.wlast;
    ps_gp.wid       = core.wid;
    core.wready     = ps_gp.wready;

    core.bvalid     = ps_gp.bvalid;
    core.bresp      = ps_gp.bresp;
    core.bid        = ps_gp.bid;
    ps_gp.bready    = core.bready;

    ps_gp.arvalid   = core.arvalid;
    ps_gp.araddr    = core.araddr;
    ps_gp.arlen     = core.arlen;
    ps_gp.arsize    = core.arsize;
    ps_gp.arburst   = core.arburst;
    ps_gp.arid      = core.arid;
    core.arready    = ps_gp.arready;

    core.rvalid     = ps_gp.rvalid;
    core.rdata      = ps_gp.rdata;
    core.rresp      = ps_gp.rresp;
    core.rid        = ps_gp.rid;
    core.rlast      = ps_gp.rlast;
    ps_gp.rready    = core.rready;
end

/* ------------------------------------------------------------------------------------------------
 * Tying off ACP port (for now)
 * --------------------------------------------------------------------------------------------- */

//TODO for now we'll just be using the ps_gp port to simplify LETC
//per a meeting we had a few weeks ago. Maybe we'll use the ACP port later.
always_comb begin
    ps_acp.awvalid = 1'b0;
    ps_acp.wvalid  = 1'b0;
    ps_acp.bready  = 1'b0;
    ps_acp.arvalid = 1'b0;
    ps_acp.rready  = 1'b0;
end

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

//TODO

`endif //SIMULATION

endmodule : letc_matrix_switch
