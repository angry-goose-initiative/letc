/*
 * File:    letc_matrix_top.sv
 * Brief:   TODO
 *  _     _____ _____ ____   __  __       _        _
 * | |   | ____|_   _/ ___| |  \/  | __ _| |_ _ __(_)_  __
 * | |   |  _|   | || |     | |\/| |/ _` | __| '__| \ \/ /
 * | |___| |___  | || |___  | |  | | (_| | |_| |  | |>  <
 * |_____|_____| |_| \____| |_|  |_|\__,_|\__|_|  |_/_/\_\
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

module letc_matrix_top
    import letc_pkg::*;
(
    //Clock and reset
    input logic i_clk,
    input logic i_rst_n,

    //AXI ports
    axi_if.subordinate  core,//Pre-buffered
    axi_if.manager      ps_gp,//Buffered//FIXME this too
    //FIXME width needs to be converted to 64-bit, not in the switch but in another submodule under top; override the data and id widths
    axi_if.manager      ps_acp,//Buffered
    axi_if.manager      aclint//Buffered
    //TODO more as nesessary
);

/* ------------------------------------------------------------------------------------------------
 * Default Subordinate
 * --------------------------------------------------------------------------------------------- */

//The default subordinate responds with decerrs when an invalid address is accessed

axi_if default_subordinate(.i_aclk(i_clk), .i_arst_n(i_rst_n));//Buffered

letc_matrix_default_subordinate default_subordinate_inst (
    .*,
    .axi(default_subordinate.subordinate)
);

/* ------------------------------------------------------------------------------------------------
 * AXI Buffers
 * --------------------------------------------------------------------------------------------- */

//Buffering adds latency (two cycles in total) but eases timing

axi_if                  core_buffered(.i_aclk(i_clk), .i_arst_n(i_rst_n));
axi_if                  default_subordinate_pre_buffered(.i_aclk(i_clk), .i_arst_n(i_rst_n));
axi_if                  ps_gp_pre_buffered(.i_aclk(i_clk), .i_arst_n(i_rst_n));
axi_if #(.DWIDTH(64))   ps_acp_pre_buffered(.i_aclk(i_clk), .i_arst_n(i_rst_n));
axi_if                  aclint_pre_buffered(.i_aclk(i_clk), .i_arst_n(i_rst_n));

axi_buffer core_buffer (
    .*,
    .from_manager(core),
    .to_subordinate(core_buffered.manager)
);

axi_buffer default_subordinate_buffer (
    .*,
    .from_manager(default_subordinate_pre_buffered.subordinate),
    .to_subordinate(default_subordinate.manager)
);

axi_buffer ps_gp_buffer (
    .*,
    .from_manager(ps_gp_pre_buffered.subordinate),
    .to_subordinate(ps_gp)
);

axi_buffer ps_acp_buffer (//FIXME need to parameterize this to be 64-bit
    .*,
    .from_manager(ps_acp_pre_buffered.subordinate),
    .to_subordinate(ps_acp)
);

axi_buffer aclint_buffer (
    .*,
    .from_manager(aclint_pre_buffered.subordinate),
    .to_subordinate(aclint)
);

//TODO more as nesessary

/* ------------------------------------------------------------------------------------------------
 * Switching Logic
 * --------------------------------------------------------------------------------------------- */

letc_matrix_switch switch (
    .*,
    .core(core_buffered.subordinate),
    .default_sub(default_subordinate_pre_buffered.manager),
    .ps_gp(ps_gp_pre_buffered.manager),
    .ps_acp(ps_acp_pre_buffered.manager),
    .aclint(aclint_pre_buffered.manager)
    //TODO more as nesessary
);

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

//TODO

`endif //SIMULATION

endmodule : letc_matrix_top
