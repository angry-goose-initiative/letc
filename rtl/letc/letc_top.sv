/*
 * File:    letc_top.sv
 * Brief:   The top-level RTL file for LETC
 *
 * Copyright:
 *  Copyright (C) 2023-2024 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * Connects within a coraz7_top.sv, so it may not be the "real" top-level that goes onto an
 * FPGA. But for most RTL purposes (ex. simulation) it basically is.
 *
 * All connections are assumed to be synchronous to i_clk
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_top
    import letc_pkg::*;
(
    //All connections are assumed to be synchronous to i_clk

    //Clock and reset
    input logic i_clk,
    input logic i_rst_n,

    //LEDs and Buttons
    input  logic [1:0]  i_btn,
    output logic        o_led0_r,
    output logic        o_led0_g,
    output logic        o_led0_b,
    output logic        o_led1_r,
    output logic        o_led1_g,
    output logic        o_led1_b,

    //PS Connections
    input logic         i_uart1_interrupt,
    axi_if.subordinate  axi_m_gp_0,//LETC is the subordinate, PS is the manager
    axi_if.manager      axi_s_gp_0,//PS is the subordinate, LETC is the manager
    axi_if.manager      axi_s_acp,//PS is the subordinate, LETC is the manager; YOU MUST PARAMETERIZE DWIDTH TO 64

    //Debug (Logic Analyzer)
    output logic [7:0]      o_debug
);

/* ------------------------------------------------------------------------------------------------
 * Connections
 * --------------------------------------------------------------------------------------------- */

axi_if  axi_core(.i_aclk(i_clk), .i_arst_n(i_rst_n));
logic   timer_irq_pending;//TEMPORARY

axi_if  axi_aclint(.i_aclk(i_clk), .i_arst_n(i_rst_n));
//TODO more

/* ------------------------------------------------------------------------------------------------
 * Module Instantiations
 * --------------------------------------------------------------------------------------------- */

letc_core_top core (
    .*,

    //IO
    .axi(axi_core),
    .i_timer_irq_pending(timer_irq_pending),
    .i_external_irq_pending(i_uart1_interrupt)
);

//TEMPORARY
assign timer_irq_pending = 1'b0;

letc_matrix_top matrix (
    .*,

    //AXI ports
    .core(axi_core),
    .ps_gp(axi_s_gp_0),
    .ps_acp(axi_s_acp),
    .aclint(axi_aclint)
);

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

//TODO

`endif //SIMULATION

endmodule : letc_top
