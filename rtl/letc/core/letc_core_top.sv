/*
 * File:    letc_core_top.sv
 * Brief:   TODO
 *
 * Copyright:
 *  Copyright (C) 2023-2024 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_top
    import letc_pkg::*;
    import letc_core_pkg::*;
(
    //Clock and reset
    input logic i_clk,
    input logic i_rst_n,

    //IO
    axi_if.manager          axi,
    input logic             i_timer_irq_pending,
    input logic             i_external_irq_pending
);

//TODO

endmodule : letc_core_top
