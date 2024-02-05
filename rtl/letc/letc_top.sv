/*
 * File:    letc_top.sv
 * Brief:   The top-level RTL file for LETC
 *
 * Copyright:
 *  Copyright (C) 2023-2024 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * Connects within a Vivado block design, so it may not be the "real" top-level that goes onto an
 * FPGA. But for most purposes it basically is.
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_top
    import letc_pkg::*;
(
    //Clock and reset
    input logic i_clk,
    input logic i_rst_n

    //TODO other ports to the Vivado block design
);

/* ------------------------------------------------------------------------------------------------
 * Connections
 * --------------------------------------------------------------------------------------------- */

axi_if  core_axi(.i_aclk(i_clk), .i_arst_n(i_rst_n));
logic   timer_irq_pending;
logic   external_irq_pending;

//TODO more

/* ------------------------------------------------------------------------------------------------
 * Module Instantiations
 * --------------------------------------------------------------------------------------------- */

letc_core_top core (
    .*,

    .axi(core_axi),
    .i_timer_irq_pending(timer_irq_pending),
    .i_external_irq_pending(external_irq_pending)
);

//TEMPORARY
assign timer_irq_pending = 1'b0;
assign external_irq_pending = 1'b0;

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

    //TODO

`endif

endmodule : letc_top
