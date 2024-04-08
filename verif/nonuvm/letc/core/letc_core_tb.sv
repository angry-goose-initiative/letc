/**
 * File    letc_core_tb.sv
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

module letc_core_tb;

import letc_pkg::*;
import letc_core_pkg::*;

/* ------------------------------------------------------------------------------------------------
 * Parameters
 * --------------------------------------------------------------------------------------------- */

localparam CLOCK_PERIOD = 10;

/* ------------------------------------------------------------------------------------------------
 * DUT Connections
 * --------------------------------------------------------------------------------------------- */

//Clock and reset
logic i_clk;
logic i_rst_n;

//IO
axi_if  axi(.i_aclk(i_clk), .i_arst_n(i_rst_n));
logic   i_timer_irq_pending;
logic   i_external_irq_pending;

//Debug
logic [7:0] o_debug;

/* ------------------------------------------------------------------------------------------------
 * DUT
 * --------------------------------------------------------------------------------------------- */

letc_core_top dut (.*);

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

    //IO
    //TODO axi
    output  i_timer_irq_pending;
    output  i_external_irq_pending;

    //Debug
    input   o_debug;

    /* verilator lint_on UNUSEDSIGNAL */
endclocking

/* ------------------------------------------------------------------------------------------------
 * Tasks
 * --------------------------------------------------------------------------------------------- */

//Note: due to quirks with Verilator, sadly we should try to avoid waiting for the next posedge in tasks

task setup();
begin
    //Set initial input states
    //FIXME use cb
    axi.arready = 1'b0;
    axi.rvalid  = 1'b0;
    axi.awready = 1'b0;
    axi.wready  = 1'b0;
    axi.bvalid  = 1'b0;
    i_timer_irq_pending = 1'b0;
    i_external_irq_pending = 1'b0;
end
endtask

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

initial begin
    setup();

    //Reset things
    i_rst_n = 1'b0;
    ##2;
    i_rst_n = 1'b1;
    ##2;

    //cb.//TODO

    ##50;
    $finish;
end

endmodule : letc_core_tb
