/**
 * File    axi_buffer_tb.sv
 * Brief   TODO
 *
 * Copyright:
 *  Copyright (C) 2025 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module axi_buffer_tb;

import axi_pkg::*;

/* ------------------------------------------------------------------------------------------------
 * Parameters
 * --------------------------------------------------------------------------------------------- */

localparam CLOCK_PERIOD = 10;

localparam AWDEPTH  = 2;
localparam WDEPTH   = 2;
localparam BDEPTH   = 2;
localparam ARDEPTH  = 2;
localparam RDEPTH   = 2;

/* ------------------------------------------------------------------------------------------------
 * DUT Connections
 * --------------------------------------------------------------------------------------------- */

//Clock and reset
logic i_clk;
logic i_rst_n;

//AXI ports
axi_if from_manager (
    .i_aclk(i_clk),
    .i_arst_n(i_rst_n)
);
axi_if to_subordinate (
    .i_aclk(i_clk),
    .i_arst_n(i_rst_n)
);

/* ------------------------------------------------------------------------------------------------
 * DUT
 * --------------------------------------------------------------------------------------------- */

axi_buffer #(
    .AWDEPTH(AWDEPTH),
    .WDEPTH(WDEPTH),
    .BDEPTH(BDEPTH),
    .ARDEPTH(ARDEPTH),
    .RDEPTH(RDEPTH)
) dut (
    .*
);

/* ------------------------------------------------------------------------------------------------
 * Clocking
 * --------------------------------------------------------------------------------------------- */

clock_generator #(
    .PERIOD(CLOCK_PERIOD)
) clock_gen_inst (
    .clk(i_clk)
);

/* ------------------------------------------------------------------------------------------------
 * Tasks
 * --------------------------------------------------------------------------------------------- */

//verilator lint_save
//verilator lint_off INITIALDLY

task reset();
begin
    //Enter reset
    i_rst_n <= 1'b0;

    //AW: Write Address Channel
    from_manager.awvalid        <= 1'b0;
    to_subordinate.awready      <= 1'b0;
    from_manager.awid           <= '0;
    from_manager.awaddr         <= '0;
    from_manager.awlen          <= '0;
    from_manager.awsize         <= '0;
    from_manager.awburst        <= AXI_BURST_FIXED;

    //W: Write Data Channel
    from_manager.wvalid         <= 1'b0;
    to_subordinate.wready       <= 1'b0;
    from_manager.wdata          <= '0;
    from_manager.wstrb          <= '0;
    from_manager.wlast          <= 1'b0;

    //B: Write Response Channel
    to_subordinate.bvalid       <= 1'b0;
    from_manager.bready         <= 1'b0;
    to_subordinate.bid          <= '0;
    to_subordinate.bresp        <= AXI_RESP_OKAY;

    //AR: Read Address Channel
    from_manager.arvalid        <= 1'b0;
    to_subordinate.arready      <= 1'b0;
    from_manager.arid           <= '0;
    from_manager.araddr         <= '0;
    from_manager.arlen          <= '0;
    from_manager.arsize         <= '0;
    from_manager.arburst        <= AXI_BURST_FIXED;

    //R: Read Data Channel
    to_subordinate.rvalid       <= 1'b0;
    from_manager.rready         <= 1'b0;
    to_subordinate.rid          <= '0;
    to_subordinate.rdata        <= '0;
    to_subordinate.rresp        <= AXI_RESP_OKAY;
    to_subordinate.rlast        <= 1'b0;
    
    //Now come out of reset (after holding it for a couple of cycles)
    @(negedge i_clk);
    @(negedge i_clk);
    i_rst_n <= 1'b1;
    @(negedge i_clk);
    @(negedge i_clk);
end
endtask

//verilator lint_restore

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

initial begin
    //verilator lint_save
    //verilator lint_off INITIALDLY
    reset();

    //TODO add interesting traffic (maybe create an AXI traffic generator?)

    repeat(5) @(negedge i_clk);
    $finish;

    //verilator lint_restore
end

endmodule : axi_buffer_tb
