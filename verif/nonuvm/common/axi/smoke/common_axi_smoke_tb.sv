/**
 * File    common_axi_smoke_tb.sv
 * Brief   Smoketest for axi_pkg and interfaces
 * 
 * Copyright:
 *  Copyright (C) 2024 John Jekel\n
 * See the LICENSE file at the root of the project for licensing info.
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module common_axi_smoke_tb;

localparam CLOCK_PERIOD = 10;

import axi_pkg::*;

/* ------------------------------------------------------------------------------------------------
 * Connections
 * --------------------------------------------------------------------------------------------- */

logic i_aclk;
logic i_arst_n;

/* ------------------------------------------------------------------------------------------------
 * Other Stuff
 * --------------------------------------------------------------------------------------------- */

axi_if axi_if_inst (
    //Global signals
    .i_aclk(i_aclk),
    .i_arst_n(i_arst_n)
);

initial begin
    $finish;
end

endmodule : common_axi_smoke_tb
