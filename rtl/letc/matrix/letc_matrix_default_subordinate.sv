/*
 * File:    letc_matrix_default_subordinate.sv
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

module letc_matrix_default_subordinate
    import letc_pkg::*;
(
    //Clock and reset
    input logic i_clk,
    input logic i_rst_n,

    axi_if.subordinate axi
);

//TODO (not a high priority since software shouldn't do this anyways)
always_comb begin
    axi.awready = 1'b1;
    axi.wready  = 1'b1;
    axi.bvalid  = 1'b1;
    axi.arready = 1'b1;
    axi.rvalid  = 1'b1;
end

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

//TODO

`endif //SIMULATION

endmodule : letc_matrix_default_subordinate
