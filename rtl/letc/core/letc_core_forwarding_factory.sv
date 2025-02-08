/*
 * File:    letc_core_forwarding_factory.sv
 * Brief:   Forwarding register values to previous stages as their computation completes
 *
 * Copyright:
 *  Copyright (C) 2025 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_forwarding_factory
    import letc_pkg::*;
    import letc_core_pkg::*;
    import riscv_pkg::*;
(
    input   logic clk,
    input   logic rst_n,

    letc_core_forwardee_if.adhesive  e_forwardee_rs1,
    letc_core_forwardee_if.adhesive  e_forwardee_rs2,
    letc_core_forwardee_if.adhesive m1_forwardee_rs2,
    letc_core_forwardee_if.adhesive m2_forwardee_rs2,

    letc_core_forwarder_if.adhesive m1_forwarder,
    letc_core_forwarder_if.adhesive m2_forwarder,
    letc_core_forwarder_if.adhesive  w_forwarder
);

//TODO

//TEMP just adding these so execute doesn't complain as it is already using the forwardee interfaces
assign e_forwardee_rs1.use_fwd = 1'b0;
assign e_forwardee_rs2.use_fwd = 1'b0;

endmodule : letc_core_forwarding_factory
