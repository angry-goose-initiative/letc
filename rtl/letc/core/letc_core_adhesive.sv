/*
 * File:    letc_core_adhesive.sv
 * Brief:   Glue logic for LETC, handling hazards, exceptions, branches, etc
 *
 * Copyright:
 *  Copyright (C) 2025 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * Get the joke?
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_adhesive
    import letc_pkg::*;
    import letc_core_pkg::*;
    import riscv_pkg::*;
(
    input   logic clk,
    input   logic rst_n,

    input   logic [NUM_STAGES-1:0] stage_ready,
    output  logic [NUM_STAGES-1:0] stage_flush,
    output  logic [NUM_STAGES-1:0] stage_stall,

    input   logic   branch_taken,
    input   pc_t    branch_target,

    output  logic   pc_load_en,
    output  pc_t    pc_load_val,

    letc_core_forwardee_if.adhesive  e_forwardee_rs1,
    letc_core_forwardee_if.adhesive  e_forwardee_rs2,
    letc_core_forwardee_if.adhesive m1_forwardee_rs2,
    letc_core_forwardee_if.adhesive m2_forwardee_rs2,

    letc_core_forwarder_if.adhesive m1_forwarder,
    letc_core_forwarder_if.adhesive m2_forwarder,
    letc_core_forwarder_if.adhesive  w_forwarder
);

//TODO

/* ------------------------------------------------------------------------------------------------
 * Forwarding Logic
 * --------------------------------------------------------------------------------------------- */

//TODO

//TEMP just adding these so execute doesn't complain as it is already using the forwardee interfaces
assign e_forwardee_rs1.use_fwd = 1'b0;
assign e_forwardee_rs2.use_fwd = 1'b0;

/* ------------------------------------------------------------------------------------------------
 * Pipeline Bubble Insertion
 * --------------------------------------------------------------------------------------------- */

letc_core_bubble_wrap pop_pop_pop (.*);

/* ------------------------------------------------------------------------------------------------
 * Flush Logic
 * --------------------------------------------------------------------------------------------- */

//TODO put this into it's own module
//FIXME coordinate with bubble_wrap so we never stall and flush at the same time
always_comb begin
    //FIXME causes an f2 assertion to fire...
    /*
    if (branch_taken) begin
        stage_flush = 7'b0001111;//Flush F1, F2, D and E since the branch decision is available in M1
    end else begin
    */
        stage_flush = '0;
    //end
end

/* ------------------------------------------------------------------------------------------------
 * Branch Prediction / Exceptions / PC Handling
 * --------------------------------------------------------------------------------------------- */

//TODO improve this

//FIXME causes a decode assertion to fire
assign pc_load_en   = 1'b0;
//assign pc_load_en   = branch_taken;
assign pc_load_val  = branch_target;

endmodule : letc_core_adhesive
