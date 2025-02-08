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

    letc_core_forwardee_if.fwd_factory  e_forwardee_rs1,
    letc_core_forwardee_if.fwd_factory  e_forwardee_rs2,
    letc_core_forwardee_if.fwd_factory m1_forwardee_rs2,
    letc_core_forwardee_if.fwd_factory m2_forwardee_rs2,

    letc_core_forwarder_if.fwd_factory m1_forwarder,
    letc_core_forwarder_if.fwd_factory m2_forwarder,
    letc_core_forwarder_if.fwd_factory  w_forwarder
);

logic [NUM_STAGES-1:0] unforwardable_stage_hazard;
assign unforwardable_stage_hazard = '0;//FIXME actually implement this

logic e_unforwardable_hazard;
logic m1_unforwardable_hazard;
logic m2_unforwardable_hazard;

/* ------------------------------------------------------------------------------------------------
 * Forwarding Logic
 * --------------------------------------------------------------------------------------------- */

letc_core_forwarding_factory forwarder (.*);

/* ------------------------------------------------------------------------------------------------
 * Pipeline Bubble Insertion and Flushing
 * --------------------------------------------------------------------------------------------- */

letc_core_bubble_wrap pop_pop_pop (.*);

/* ------------------------------------------------------------------------------------------------
 * Branch Prediction / Exceptions / PC Handling
 * --------------------------------------------------------------------------------------------- */

//TODO improve this

//FIXME causes a decode assertion to fire
//assign pc_load_en   = 1'b0;
assign pc_load_en   = branch_taken;
assign pc_load_val  = branch_target;

endmodule : letc_core_adhesive
