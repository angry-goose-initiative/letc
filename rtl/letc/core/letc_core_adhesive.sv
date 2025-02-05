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
    input   logic [NUM_STAGES-1:0] stage_ready,
    output  logic [NUM_STAGES-1:0] stage_flush,
    output  logic [NUM_STAGES-1:0] stage_stall
);

//TODO

/* ------------------------------------------------------------------------------------------------
 * Forwarding Logic
 * --------------------------------------------------------------------------------------------- */

//TODO

/* ------------------------------------------------------------------------------------------------
 * Pipeline Bubble Insertion
 * --------------------------------------------------------------------------------------------- */

letc_core_bubble_wrap pop_pop_pop (.*);

endmodule : letc_core_adhesive
