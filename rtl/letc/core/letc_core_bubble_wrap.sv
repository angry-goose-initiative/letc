/*
 * File:    letc_core_bubble_wrap.sv
 * Brief:   Bubbles, bubbles, bubbles everywhere!
 *
 * Copyright:
 *  Copyright (C) 2025 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * All jokes aside, this module is responsible for flushing and stalling stages as appropriate...
 * Thereby introducing bubbles into the pipeline :)
 *
 * https://www.youtube.com/watch?v=LIIbydhC5tE
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_bubble_wrap
    import letc_pkg::*;
    import letc_core_pkg::*;
    import riscv_pkg::*;
(
    input   logic [NUM_STAGES-1:0] stage_ready,
    output  logic [NUM_STAGES-1:0] stage_stall

    //TODO also need to have some inputs to detect data hazards, feeding from the forwarder/forwardee interfaces
    //TODO flushing should happen in a different module
);

/* ------------------------------------------------------------------------------------------------
 * Hazard Detection
 * --------------------------------------------------------------------------------------------- */

//Specifically hazards that can NOT be handled by forwarding

logic [NUM_STAGES-1:0] unforwardable_stage_hazard;

assign unforwardable_stage_hazard = '0;//TODO

/* ------------------------------------------------------------------------------------------------
 * Ready To Stall Loopback
 * --------------------------------------------------------------------------------------------- */

logic [NUM_STAGES-1:0] stage_stall_loopback;
assign stage_stall_loopback = ~stage_ready;

/* ------------------------------------------------------------------------------------------------
 * Output Logic
 * --------------------------------------------------------------------------------------------- */

//Determine which stages need to be stalled directly
logic [NUM_STAGES-1:0] direct_stage_stall;
assign direct_stage_stall = unforwardable_stage_hazard | stage_stall_loopback;

//Propagate stalls backwards to avoid losing data (backpressure)
logic [NUM_STAGES-1:0] backpressured_stage_stall;
always_comb begin
    //Base case: the last stage does not have any stages after it that could stall it
    backpressured_stage_stall[NUM_STAGES-1] = direct_stage_stall[NUM_STAGES-1];

    //All others could either be directly stalled or stalled as a result of backpressure
    for (int ii = (NUM_STAGES-1) - 1; ii >= 0; --ii) begin
        backpressured_stage_stall[ii] = backpressured_stage_stall[ii+1] | direct_stage_stall[ii];
    end
end

//Simple as that!
assign stage_stall = backpressured_stage_stall;

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

//TODO

endmodule : letc_core_bubble_wrap
