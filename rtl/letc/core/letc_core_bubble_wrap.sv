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
    //Just used for assertions at the moment
    input   logic clk,
    input   logic rst_n,

    input   logic [NUM_STAGES-1:0] stage_ready,
    output  logic [NUM_STAGES-1:0] stage_flush,
    output  logic [NUM_STAGES-1:0] stage_stall,

    input   logic branch_taken
    //TODO also add exception in writeback signal, which should take precedence over branch_taken

    //TODO also need to have some inputs to detect data hazards, feeding from the forwarder/forwardee interfaces
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
 * Stall Consolidation And Backpressuring
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

/* ------------------------------------------------------------------------------------------------
 * Flushing
 * --------------------------------------------------------------------------------------------- */

logic [NUM_STAGES-1:0] direct_stage_flush;

always_comb begin
    //TODO prioritize writeback exeception flush over branch taken flush
    //FIXME causes an f2 assertion to fire...
    /**/
    if (branch_taken) begin
        direct_stage_flush = 7'b0001111;//Flush F1, F2, D and E since the branch decision is available in M1
    end else begin
    /**/
        direct_stage_flush = '0;
    end
end

/* ------------------------------------------------------------------------------------------------
 * Output Logic
 * --------------------------------------------------------------------------------------------- */

//Avoid stalling and flushing at the same time

//TODO is it correct for flushing to take priority?
assign stage_flush = direct_stage_flush;
assign stage_stall = backpressured_stage_stall & ~direct_stage_flush;

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

//Control signals should always be known out of reset
assert property (@(posedge clk) disable iff (!rst_n) !$isunknown(stage_ready));
assert property (@(posedge clk) disable iff (!rst_n) !$isunknown(stage_flush));
assert property (@(posedge clk) disable iff (!rst_n) !$isunknown(stage_stall));
assert property (@(posedge clk) disable iff (!rst_n) !$isunknown(unforwardable_stage_hazard));
assert property (@(posedge clk) disable iff (!rst_n) !$isunknown(stage_stall_loopback));
assert property (@(posedge clk) disable iff (!rst_n) !$isunknown(direct_stage_stall));

//Per-bit checks
generate
    for (genvar ii = 0; ii < NUM_STAGES; ++ii) begin : gen_asserts
        //FIXME not correct, as flush may take precedence over stall
        //assert property (@(posedge clk) disable iff (!rst_n) !stage_ready[ii] |-> stage_stall[ii]);//Loopback
        if (ii != NUM_STAGES-1) begin : gen_bp_asserts
            assert property (@(posedge clk) disable iff (!rst_n) stage_stall[ii+1] |-> stage_stall[ii]);//Backpressure
        end : gen_bp_asserts

        assert property (@(posedge clk) disable iff (!rst_n) !(stage_flush[ii] & stage_stall[ii]));//No flushing and stalling at the same time
    end : gen_asserts
endgenerate

`endif //SIMULATION

endmodule : letc_core_bubble_wrap
