/*
 * File:    core_s1_control.sv
 * Brief:   TODO
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

`ifdef IMPORTS_IN_MODULE_SCOPE_UNSUPPORTED
import letc_pkg::*;
import core_pkg::*;
`endif

module core_s1_control
`ifndef IMPORTS_IN_MODULE_SCOPE_UNSUPPORTED
    import letc_pkg::*;
    import core_pkg::*;
`endif
(
    input   logic   clk,
    input   logic   rst_n,

    input   logic   halt_req,//LETC.EXIT instruction encountered in M-mode
    input   logic   s2_busy,//Means s2 is NOT ready to accept a new instruction from s1 this cycle
    input   logic   fetch_exception,

    output  logic   s1_stall,//Prevents pc_ff from updating
    output  logic   bypass_pc_for_fetch_addr//fetch_addr becomes next_pc instead of pc_ff
    //TODO other ports

);

/* ------------------------------------------------------------------------------------------------
 * Internal connections and state
 * --------------------------------------------------------------------------------------------- */

typedef enum logic [2:0] {
    INIT,
    HALT,
    FETCHING,
    STALLED_ON_S2_NOEXCEPT,
    STALLED_ON_S2_FETCHEXCEPT
} state_e;
state_e state_ff, next_state;

/* ------------------------------------------------------------------------------------------------
 * State machine logic
 * --------------------------------------------------------------------------------------------- */

always_ff @(posedge clk, negedge rst_n) begin : state_seq_logic
    if (!rst_n) begin
        state_ff <= INIT;
    end else begin
        state_ff <= next_state;
    end
end : state_seq_logic

always_comb begin : next_state_logic
    if (halt_req) begin//Previous instruction was LETC.EXIT
        next_state = HALT;
    end else begin
        unique case (state_ff)
            INIT: begin
                //In the future we may do more things in INIT
                next_state = FETCHING;
            end
            HALT: next_state = HALT;//There is no escape except for reset
            FETCHING: begin
                if (s2_busy) begin
                    next_state = fetch_exception ? STALLED_ON_S2_FETCHEXCEPT : STALLED_ON_S2_NOEXCEPT;
                end else begin
                    next_state = FETCHING;//No need to wait around, fetch the next instruction right away!
                end
            end
            STALLED_ON_S2_NOEXCEPT, STALLED_ON_S2_FETCHEXCEPT: begin
                next_state = s2_busy ? state_ff : FETCHING;//If s2 is no longer busy, then we can fetch the next instruction
            end
            default: next_state = HALT;//We entered an illegal state, so halt
        endcase
    end
end : next_state_logic

/* ------------------------------------------------------------------------------------------------
 * Control signal output logic
 * --------------------------------------------------------------------------------------------- */

assign s1_stall = state_ff != FETCHING;//TODO is this correct?
assign bypass_pc_for_fetch_addr = state_ff == FETCHING;//Not init since we need to fetch the first instruction
//TODO

endmodule : core_s1_control
