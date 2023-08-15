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
    input   logic   s2_busy//Means s2 is NOT ready to accept a new instruction from s1 this cycle

    //TODO other ports

);

/* ------------------------------------------------------------------------------------------------
 * Internal connections and state
 * --------------------------------------------------------------------------------------------- */

typedef enum logic [2:0] {
    INIT,
    HALT,
    FETCHING,
    STALLED_WAITING_ON_S2_NOEXCEPT,
    STALLED_WAITING_ON_S2_FETCHEXCEPT
    //TODO any other additional states that may be needed in the future
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
    if (halt_req) begin
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
                    next_state = STALLED_WAITING_ON_S2_NOEXCEPT;
                end else begin//TODO else if exception then [...]_FETCHEXCEPT
                    next_state = FETCHING;//No need to wait around, fetch the next instruction right away!
                end
            end
            STALLED_WAITING_ON_S2_NOEXCEPT: begin
                next_state = HALT;//TODO
            end
            STALLED_WAITING_ON_S2_FETCHEXCEPT: begin
                next_state = HALT;//TODO
            end
            default: next_state = HALT;//We entered an illegal state, so halt
        endcase
    end
end : next_state_logic

/* ------------------------------------------------------------------------------------------------
 * Control signal output logic
 * --------------------------------------------------------------------------------------------- */

//TODO

endmodule : core_s1_control
