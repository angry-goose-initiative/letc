/*
 * File:    core_s2_control.sv
 * Brief:   State machine and control logic for LETC Core Stage 2
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

module core_s2_control
    import core_pkg::*;
(
    input clk,
    input rst_n,

    //TODO other ports (for Mealy and next-state logic inputs)

    //Control signals out
    output logic rd_write_enable
    //TODO others
);

/* ------------------------------------------------------------------------------------------------
 * State machine
 * --------------------------------------------------------------------------------------------- */
typedef enum logic [2:0] {
    INIT,
    HALT,
    FETCH_NEXT,
    WAIT_ON_L1DCACHE,
    //TODO any other additional states needed by various instructions
    FINISH_CURRENT_AND_FETCH_NEXT 
} state_e;

state_e state, next_state;

always_ff @(posedge clk, negedge rst_n) begin : state_ff
    if (!rst_n) begin
        state <= INIT;
    end else begin
        state <= next_state;
    end
end : state_ff

always_comb begin : next_state_logic
    unique case (state)
        INIT: begin
            //In the future we may do more things in INIT
            next_state = FETCH_NEXT;
        end
        HALT: next_state = HALT;
        FETCH_NEXT: begin
            next_state = HALT;//TODO
        end
        WAIT_ON_L1DCACHE: begin
            next_state = HALT;//TODO
        end
        //TODO any other additional states needed by various instructions
        FINISH_CURRENT_AND_FETCH_NEXT: begin
            next_state = HALT;//TODO
        end
        default: next_state = HALT;//We entered an illegal state, so halt
    endcase
end : next_state_logic

/* ------------------------------------------------------------------------------------------------
 * Control logic (Mealy)
 * --------------------------------------------------------------------------------------------- */
always_comb begin : control_signal_logic
    rd_write_enable = 0;
    unique case (state)
        INIT: begin
            //In the future we may do more things in INIT
            //TODO other control signals
        end
        HALT: begin
            //TODO other control signals
        end
        FETCH_NEXT: begin
            //TODO other control signals
        end
        WAIT_ON_L1DCACHE: begin
            //TODO other control signals
        end
        //TODO any other additional states needed by various instructions
        FINISH_CURRENT_AND_FETCH_NEXT: begin
            //rd_write_enable = ?;//TODO this will depend on the instruction
        end
        default: begin end//Illegal state, so do nothing
    endcase
end : control_signal_logic

endmodule : core_s2_control
