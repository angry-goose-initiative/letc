/*
 * File:    core_control.sv
 * Brief:   State machine and control logic for LETC Core
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

module core_control
    import letc_pkg::*;
(
    input clk,
    input rst_n

    //TODO other ports

);

typedef enum {
    FETCH,
    LOAD_CYCLE_1,
    //TODO any other additional states needed by various instructions
    FINISH_CURRENT_AND_FETCH_NEXT 
} state_e;

state_e state, next_state;

//TODO all of the inner goodness

endmodule : core_control
