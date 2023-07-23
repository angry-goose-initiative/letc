/*
 * File:    core_control.sv
 * Brief:   TODO
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

import letc_pkg::*;

module core_control (
    input clk,
    input rst_n

    //TODO other ports

);

//TODO all of the inner goodness

typedef enum logic [1:0] {
    INIT,
    FETCH,
    DECODE,
    EXECUTE
    //TODO this will likely change in the future
} state_e;

state_e state, next_state;

always_ff @(posedge clk, negedge rst_n) begin
    if (!rst_n) begin
        state <= INIT;
    end else begin
        state <= next_state;
    end
end

always_comb begin
    next_state = state_e'(state + 2'b1);//TESTING
    /*
    case (state)
        INIT: begin
            //TODO
        end
        FETCH: begin
            //TODO
        end
        DECODE: begin
            //TODO
        end
        EXECUTE: begin
            //TODO
        end
        default: begin
            //TODO
        end
    endcase
    */
end

endmodule
