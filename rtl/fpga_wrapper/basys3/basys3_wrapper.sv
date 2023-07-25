/*
 * File:    top_basys3.sv
 * Brief:   Connects LETC to Basys 3 board
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

module top_basys3 (
    input clk
);

letc_top letc_top_inst (
    .clk(clk)
)

endmodule
