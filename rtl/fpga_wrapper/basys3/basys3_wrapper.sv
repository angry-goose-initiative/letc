/*
 * File:    basys3_wrapper.sv
 * Brief:   Connects LETC to Basys 3 board
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

module basys3_wrapper (
    input   logic   clk
);

letc_top letc_top_inst (
    .clk(clk)
);

endmodule : basys3_wrapper
