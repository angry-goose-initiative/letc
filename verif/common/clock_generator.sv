/**
 * File    clock_generator.sv
 * Brief   Generates a clock for use in testbenches
 *
 * Copyright:
 *  Copyright (C) 2025 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module clock_generator #(
    parameter int PERIOD = 10
) (
    output logic clk
);

initial begin
    forever begin
        clk = 1'b0;
        #(PERIOD / 2);
        clk = 1'b1;
        #(PERIOD / 2);
    end
end

endmodule : clock_generator
