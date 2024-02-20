/*
 * File:    coraz7_top.v
 * Brief:   TODO
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * This must be a Verilog, not SystemVerilog, file because Vivado can't
 * bring this into a block design if it's SystemVerilog (which we need to do
 * to connect to the PS).
 *
*/

module coraz7_top
    //import letc_pkg::*;
(
    input wire clk,
    input wire rst_n,
    
    //TODO internal ports
    
    //External IO
    input  wire [1:0]   btn,
    output wire         led0_r,
    output wire         led0_g,
    output wire         led0_b,
    output wire         led1_r,
    output wire         led1_g,
    output wire         led1_b
    
    //TODO other external IO
);

//TESTING
reg [31:0] counter;
always @(posedge clk/*, negedge rst_n*/) begin
    /*if (!rst_n) begin
        counter = 32'h0;
    end else begin*/
        counter = counter + 1;
    //end
end
assign led0_r = 1'b1;
assign led0_g = 1'b0;
assign led0_b = 1'b1;
assign led1_r = counter[22];
assign led1_g = btn[0];
assign led1_b = 1'b0;

/* ------------------------------------------------------------------------------------------------
 * Module Instantiations
 * --------------------------------------------------------------------------------------------- */

letc_top letc_top_inst (//No .* in Verilog sadly
    .clk(clk),
    .rst_n(rst_n)
);

endmodule : coraz7_top
