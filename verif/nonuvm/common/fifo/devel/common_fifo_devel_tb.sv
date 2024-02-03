/**
 * File    common_fifo_devel_tb.sv
 * Brief   TODO
 * 
 * Copyright
 *  Copyright (C) 2024 John Jekel\n
 * See the LICENSE file at the root of the project for licensing info.
 * 
 * TODO longer description
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Declaration
 * --------------------------------------------------------------------------------------------- */

module common_fifo_devel_tb();

localparam DATA_WIDTH = 32;
localparam ADDR_WIDTH = 2;

/* ------------------------------------------------------------------------------------------------
 * DUT Connections
 * --------------------------------------------------------------------------------------------- */

logic clk;
logic rst_n;

logic push;
logic full;
logic [DATA_WIDTH - 1:0] data_in;

logic pop;
logic empty;
logic [DATA_WIDTH - 1:0] data_out;

/* ------------------------------------------------------------------------------------------------
 * DUT
 * --------------------------------------------------------------------------------------------- */

fifo #(
    .DATA_WIDTH(DATA_WIDTH),
    .ADDR_WIDTH(ADDR_WIDTH)
) dut (
    .*
);

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

initial begin
    $display("Running common_fifo_devel_tb testbench");

    #4;//Wait for reset to finish
    
    #1;//We set things on negedges to make things more clear

    data_in = 32'hCAFEBABE;
    push = 1'b1;
    #2;//Wait one cc
    data_in = 32'hDEADBEEF;
    push = 1'b1;
    pop = 1'b1;
    $display("Popped %h", data_out);
    #2;
    push = 1'b0;
    pop = 1'b0;
    $display("Peaked %h", data_out);

    #1000;//TODO test stimulus

    $finish;
end

initial begin
    rst_n   = 1'b0;
    clk     = 1'b0;
    #4;
    rst_n   = 1'b1;

    forever begin
        clk = ~clk;
        #1;
    end
end

endmodule : common_fifo_devel_tb
