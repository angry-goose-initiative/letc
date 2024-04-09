/*
 * File:    counter.sv
 * Brief:   Simple module that stores a value and increments it.
 *
 * Copyright:
 *  Copyright (C) 2024 Eric Jessee
 * See the LICENSE file at the root of the project for licensing info.
 *
*/

module counter #(
    parameter int WIDTH = 32,
    parameter int STEP = 4
) (
    input logic i_clk,
    input logic i_rst_n,
    //address in/out
    input  logic [WIDTH-1:0]  i_addr,
    output logic [WIDTH-1:0]  o_addr,
    //control signals
    input logic i_en,
    input logic i_load // load == !count
);

logic [WIDTH-1:0] addr;
always_comb begin
    o_addr = addr;
end

always_ff @(posedge i_clk) begin
    if(!i_rst_n) begin
        addr <= 'h0;
    end else if (i_en) begin
        if (i_load) begin
            addr <= i_addr;
        end else begin
            addr <= addr + STEP;
        end
    end
end

endmodule
