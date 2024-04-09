/*
 * File:    shift_register.sv
 * Brief:   Simple left-shift register.
 *
 * Copyright:
 *  Copyright (C) 2024 Eric Jessee
 * See the LICENSE file at the root of the project for licensing info.
 *
*/

module shift_register #(
    parameter int WIDTH = 8
) (
    input logic i_clk,
    input logic i_rst_n,

    input logic i_sdata,
    input logic i_shift,
    input logic i_load,
    input logic [WIDTH-1:0] i_ldata,

    output logic [WIDTH-1:0] o_data,
    output logic o_carryout
);

logic [WIDTH-1:0] data;

always_ff @(posedge i_clk) begin
    if (!i_rst_n) begin
        data <= '0;
        o_carryout <= 1'b0;
    end else if (i_load) begin
        data <= i_ldata;
        o_carryout <= 1'b0;
    end else if (i_shift) begin
        data[0] <= i_sdata;
        for (int i=1; i<WIDTH; ++i) begin
            data[i] <= data[i-1];
        end
        o_carryout <= data[WIDTH-1];
    end
end

always_comb begin
    o_data = data;
end

endmodule
