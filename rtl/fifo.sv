/*
 * File:    fifo.sv
 * Brief:   TODO
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

module fifo #(
    parameter DATA_WIDTH = 8,
    parameter ADDR_WIDTH = 4//Usable entries is (2 ** ADDR_WIDTH) - 1
    //TODO add parameters to control various latencies (ex. a parameter to
    //allow push->pop forwarding in the same cc)
) (
    input   logic clk,

    input   logic rst_n,

    //It is undefined behaviour to push while full or pop while empty

    //Write port
    input   logic                   push,
    output  logic                   full,
    input   logic [DATA_WIDTH-1:0]  data_in,
    
    //Read port
    input   logic                   pop,
    output  logic                   empty,
    output  logic [DATA_WIDTH-1:0]  data_out
);

localparam DEPTH = 2 ** ADDR_WIDTH;

logic [DATA_WIDTH - 1:0] mem [DEPTH - 1:0];
logic [ADDR_WIDTH - 1:0] push_idx, pop_idx, next_push_idx, next_pop_idx;

assign full = next_push_idx == pop_idx;
assign empty = push_idx == pop_idx;

//Works since DEPTH is a power of 2
assign next_push_idx = push_idx + 1;
assign next_pop_idx = pop_idx + 1;

assign data_out = mem[pop_idx];//Output multiplexer

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        push_idx <= '0;
        pop_idx <= '0;
    end else begin
        if (push) begin//Assumes not full
            mem[push_idx] <= data_in;//Input multiplexer
            push_idx <= next_push_idx;
        end

        if (pop) begin//Assumes not empty
            pop_idx <= next_pop_idx;
        end
    end
end

endmodule : fifo
