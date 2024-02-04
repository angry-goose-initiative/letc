/*
 * File:    fifo_1r1w.sv
 * Brief:   FIFO with 1-cycle read latency and write latencies
 *
 * Copyright:
 *  Copyright (C) 2024 John Jekel\n
 * See the LICENSE file at the root of the project for licensing info.
 *
 * As long as i_pop is deasserted, o_rdata will be held for convenience
 *
 * Parameters:
 *     DWIDTH:  Data width of the FIFO
 *     DEPTH:   Depth of the FIFO
 *
 * It is undefined behaviour to push while full or pop while empty
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module fifo_1r1w #(
    parameter DWIDTH    = 8,
    parameter DEPTH     = 4
) (
    //Clock and reset
    input   logic i_clk,
    input   logic i_rst_n,

    //Write port (1-cycle latency)
    input   logic               i_push,
    output  logic               o_full,
    input   logic [DWIDTH-1:0]  i_wdata,
    
    //Read port (0-cycle latency)
    input   logic               i_pop,
    output  logic               o_empty,
    output  logic [DWIDTH-1:0]  o_rdata
);

localparam AWIDTH = $clog2(DEPTH);

/* ------------------------------------------------------------------------------------------------
 * State
 * --------------------------------------------------------------------------------------------- */

logic [DEPTH-1:0] [DWIDTH-1:0] mem;
logic [AWIDTH-1:0] push_idx, pop_idx, next_push_idx, next_pop_idx;

/* ------------------------------------------------------------------------------------------------
 * Logic
 * --------------------------------------------------------------------------------------------- */

always_comb begin
    //TODO be more efficient when DEPTH is a power of 2
    next_push_idx   = (push_idx == (AWIDTH)'(DEPTH - 1)) ? '0 : push_idx + (AWIDTH)'(1);
    next_pop_idx    = (pop_idx  == (AWIDTH)'(DEPTH - 1)) ? '0 : pop_idx  + (AWIDTH)'(1);

    o_full  = next_push_idx == pop_idx;//Next push would make it indistinguishable from empty
    o_empty = push_idx == pop_idx;
end

always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (~i_rst_n) begin
        push_idx    <= '0;
        pop_idx     <= '0;
        //Save area by not resetting mem
    end else begin
        if (i_push) begin
            push_idx        <= next_push_idx;
            mem[push_idx]   <= i_wdata;//Input demux (1-cycle latency)
        end

        if (i_pop) begin
            pop_idx <= next_pop_idx;
            o_rdata <= mem[pop_idx];//Output mux (1-cycle latency)
        end
    end
end

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

//Parameter Assertions
initial begin
    assert (DWIDTH > 0);
    assert (DEPTH > 0);
end

//Ensure input into the FIFO is valid
/* verilator lint_off SYNCASYNCNET */
assert property (@(posedge i_clk) disable iff (!i_rst_n) !(i_push & o_full));
/* verilator lint_on SYNCASYNCNET */
assert property (@(posedge i_clk) disable iff (!i_rst_n) !(i_pop & o_empty));

//Ensure pointers never go out of bounds
assert property (@(posedge i_clk) disable iff (!i_rst_n) !(push_idx >= (AWIDTH)'(DEPTH)));
assert property (@(posedge i_clk) disable iff (!i_rst_n) !(pop_idx  >= (AWIDTH)'(DEPTH)));

`endif

endmodule : fifo_1r1w
