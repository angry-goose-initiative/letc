/**
 * File    fifo_0r1w_tb.sv
 * Brief   TODO
 *
 * Copyright:
 *  Copyright (C) 2024-2025 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module fifo_0r1w_tb;

/* ------------------------------------------------------------------------------------------------
 * Parameters
 * --------------------------------------------------------------------------------------------- */

localparam CLOCK_PERIOD = 10;

localparam DWIDTH   = 32;
localparam DEPTH    = 3;

/* ------------------------------------------------------------------------------------------------
 * DUT Connections
 * --------------------------------------------------------------------------------------------- */

//Clock and reset
logic i_clk;
logic i_rst_n;

//Write port
logic               i_push;
logic               o_full;
logic [DWIDTH-1:0]  i_wdata;

//Read port
logic               i_pop;
logic               o_empty;
logic [DWIDTH-1:0]  o_rdata;

/* ------------------------------------------------------------------------------------------------
 * DUT
 * --------------------------------------------------------------------------------------------- */

fifo_0r1w #(
    .DWIDTH(DWIDTH),
    .DEPTH(DEPTH)
) dut (
    .*
);

/* ------------------------------------------------------------------------------------------------
 * Clocking
 * --------------------------------------------------------------------------------------------- */

clock_generator #(
    .PERIOD(CLOCK_PERIOD)
) clock_gen_inst (
    .clk(i_clk)
);

/* ------------------------------------------------------------------------------------------------
 * Tasks
 * --------------------------------------------------------------------------------------------- */

//verilator lint_save
//verilator lint_off INITIALDLY

//Note: due to quirks with Verilator, sadly we should try to avoid waiting for the next posedge in tasks

task setup();
begin
    $display("Running fifo_0r1w_tb testbench");

    //Set initial input states
    i_push   <= 1'b0;
    i_wdata  <= '0;
    i_pop    <= 1'b0;
end
endtask

task push(input logic [DWIDTH-1:0] data);
begin
    $display("Pushing 'h%h", data);
    assert(!o_full);

    i_push   <= 1'b1;
    i_wdata  <= data;
end
endtask

task pop_expecting(input logic [DWIDTH-1:0] data);
begin
    $display("Popped  'h%h (expected 'h%h)", o_rdata, data);
    assert(!o_empty);
    assert(o_rdata == data);

    i_pop <= 1'b1;
end
endtask

task peak();
begin
    assert(o_empty == 1'b0);
    $display("Peaked 'h%h", o_rdata);
end
endtask

task idle();
begin
    i_push   <= 1'b0;
    i_wdata  <= '0;
    i_pop    <= 1'b0;
end
endtask

//verilator lint_restore

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

initial begin
    //verilator lint_save
    //verilator lint_off INITIALDLY
    setup();

    //Reset things
    i_rst_n <= 1'b0;
    @(negedge i_clk);
    @(negedge i_clk);
    i_rst_n <= 1'b1;
    @(negedge i_clk);
    @(negedge i_clk);

    //Initial experiements with avoiding races with $display statements
    push(32'hCAFEBABE);
    @(negedge i_clk);//One cycle for the push to actually occur
    push(32'hDEADBEEF);
    pop_expecting(32'hCAFEBABE);
    @(negedge i_clk);
    push(32'hA5A5A5A5);
    pop_expecting(32'hDEADBEEF);
    @(negedge i_clk);
    idle();
    pop_expecting(32'hA5A5A5A5);
    @(negedge i_clk);
    idle();

    repeat(5) @(negedge i_clk);

    //Back-to-back push and pop tests
    i_push   <= 1'b1;
    i_wdata  <= 32'h11111111;
    i_pop    <= 1'b0;
    @(negedge i_clk);
    i_push   <= 1'b1;
    i_wdata  <= 32'h22222222;
    i_pop    <= 1'b1;
    assert(o_rdata == 32'h11111111);
    @(negedge i_clk);
    i_push   <= 1'b1;
    i_wdata  <= 32'h33333333;
    i_pop    <= 1'b1;
    assert(o_rdata == 32'h22222222);
    @(negedge i_clk);
    i_push   <= 1'b0;
    i_wdata  <= '0;
    i_pop    <= 1'b1;
    assert(o_rdata == 32'h33333333);
    @(negedge i_clk);
    i_push   <= 1'b0;
    i_wdata  <= '0;
    i_pop    <= 1'b0;

    repeat(5) @(negedge i_clk);
    $finish;

    //verilator lint_restore
end

endmodule : fifo_0r1w_tb
