/**
 * File    fifo_0r1w_tb.sv
 * Brief   TODO
 * 
 * Copyright:
 *  Copyright (C) 2024 John Jekel\n
 * See the LICENSE file at the root of the project for licensing info.
 * 
 * TODO longer description
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module fifo_0r1w_tb;

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

initial begin
    forever begin
        i_clk = 1'b0;
        #(CLOCK_PERIOD / 2);
        i_clk = 1'b1;
        #(CLOCK_PERIOD / 2);
    end
end

default clocking cb @(posedge i_clk);
    //Not sure why Verilator complains...
    /* verilator lint_off UNUSEDSIGNAL */

    //Write port
    output  i_push;
    input   o_full;
    output  i_wdata;

    //Read port
    output  i_pop;
    input   o_empty;
    input   o_rdata;

    /* verilator lint_on UNUSEDSIGNAL */
endclocking

/* ------------------------------------------------------------------------------------------------
 * Tasks
 * --------------------------------------------------------------------------------------------- */

task setup;
begin
    $display("Running fifo_0r1w_tb testbench");

    //Set initial input states
    cb.i_push   <= 1'b0;
    cb.i_wdata  <= '0;
    cb.i_pop    <= 1'b0;

    //Reset things
    i_rst_n = 1'b0;
    //##2;//Verilator doesn't like this in tasks for some reason
    @(posedge i_clk);
    @(posedge i_clk);
    i_rst_n = 1'b1;
    //##2;
    @(posedge i_clk);
    @(posedge i_clk);
end
endtask

task push(input logic [DWIDTH-1:0] data);
begin
    $display("Setting up push signals next posedge");

    //Stimulus signals go out right after the posedge
    cb.i_push   <= 1'b1;
    cb.i_wdata  <= data;
    @(posedge i_clk);

    $display("Pushing %h", data);

    //We disable them right after the next posedge where the push occurs
    cb.i_push   <= 1'b0;
    cb.i_wdata  <= '0;
    @(posedge i_clk);

    $display("Pushed %h", data);
end
endtask

task pop();
begin
    $display("Popped (peaked) %h, and setting up pop signals next posedge", o_rdata);

    //Stimulus signals go out right after the posedge
    cb.i_pop <= 1'b1;
    @(posedge i_clk);

    $display("Pop will take effect next posedge, popped data is still %h", o_rdata);

    //We disable them right after the next posedge where the pop takes effect
    cb.i_pop <= 1'b0;
    @(posedge i_clk);

    $display("Pop took effect; (invalid/next) pop data is now %h", o_rdata);
end
endtask

task peak();
begin
    assert(o_empty == 1'b0);
    $display("Peaked %h", o_rdata);
end
endtask

task push_and_pop(input logic [DWIDTH-1:0] data);
begin
    $display("Popped (peaked) %h, and setting up push and pop signals next posedge", o_rdata);

    //Stimulus signals go out right after the posedge
    cb.i_push   <= 1'b1;
    cb.i_wdata  <= data;
    cb.i_pop    <= 1'b1;
    @(posedge i_clk);

    $display("Pushing %h, and pop will take effect next posedge; pop data is still %h", data, o_rdata);

    //We disable them right after the next posedge where the push occurs and pop takes effect
    cb.i_push   <= 1'b0;
    cb.i_wdata  <= '0;
    cb.i_pop    <= 1'b0;
    @(posedge i_clk);

    $display("Pushed %h and pop took effect; (invalid/next) pop data is now %h", data, o_rdata);
end
endtask

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

initial begin
    setup();

    //Initial experiements with avoiding races with $display statements
    push(32'hCAFEBABE);
    push_and_pop(32'hDEADBEEF);
    //peak();
    pop();
    //FIFO is empty at this point

    //Back-to-back push and pop tests
    //It's a bit unintuitive but remember that the signals don't actually take
    //effect until just after the posedge AFTER the signals are set
    //This delays things by a cycle then what you might exepect with this
    //stimulus but it doesn't really matter
    cb.i_push   <= 1'b1;
    cb.i_wdata  <= 32'h11111111;
    cb.i_pop    <= 1'b0;
    ##1;
    cb.i_push   <= 1'b1;
    cb.i_wdata  <= 32'h22222222;
    cb.i_pop    <= 1'b1;
    ##1;
    cb.i_push   <= 1'b1;
    cb.i_wdata  <= 32'h33333333;
    cb.i_pop    <= 1'b1;
    ##1;
    cb.i_push   <= 1'b0;
    cb.i_wdata  <= '0;
    cb.i_pop    <= 1'b1;
    ##1;
    cb.i_push   <= 1'b0;
    cb.i_wdata  <= '0;
    cb.i_pop    <= 1'b0;

    ##5;
    $finish;
end

endmodule : fifo_0r1w_tb
