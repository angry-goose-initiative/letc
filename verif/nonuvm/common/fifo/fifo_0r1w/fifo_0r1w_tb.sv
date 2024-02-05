/**
 * File    fifo_0r1w_tb.sv
 * Brief   TODO
 * 
 * Copyright:
 *  Copyright (C) 2024 John Jekel
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

//Note: due to quirks with Verilator, sadly we should try to avoid waiting for the next posedge in tasks

task setup();
begin
    $display("Running fifo_0r1w_tb testbench");

    //Set initial input states
    cb.i_push   <= 1'b0;
    cb.i_wdata  <= '0;
    cb.i_pop    <= 1'b0;
end
endtask

task push(input logic [DWIDTH-1:0] data);
begin
    $display("Pushing %h", data);

    cb.i_push   <= 1'b1;
    cb.i_wdata  <= data;
end
endtask

task pop();
begin
    $display("Popped %h", o_rdata);

    cb.i_pop <= 1'b1;
end
endtask

task peak();
begin
    assert(o_empty == 1'b0);
    $display("Peaked %h", o_rdata);
end
endtask

task idle();
begin
    cb.i_push   <= 1'b0;
    cb.i_wdata  <= '0;
    cb.i_pop    <= 1'b0;
end
endtask

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

initial begin
    setup();

    //Reset things
    i_rst_n = 1'b0;
    ##2;
    i_rst_n = 1'b1;
    ##2;

    //Initial experiements with avoiding races with $display statements
    push(32'hCAFEBABE);
    ##1;//One cycle for the signals from push() to take effect
    idle();
    ##1;//One cycle for the push to actually occur
    push(32'hDEADBEEF);
    pop();
    ##1;//One cycle for the signals from push() and pop to take effect
    idle();
    ##1;//One cycle for the push and pop to actually occur
    peak();
    ##2;
    push(32'hA5A5A5A5);
    pop();
    ##1;//One cycle for the signals from push() and pop to take effect
    idle();
    pop();//Note: What is said that is popped here is wrong because it takes a cycle for the first pop to actually occur
    ##1;//One cycle for the push and pop to actually occur; second pop signals also taking effect
    idle();
    ##1;//One cycle for the second pop to actually occur
    //FIFO is empty at this point

    ##5;

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
