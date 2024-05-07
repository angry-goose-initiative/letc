/**
 * File    letc_core_cache_tb.sv
 * Brief   TODO
 *
 * Copyright:
 *  Copyright (C) 2024 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

`default_nettype none

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_cache_tb;

import letc_pkg::*;
import letc_core_pkg::*;

/* ------------------------------------------------------------------------------------------------
 * Parameters
 * --------------------------------------------------------------------------------------------- */

localparam CLOCK_PERIOD = 10;
localparam TIMEOUT = 20;//TODO set upper bound

/* ------------------------------------------------------------------------------------------------
 * DUT Connections
 * --------------------------------------------------------------------------------------------- */

//Clock and reset
logic i_clk;
logic i_rst_n;

//Signal to flush all cache lines
logic i_flush_cache;

//Cache interface (LIMP)
letc_core_limp_if stage_limp(.*);

//LIMP interface to AXI FSM
letc_core_limp_if axi_fsm_limp(.*);

/* ------------------------------------------------------------------------------------------------
 * DUT
 * --------------------------------------------------------------------------------------------- */

letc_core_cache dut (.*);

/* ------------------------------------------------------------------------------------------------
 * Interface Workaround
 * --------------------------------------------------------------------------------------------- */

logic   stage_limp_valid;
logic   stage_limp_ready;
logic   stage_limp_wen_nren;
logic   stage_limp_uncacheable;
size_e  stage_limp_size;
paddr_t stage_limp_addr;
word_t  stage_limp_rdata;
word_t  stage_limp_wdata;

logic   axi_fsm_limp_valid;
logic   axi_fsm_limp_ready;
logic   axi_fsm_limp_wen_nren;
logic   axi_fsm_limp_uncacheable;
size_e  axi_fsm_limp_size;
paddr_t axi_fsm_limp_addr;
word_t  axi_fsm_limp_rdata;
word_t  axi_fsm_limp_wdata;

always_comb begin
    stage_limp.valid        = stage_limp_valid;
    stage_limp_ready        = stage_limp.ready;
    stage_limp.wen_nren     = stage_limp_wen_nren;
    stage_limp.uncacheable  = stage_limp_uncacheable;
    stage_limp.size         = stage_limp_size;
    stage_limp.addr         = stage_limp_addr;
    stage_limp_rdata        = stage_limp.rdata;
    stage_limp.wdata        = stage_limp_wdata;

    axi_fsm_limp_valid          = axi_fsm_limp.valid;
    axi_fsm_limp.ready          = axi_fsm_limp_ready;
    axi_fsm_limp_wen_nren       = axi_fsm_limp.wen_nren;
    axi_fsm_limp_uncacheable    = axi_fsm_limp.uncacheable;
    axi_fsm_limp_size           = axi_fsm_limp.size;
    axi_fsm_limp_addr           = axi_fsm_limp.addr;
    axi_fsm_limp.rdata          = axi_fsm_limp_rdata;
    axi_fsm_limp_wdata          = axi_fsm_limp.wdata;
end

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

    //Reset
    output i_rst_n;

    //Signal to flush all cache lines
    output i_flush_cache;

    //Cache interface (LIMP)
    output stage_limp_valid;
    input  stage_limp_ready;
    output stage_limp_wen_nren;//Write enable and not read enable
    output stage_limp_uncacheable;
    output stage_limp_size;
    output stage_limp_addr;
    input  stage_limp_rdata;
    output stage_limp_wdata;

    //LIMP interface to AXI FSM
    input  axi_fsm_limp_valid;
    output axi_fsm_limp_ready;
    input  axi_fsm_limp_wen_nren;//Write enable and not read enable
    input  axi_fsm_limp_uncacheable;
    input  axi_fsm_limp_size;
    input  axi_fsm_limp_addr;
    output axi_fsm_limp_rdata;
    input  axi_fsm_limp_wdata;

    /* verilator lint_on UNUSEDSIGNAL */
endclocking

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

initial begin
    int timeout_counter = 0;

    //Setup
    cb.stage_limp_valid         <= 1'b0;
    cb.axi_fsm_limp_ready       <= 1'b0;
    cb.i_flush_cache            <= 1'b0;
    cb.stage_limp_wen_nren      <= 1'b0;
    cb.stage_limp_uncacheable   <= 1'b0;

    //Reset things
    cb.i_rst_n <= 1'b0;
    ##2;
    cb.i_rst_n <= 1'b1;
    ##2;

    assert(dut.cache_line_valid == '0);//Cache should be empty after reset

    /////////////////////////////
    //Testing reads, with simple latency-free backing memory
    /////////////////////////////

    axi_fsm_limp_ready <= 1'b1;
    assign axi_fsm_limp_rdata = 32'hEFEF5678 + axi_fsm_limp_addr[31:0];

    //Fetch a word from 32'hABCD1234, pretty simple
    stage_limp_valid    <= 1'b1;
    stage_limp_wen_nren <= 1'b0;
    stage_limp_size     <= SIZE_WORD;
    stage_limp_addr     <= 32'hABCD1234;
    ##1;//One cycle for inputs to take effect
    assert(!stage_limp_ready);//Since the cache is empty, this won't be ready right away
    while (!stage_limp_ready) begin
        $display("Waiting for stage_limp_ready");
        ##1;
        ++timeout_counter;
        if (timeout_counter > TIMEOUT) begin
            $display("Timeout waiting for stage_limp_ready");
            $fatal;
        end
    end
    timeout_counter = 0;
    assert(stage_limp_rdata == (32'hEFEF5678 + axi_fsm_limp_addr[31:0]));

    //Tiny break to mix things up :)
    stage_limp_valid <= 1'b0;
    ##1;

    //Fetch a byte from 32'hABCD1230, which should be on the same cache line
    stage_limp_valid    <= 1'b1;
    stage_limp_wen_nren <= 1'b0;
    stage_limp_size     <= SIZE_BYTE;
    stage_limp_addr     <= 32'hABCD1230;
    ##1;//One cycle for inputs to take effect
    assert(stage_limp_ready);//Should hit
    assert(stage_limp_rdata == ((32'hEFEF5678 + axi_fsm_limp_addr[31:0]) & 32'hFF));

    //Fetch a halfword from 32'h11111110
    stage_limp_valid    <= 1'b1;
    stage_limp_wen_nren <= 1'b0;
    stage_limp_size     <= SIZE_WORD;
    stage_limp_addr     <= 32'h11111110;
    ##1;//One cycle for inputs to take effect
    assert(!stage_limp_ready);//Upper bits completely different, should miss
    while (!stage_limp_ready) begin
        $display("Waiting for stage_limp_ready");
        ##1;
        ++timeout_counter;
        if (timeout_counter > TIMEOUT) begin
            $display("Timeout waiting for stage_limp_ready");
            $fatal;
        end
    end
    timeout_counter = 0;
    assert(stage_limp_rdata == (32'hEFEF5678 + axi_fsm_limp_addr[31:0]));

    //Fetch a halfword from 32'hABCD1200, which should be on the same cache line as the first word
    stage_limp_valid    <= 1'b1;
    stage_limp_wen_nren <= 1'b0;
    stage_limp_size     <= SIZE_HALFWORD;
    stage_limp_addr     <= 32'hABCD1200;
    ##1;//One cycle for inputs to take effect
    assert(stage_limp_ready);//Should hit
    assert(stage_limp_rdata == ((32'hEFEF5678 + axi_fsm_limp_addr[31:0]) & 32'hFFFF));

    /////////////////////////////
    //Testing invalidation on writes and uncached reads
    /////////////////////////////

    //Write a halfword t0 32'hABCD1202, which should invalidate the cache line
    stage_limp_valid    <= 1'b1;
    stage_limp_wen_nren <= 1'b1;
    stage_limp_size     <= SIZE_HALFWORD;
    stage_limp_addr     <= 32'hABCD1202;
    stage_limp_wdata    <= 32'h3C3CA5A5;
    ##1;//One cycle for inputs to take effect
    assert(stage_limp_ready);//Should write through and work immediately
    assert(axi_fsm_limp_wdata == 32'h3C3CA5A5);//The write should be passed through

    //Fetch a byte from 32'hABCD1233, which will miss due to the invalidation
    stage_limp_valid    <= 1'b1;
    stage_limp_wen_nren <= 1'b0;
    stage_limp_size     <= SIZE_BYTE;
    stage_limp_addr     <= 32'hABCD1230;
    ##1;//One cycle for inputs to take effect
    assert(!stage_limp_ready);
    while (!stage_limp_ready) begin
        $display("Waiting for stage_limp_ready");
        ##1;
        ++timeout_counter;
        if (timeout_counter > TIMEOUT) begin
            $display("Timeout waiting for stage_limp_ready");
            $fatal;
        end
    end
    timeout_counter = 0;
    assert(stage_limp_rdata == ((32'hEFEF5678 + axi_fsm_limp_addr[31:0]) & 32'hFF));

    axi_fsm_limp_ready <= 1'b0;

    /////////////////////////////
    //Testing write-through
    /////////////////////////////

    //TODO

`ifndef VERILATOR
    //Verilator sometimes doesn't like deassign
    deassign axi_fsm_limp_rdata;

    /////////////////////////////
    //Testing reads, with more complex backing memory latencies
    /////////////////////////////

    //TODO

`endif //VERILATOR

    ##10;
    $finish;
end

endmodule : letc_core_cache_tb
