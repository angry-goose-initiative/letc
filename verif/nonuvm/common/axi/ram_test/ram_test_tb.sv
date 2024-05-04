/**
 * File    ram_test_tb.sv
 * Brief   connects the axi fsm to a generic axi4 ram for testing
 *
 * Copyright:
 *  Copyright (C) 2024 Eric Jessee
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

`default_nettype none

module ram_test_tb;

import letc_pkg::*;
import letc_core_pkg::*;
import axi_pkg::*;

//ram
//this is the vivado-generated ram IP with an axi4 interface,
//for testing the axi fsm and eventually the cache
test_ram ram(.*);

logic        rsta_busy;
logic        rstb_busy;
logic        s_aclk;
logic        s_aresetn;
logic [3:0]  s_axi_awid;
logic [31:0] s_axi_awaddr;
logic [7:0]  s_axi_awlen;
logic [2:0]  s_axi_awsize;
logic [1:0]  s_axi_awburst;
logic        s_axi_awvalid;
logic        s_axi_awready;
logic [31:0] s_axi_wdata;
logic [3:0]  s_axi_wstrb;
logic        s_axi_wlast;
logic        s_axi_wvalid;
logic        s_axi_wready;
logic [3:0]  s_axi_bid;
logic [1:0]  s_axi_bresp;
logic        s_axi_bvalid;
logic        s_axi_bready;
logic [3:0]  s_axi_arid;
logic [31:0] s_axi_araddr;
logic [7:0]  s_axi_arlen;
logic [2:0]  s_axi_arsize;
logic [1:0]  s_axi_arburst;
logic        s_axi_arvalid;
logic        s_axi_arready;
logic [3:0]  s_axi_rid;
logic [31:0] s_axi_rdata;
logic [1:0]  s_axi_rresp;
logic        s_axi_rlast;
logic        s_axi_rvalid;
logic        s_axi_rready;

//DUT
logic i_clk;
logic i_rst_n;
axi_if axi(.i_aclk(i_clk), .i_arst_n(i_rst_n), .*);
letc_core_limp_if limp[2:0](.*);

letc_core_axi_fsm dut(.*);

//connections between axi if and ram IP
always_comb begin
    s_aclk         = i_clk;
    s_aresetn      = i_rst_n;
    s_axi_awid     = axi.awid;
    s_axi_awaddr   = axi.awaddr;
    s_axi_awlen    = axi.awlen;
    s_axi_awsize   = axi.awsize;
    s_axi_awburst  = axi.awburst;
    s_axi_awvalid  = axi.awvalid;
    axi.awready    = s_axi_awready;
    s_axi_wdata    = axi.wdata;
    s_axi_wstrb    = axi.wstrb;
    s_axi_wlast    = axi.wlast;
    s_axi_wvalid   = axi.wvalid;
    axi.wready     = s_axi_wready;
    axi.bid        = s_axi_bid;
    axi.bresp      = resp_e'(s_axi_bresp);
    axi.bvalid     = s_axi_bvalid;
    s_axi_bready   = axi.bready;
    s_axi_arid     = axi.arid;
    s_axi_araddr   = axi.araddr;
    s_axi_arlen    = axi.arlen;
    s_axi_arsize   = axi.arsize;
    s_axi_arburst  = axi.arburst;
    s_axi_arvalid  = axi.arvalid;
    axi.arready    = s_axi_arready;
    axi.rid        = s_axi_rid;
    axi.rdata      = s_axi_rdata;
    axi.rresp      = resp_e'(s_axi_rresp);
    axi.rlast      = s_axi_rlast;
    axi.rvalid     = s_axi_rvalid;
    s_axi_rready   = axi.rready;
end

//limp interface signals - we will use these to drive
//the axi fsm.
logic   limp_valid;
logic   limp_ready;
logic   limp_wen_nren;
logic   limp_bypass;
size_e  limp_size;
paddr_t limp_addr;
word_t  limp_rdata;
word_t  limp_wdata;

always_comb begin
    limp[0].valid    = limp_valid;
    limp_ready    = limp[0].ready;
    limp[0].wen_nren = limp_wen_nren;
    limp_bypass   = limp[0].bypass;
    limp[0].size     = limp_size;
    limp[0].addr     = limp_addr;
    limp_rdata    = limp[0].rdata;
    limp[0].wdata    = limp_wdata;

    limp[1].valid    = 1'b0; 
    limp[1].wen_nren = 1'b0; 

    limp[2].valid    = 1'b0; 
    limp[2].wen_nren = 1'b0; 
end

//clocking
localparam CLOCK_PERIOD = 10;
initial begin
    forever begin
        i_clk = 1'b0;
        #(CLOCK_PERIOD / 2);
        i_clk = 1'b1;
        #(CLOCK_PERIOD / 2);
    end
end

default clocking cb @(posedge i_clk);
    output i_rst_n;
    output limp_valid;
    input  limp_ready;
    output limp_wen_nren;
    output limp_bypass;
    output limp_size;
    output limp_addr;
    input  limp_rdata;
    output limp_wdata;
endclocking

int timeout_counter = 0;
localparam TIMEOUT = 100;
localparam[31:0] writeData = 32'hbeefcafe;
task wait_ready();
    while (!limp_ready) begin
        $display("Waiting for limp_ready");
        ##1;
        ++timeout_counter;
        if (timeout_counter > TIMEOUT) begin
            $display("Timeout waiting for limp_ready");
            $fatal;
        end
    end
endtask

initial begin
    //inital values
    cb.i_rst_n <= 1'b0;
    cb.limp_valid <= 1'b0;
    cb.limp_wen_nren <= 1'b0;
    cb.limp_bypass <= 1'b0;
    cb.limp_size <= SIZE_WORD;
    ##2
    cb.i_rst_n <= 1'b1;
    ##2
    //first write something to address 0xf
    cb.limp_addr <= 32'hf;
    cb.limp_wen_nren <= 1'b1;
    cb.limp_wdata <= writeData;
    cb.limp_valid <= 1'b1;
    //wait for the write to finish
    ##1
    $display("Waiting for write to complete");
    wait_ready();
    //then try to read the data back
    cb.i_rst_n <= 1'b1;
    cb.limp_valid <= 1'b1;
    cb.limp_addr <= 32'hf;
    $display("Waiting for read to complete");
    wait_ready();
    assert(limp_rdata == writeData);
    ##20
    $finish;
end

endmodule: ram_test_tb
