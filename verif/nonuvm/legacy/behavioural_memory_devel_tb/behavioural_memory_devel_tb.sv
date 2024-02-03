/*
 * File:    behavioural_memory_devel_tb.sv
 * Brief:   TODO
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

module behavioural_memory_devel_tb();
import axi_pkg::*;

global_s axi_global;
req_s    req;
rsp_s    rsp;

behavioural_axi_memory mem(.*);

initial begin
    $display("Starting behavioural_memory_devel_tb");
    $dumpfile(`DUMPFILE_PATH);
    $dumpvars(0, firsttb);

    //TODO support bursts and fancy stuff like that
    req.awlen = '0;
    req.arlen = '0;
    req.awburst = AXI_BURST_FIXED;
    req.arburst = AXI_BURST_FIXED;

    #4;//Wait for reset to finish

    #1;//We change things at negative edges to make debugging more clear

    //Clock cycle 1
    req.awvalid = 1'b1;
    req.awaddr  = 32'hDEADBEEF;
    req.awid    = '1;
    #2;

    //Clock cycle 2
    req.awvalid = 1'b0;
    req.awaddr  = '0;
    req.awid    = '0;
    req.wvalid  = 1'b1;
    req.wid     = '1;
    req.wdata   = 32'hCAFEBABE;
    req.wstrb   = 4'b1111;
    #2;

    //Clock cycle 3
    req.wvalid  = 1'b0;
    req.wdata   = '0;
    req.wstrb   = '0;
    #2;

    //Clock cycle 4
    req.bready  = 1'b1;//Since we assume we'll get a response 1 cycle later
    #2;

    //Clock cycle 5
    req.bready  = 1'b0;
    #2;

    #1000;//TODO test stimulus

    $finish;
end

initial begin
    axi_global.aresetn  = 1'b0;
    axi_global.aclk     = 1'b0;
    #4;
    axi_global.aresetn  = 1'b1;

    forever begin
        axi_global.aclk = ~axi_global.aclk;
        #1;
    end
end

endmodule : behavioural_memory_devel_tb
