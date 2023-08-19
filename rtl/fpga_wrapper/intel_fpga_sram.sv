/*
 * File:    intel_fpga_sram.sv
 * Brief:   Inferred SRAM for Intel FPGAs
 *
 * Copyright (C) 2023 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * Designed with the limitations of Intel FPGAs in mind, discussed at:
 * https://www.intel.com/content/www/us/en/docs/programmable/683082/23-1/use-synchronous-memory-blocks.html
 * https://www.intel.com/content/www/us/en/docs/programmable/683082/23-1/true-dual-port-synchronous-ram.html
 *
 * Also with reference to my old (poorly written) module:
 * https://git.jekel.ca/JZJ/jzjpipelinedcorec/src/branch/master/src/jzjpcc/memory_backend/jzjpcc_inferred_sram.sv
 *
 * NOTE: To initialize the SRAM with default contents, use an initial block
 * from a testbench or outer FPGA wrapper (which is okayish practice for FPGAs). Alternatively, there are
 * likely options in the Quartus IDE that probably are the "proper" way to do it.
 *
 * NOTE: This module is dual ported. If you don't need the second port,
 * just tie the relevant signals off and ignore unneeded outputs.
 * Each port also has its own clock, which is useful for, ex. CDC FIFOs.
 *
 * NOTE: To use this as a ROM, similiarly tie off all of the write signals.
 *
 * NOTE: Intel FPGA memories have a mandatory 1-cycle latency for both reads and writes.
 * Note that this mandatory flop stage is on the INPUTS to the SRAMs (at least for M9K on Cyclone IV).
 * You may want to add a flop stage to the output to help with timing if needed.
 *
 *  All SRAM inputs
 *  |    -------       --------
 *  V    |  V  |       | COMB |
 * ------|     |-------| SRAM |------ (optional extra flop stage) ------ Output
 *       |     |       |      |
 *       |     |       |      |
 *       -------       --------
 *
 * NOTE: In terms of the interations between reads and writes:
 * - We always read the old data written to the SRAM, even on the same port
 * - Multiple simultaneous writes to the same address are undefined
 *
*/

/* ------------------------------------------------------------------------------------------------
 * The Cleaner Approach That Is Sadly Unsupported By Quartus
 * --------------------------------------------------------------------------------------------- */
/*
//This is the cleaner approach. However, there are two issues:
//- Quartus doesn't support avoiding the generate block, even though SystemVerilog no longer requires it for for-loops and if statements in the module scope
//- Quartus doesn't infer SRAM from this properly, leading to multiple drivers in synthesis, when you use loops with the WBMASK
//  Technically, since we have 2 write ports with no priority logic, there is multiple drivers, but Quartus should ignore that in this situation
//  and infer SRAM. But it does not...
module ideal_intel_fpga_sram_module #(
    parameter   DEPTH           = 1024,//In number of entries: must be a power of 2
    parameter   WIDTH           = 8,//In bits: must be non-zero
    parameter   OUTPUT_REGISTER = 0//If 1, adds a flop stage to the output
) (
    //All signals are duplicated, once per port
    input   logic [1:0]                         clk,
    input   logic [1:0] [ADDR_WIDTH - 1:0]      addr,
    input   logic [1:0]                         re,
    output  logic [1:0] [WIDTH - 1:0]           rdata,
    input   logic [1:0]                         we,
    input   logic [1:0] [WIDTH - 1:0]           wdata,
    input   logic [1:0] [WBMASK_WIDTH - 1:0]    wbmask
);

localparam  ADDR_WIDTH          = $clog2(DEPTH);
localparam  WBMASK_WIDTH        = (WIDTH / 8) + ((WIDTH % 8) ? 1 : 0);
localparam  INTERNAL_DATA_WIDTH = WBMASK_WIDTH * 8;

logic [INTERNAL_DATA_WIDTH - 1:0] sram [DEPTH - 1:0];
logic [1:0] [WIDTH - 1:0] rdata_internal;

//Note: It is misleading, but when mapped to SRAM blocks
//by Quartus, the addr, wdata, we, re, wbmask, etc. are latched on
//the positive edges. The read outputs actually happen
//combinationally, even though it looks like there is only an output register in the RTL
//Check out the chip planner to see what I mean (or check out the ASCII art
//at the top of the file)

for (genvar i = 0; i < 2; ++i) begin : ports
    always_ff @(posedge clk[i]) begin
        //SRAM writes
        if (we[i]) begin
            for (int j = 0; j < WBMASK_WIDTH; ++j) begin
                if (wbmask[i][j]) begin
                    sram[addr[i]][j * 8 +: 8] <= wdata[i][j * 8 +: 8];
                end
            end
        end

        //SRAM reads
        if (re[i]) begin
            rdata_internal[i] <= sram[addr[i]][DATA_WIDTH - 1:0];
        end
    end
end : ports

//Optionally add a flop stage to the output
if (OUTPUT_REGISTER) begin
    for (genvar i = 0; i < 2; ++i) begin : output_register
        always_ff @(posedge clk[i]) begin
            rdata[i] <= rdata_internal[i];
        end
    end : output_register
end else begin
    assign rdata = rdata_internal;
end

endmodule : ideal_intel_fpga_sram_module
*/

/* ------------------------------------------------------------------------------------------------
 * The Workaround
 * --------------------------------------------------------------------------------------------- */

//Basically we do a generic one without a wbmask, and then we add a few
//popular fixed-width ones with wbmask. This sucks, but it works.
//We also use generate blocks so that Quartus doesn't complain despite the
//fact that we shouldn't need them with SystemVerilog.

module intel_fpga_sram_generic #(
    parameter   DEPTH           = 1024,//In number of entries: must be a power of 2
    parameter   WIDTH           = 8,//In bits: must be non-zero
    parameter   OUTPUT_REGISTER = 0//If 1, adds a flop stage to the output
) (
    //All signals are duplicated, once per port
    input   logic [1:0]                     clk,
    input   logic [1:0] [ADDR_WIDTH - 1:0]  addr,
    input   logic [1:0]                     re,
    output  logic [1:0] [WIDTH - 1:0]       rdata,
    input   logic [1:0]                     we,
    input   logic [1:0] [WIDTH - 1:0]       wdata
    //No wbmask available in the generic version :(
);

localparam ADDR_WIDTH = $clog2(DEPTH);

logic [WIDTH - 1:0] sram [DEPTH - 1:0];
logic [1:0] [WIDTH - 1:0] rdata_internal;

//Note: It is misleading, but when mapped to SRAM blocks
//by Quartus, the addr, wdata, we, re, wbmask, etc. are latched on
//the positive edges. The read outputs actually happen
//combinationally, even though it looks like there is only an output register in the RTL
//Check out the chip planner to see what I mean (or check out the ASCII art
//at the top of the file)

generate
    genvar i;

    //We also can't do this as a loop either, else Quartus fails to infer SRAM
    //and we get multiple-driver errors in synthesis
    /*
    for (i = 0; i < 2; ++i) begin : ports
        always_ff @(posedge clk[i]) begin
            //SRAM writes
            if (we[i]) begin
                sram[addr[i]] <= wdata[i];
            end

            //SRAM reads
            if (re[i]) begin
                rdata_internal[i] <= sram[addr[i]];
            end
        end
    end : ports
    */
    `define intel_fpga_sram_generic_port(port) \
        always_ff @(posedge clk[port]) begin \
            if (we[port]) begin \
                sram[addr[port]] <= wdata[port]; \
            end \
            \
            if (re[port]) begin \
                rdata_internal[port] <= sram[addr[port]]; \
            end \
        end
    `intel_fpga_sram_generic_port(0)
    `intel_fpga_sram_generic_port(1)

    //Optionally add a flop stage to the output
    if (OUTPUT_REGISTER) begin
        for (i = 0; i < 2; ++i) begin : output_register
            always_ff @(posedge clk[i]) begin
                rdata[i] <= rdata_internal[i];
            end
        end : output_register
    end else begin
        assign rdata = rdata_internal;
    end
endgenerate

endmodule : intel_fpga_sram_generic

module intel_fpga_sram_32 #(
    parameter   DEPTH           = 1024,//In number of entries: must be a power of 2
    //The width is fixed to 32, but in return you get wbmask
    parameter   OUTPUT_REGISTER = 0//If 1, adds a flop stage to the output
) (
    //All signals are duplicated, once per port
    input   logic [1:0]                     clk,
    input   logic [1:0] [ADDR_WIDTH - 1:0]  addr,
    input   logic [1:0]                     re,
    output  logic [1:0] [31:0]              rdata,
    input   logic [1:0]                     we,
    input   logic [1:0] [31:0]              wdata,
    input   logic [1:0] [3:0]               wbmask
);

localparam ADDR_WIDTH = $clog2(DEPTH);

logic [3:0] [7:0] sram [DEPTH - 1:0];
logic [1:0] [31:0] rdata_internal;

//Note: It is misleading, but when mapped to SRAM blocks
//by Quartus, the addr, wdata, we, re, wbmask, etc. are latched on
//the positive edges. The read outputs actually happen
//combinationally, even though it looks like there is only an output register in the RTL
//Check out the chip planner to see what I mean (or check out the ASCII art
//at the top of the file)

generate
    genvar i;

    //We also can't do this as a loop either, else Quartus fails to infer SRAM
    //and we get multiple-driver errors in synthesis (neither a loop for the
    //port nor for the wbmask)
    `define intel_fpga_sram_32_wbmask(port, the_byte) \
        if (wbmask[port][the_byte]) begin \
            sram[addr[port]][the_byte] <= wdata[port][the_byte * 8+:8]; \
        end
    `define intel_fpga_sram_32_port(port) \
        always_ff @(posedge clk[port]) begin \
            if (we[port]) begin \
                `intel_fpga_sram_32_wbmask(port, 0) \
                `intel_fpga_sram_32_wbmask(port, 1) \
                `intel_fpga_sram_32_wbmask(port, 2) \
                `intel_fpga_sram_32_wbmask(port, 3) \
            end \
            \
            if (re[port]) begin \
                rdata_internal[port] <= sram[addr[port]]; \
            end \
        end
    `intel_fpga_sram_32_port(0)
    `intel_fpga_sram_32_port(1)

    //Optionally add a flop stage to the output
    if (OUTPUT_REGISTER) begin
        for (i = 0; i < 2; ++i) begin : output_register
            always_ff @(posedge clk[i]) begin
                rdata[i] <= rdata_internal[i];
            end
        end : output_register
    end else begin
        assign rdata = rdata_internal;
    end
endgenerate

endmodule : intel_fpga_sram_32

module intel_fpga_sram_64 #(
    parameter   DEPTH           = 1024,//In number of entries: must be a power of 2
    //The width is fixed to 64, but in return you get wbmask
    parameter   OUTPUT_REGISTER = 0//If 1, adds a flop stage to the output
) (
    //All signals are duplicated, once per port
    input   logic [1:0]                     clk,
    input   logic [1:0] [ADDR_WIDTH - 1:0]  addr,
    input   logic [1:0]                     re,
    output  logic [1:0] [63:0]              rdata,
    input   logic [1:0]                     we,
    input   logic [1:0] [63:0]              wdata,
    input   logic [1:0] [7:0]               wbmask
);

localparam ADDR_WIDTH = $clog2(DEPTH);

logic [7:0] [7:0] sram [DEPTH - 1:0];
logic [1:0] [63:0] rdata_internal;

//Note: It is misleading, but when mapped to SRAM blocks
//by Quartus, the addr, wdata, we, re, wbmask, etc. are latched on
//the positive edges. The read outputs actually happen
//combinationally, even though it looks like there is only an output register in the RTL
//Check out the chip planner to see what I mean (or check out the ASCII art
//at the top of the file)

generate
    genvar i;

    //We also can't do this as a loop either, else Quartus fails to infer SRAM
    //and we get multiple-driver errors in synthesis (neither a loop for the
    //port nor for the wbmask)
    `define intel_fpga_sram_64_wbmask(port, the_byte) \
        if (wbmask[port][the_byte]) begin \
            sram[addr[port]][the_byte] <= wdata[port][the_byte * 8+:8]; \
        end
    `define intel_fpga_sram_64_port(port) \
        always_ff @(posedge clk[port]) begin \
            if (we[port]) begin \
                `intel_fpga_sram_64_wbmask(port, 0) \
                `intel_fpga_sram_64_wbmask(port, 1) \
                `intel_fpga_sram_64_wbmask(port, 2) \
                `intel_fpga_sram_64_wbmask(port, 3) \
                `intel_fpga_sram_64_wbmask(port, 4) \
                `intel_fpga_sram_64_wbmask(port, 5) \
                `intel_fpga_sram_64_wbmask(port, 6) \
                `intel_fpga_sram_64_wbmask(port, 7) \
            end \
            \
            if (re[port]) begin \
                rdata_internal[port] <= sram[addr[port]]; \
            end \
        end
    `intel_fpga_sram_64_port(0)
    `intel_fpga_sram_64_port(1)

    //Optionally add a flop stage to the output
    if (OUTPUT_REGISTER) begin
        for (i = 0; i < 2; ++i) begin : output_register
            always_ff @(posedge clk[i]) begin
                rdata[i] <= rdata_internal[i];
            end
        end : output_register
    end else begin
        assign rdata = rdata_internal;
    end
endgenerate

//TODO more variants here as needed

endmodule : intel_fpga_sram_64
