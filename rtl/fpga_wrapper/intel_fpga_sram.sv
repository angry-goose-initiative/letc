/*
 * File:    intel_fpga_sram.sv
 * Brief:   Inferred SRAM for Intel FPGAs
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * Designed with the limitations of Intel FPGAs in mind, discussed at:
 * https://www.intel.com/content/www/us/en/docs/programmable/683082/23-1/use-synchronous-memory-blocks.html
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
 * NOTE: Intel FPGA memories have a 1-cycle latency for both reads and writes.
 * The read output is registered, but inputs are unreigstered, so you may want
 * to add a flop stage yourself to help with timing if needed.
*/

module intel_fpga_sram #(
    parameter   WORDS               = 65536,
    parameter   DATA_WIDTH          = 8,
    localparam  ADDR_WIDTH          = $clog2(WORDS),
    localparam  WMASK_WIDTH         = (DATA_WIDTH / 8) + ((DATA_WIDTH % 8) ? 1 : 0),
    localparam  INTERNAL_DATA_WIDTH = WMASK_WIDTH * 8
) (
    //All signals are duplicated, once per port
    input   logic [1:0]                             clk,
    input   logic [1:0] [ADDR_WIDTH - 1:0]          addr,
    output  logic [1:0] [DATA_WIDTH - 1:0]          rdata,
    input   logic [1:0] [DATA_WIDTH - 1:0]          wdata,
    input   logic [1:0] [WMASK_WIDTH - 1:0]         wmask,
    input   logic [1:0]                             we
);

logic [WMASK_WIDTH - 1:0] [7:0] sram [WORDS - 1:0];

for (genvar i = 0; i < 2; ++i) begin: ports
    always_ff @(posedge clk[i]) begin
        //SRAM writes
        if (we[i]) begin
            for (int j = 0; j < WMASK_WIDTH; ++j) begin
                if (wmask[i][j]) begin
                    sram[addr[i]][j * 8 +: 8] <= wdata[i][j * 8 +: 8];
                end
            end
        end

        //SRAM reads
        rdata[i] <= sram[addr[i]][DATA_WIDTH - 1:0];
    end
end : ports

endmodule
