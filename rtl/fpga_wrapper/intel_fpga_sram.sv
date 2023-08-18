/*
 * File:    intel_fpga_sram.sv
 * Brief:   Inferred SRAM for Intel FPGAs
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
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
 * NOTE: Intel FPGA memories have a 1-cycle latency for both reads and writes.
 * The read output is registered, but inputs are unreigstered, so you may want
 * to add a flop stage yourself to help with timing if needed.
 *
 * NOTE: In terms of the interations between reads and writes:
 * - We always read the old data written to the SRAM, even on the same port
 * - Multiple simultaneous writes to the same address are undefined
*/

//FIXME avoid multiple drivers in synthesis like the example module added to
//the end of this file

module intel_fpga_sram #(
    parameter   DEPTH               = 65536,
    parameter   DATA_WIDTH          = 8
) (
    //All signals are duplicated, once per port
    input   logic [1:0]                     clk,
    input   logic [1:0] [ADDR_WIDTH - 1:0]  addr,
    output  logic [1:0] [DATA_WIDTH - 1:0]  rdata,
    input   logic [1:0] [DATA_WIDTH - 1:0]  wdata,
    input   logic [1:0] [WMASK_WIDTH - 1:0] wmask,
    input   logic [1:0]                     we
);

localparam  ADDR_WIDTH          = $clog2(DEPTH);
localparam  WMASK_WIDTH         = (DATA_WIDTH / 8) + ((DATA_WIDTH % 8) ? 1 : 0);
localparam  INTERNAL_DATA_WIDTH = WMASK_WIDTH * 8;

logic [INTERNAL_DATA_WIDTH - 1:0] sram [DEPTH - 1:0] /* synthesis ramstyle = M9K */;

generate//Needed because of Quartus (otherwise this would be optional in SystemVerilog)
    genvar i;//Also needed because of Quartus

    for (i = 0; i < 2; ++i) begin : ports//Also needed because of Quartus
    //for (genvar i = 0; i < 2; ++i) begin : ports//Quartus doesn't like this
        always_ff @(posedge clk[i]) begin
            //We place reads before

            //SRAM reads
            rdata[i] <= sram[addr[i]][DATA_WIDTH - 1:0];

            //SRAM writes
            if (we[i]) begin
                /*
                for (int j = 0; j < WMASK_WIDTH; ++j) begin
                    if (wmask[i][j]) begin
                        //This would normally be bad practice, but to avoid multiple drivers in synthesis, we use blocking assignments
                        //Recommended over at: https://www.intel.com/content/www/us/en/docs/programmable/683082/23-1/true-dual-port-synchronous-ram.html
                        sram[addr[i]][j * 8 +: 8] <= wdata[i][j * 8 +: 8];
                        //sram[addr[i]][j * 8 +: 8] = wdata[i][j * 8 +: 8];
                    end
                end
                */
                if (addr[0] == addr[1]) begin
                    if (i == 0) begin
                        sram[addr[i]] <= 'x;
                    end
                end else begin
                    sram[addr[i]] <= wdata[i];//TESTING
                end
            end
        end
    end : ports
endgenerate//Needed because of Quartus (otherwise this would be optional in SystemVerilog)

endmodule

// Quartus Prime Verilog Template
// True Dual Port RAM with single clock
//
// Read-during-write behavior is undefined for mixed ports 
// and "new data" on the same port

module true_dual_port_ram_single_clock
#(parameter DATA_WIDTH=8, parameter ADDR_WIDTH=6)
(
	input [(DATA_WIDTH-1):0] data_a, data_b,
	input [(ADDR_WIDTH-1):0] addr_a, addr_b,
	input we_a, we_b, clk_a, clk_b,
	output reg [(DATA_WIDTH-1):0] q_a, q_b
);

	// Declare the RAM variable
	reg [DATA_WIDTH-1:0] ram[2**ADDR_WIDTH-1:0];

	// Port A 
	always @ (posedge clk_a)
	begin
		if (we_a) 
		begin
			ram[addr_a] = data_a;
		end
		q_a <= ram[addr_a];
	end 

	// Port B 
	always @ (posedge clk_b)
	begin
		if (we_b) 
		begin
			ram[addr_b] = data_b;
		end
		q_b <= ram[addr_b];
	end

endmodule
