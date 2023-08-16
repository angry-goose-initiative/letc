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
 * NOTE: To initialize the SRAM with default contents, use an initial block
 * from a testbench or outer FPGA wrapper (which is okayish practice for FPGAs). Alternatively, there are
 * likely options in the Quartus IDE.
*/

module intel_fpga_sram #(
    parameter WORDS         = 65536,
    parameter ADDR_WIDTH    = 8,
    parameter DATA_WIDTH    = 8,
) (
    input  logic [1:0] clk,//One clock per SRAM 
    
    //TODO ports

);

logic [DATA_WIDTH - 1:0] sram [WORDS - 1:0];

endmodule
