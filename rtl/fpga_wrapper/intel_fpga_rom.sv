/*
 * File:    intel_fpga_rom.sv
 * Brief:   ROM wrapper around inferred Intel FPGA SRAM
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * NOTE: To initialize the ROM with default contents, use an initial block
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

module intel_fpga_rom #(
    parameter   DEPTH       = 65536,
    parameter   DATA_WIDTH  = 8
) (
    //All signals are duplicated, once per port
    input   logic [1:0]                     clk,
    input   logic [1:0] [ADDR_WIDTH - 1:0]  addr,
    output  logic [1:0] [DATA_WIDTH - 1:0]  rdata
);

localparam  ADDR_WIDTH  = $clog2(DEPTH);
localparam  WMASK_WIDTH = (DATA_WIDTH / 8) + ((DATA_WIDTH % 8) ? 1 : 0);

intel_fpga_sram #(
    .DEPTH          (DEPTH),
    .DATA_WIDTH     (DATA_WIDTH),
    .ADDR_WIDTH     (ADDR_WIDTH)
) intel_fpga_sram_inst (
    .*,
    .wdata          ('0),
    .wmask          ('0),
    .we             ('0)
);

endmodule
