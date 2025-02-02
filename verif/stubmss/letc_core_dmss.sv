/*
 * File:    letc_core_dmss.sv
 * Brief:   Stubbed LETC Core Data Memory Subsystem
 *
 * Copyright:
 *  Copyright (C) 2025 Nick Chan
 *  Copyright (C) 2025 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
*/

module letc_core_dmss
    import riscv_pkg::*;
    import letc_pkg::*;
    import letc_core_pkg::*;
#(
    parameter int SIZE_BYTES = 64 * (1 << 20) // 64 MiB, like IRVE
) (
    input logic clk,
    input logic rst_n,

    letc_core_dmss_if.subsystem dmss_if
);

endmodule : letc_core_dmss
