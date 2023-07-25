/*
 * File:    reg_file.sv
 * Brief:   The register file
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

module reg_file (
    input clk,
    input rst_n,
    input logic [4:0] rs1,
    input logic [4:0] rs2
    // TODO other ports
);

logic [31:0] registers [31:1];

endmodule
