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

module core_reg_file
    import core_pkg::*;
(
    input clk,
    input rst_n,

    //rd write port
    input reg_index_t rd_index,
    input word_t      rd,
    input logic       rd_write_enable,

    //rs1 read port
    input reg_index_t rs1_index,
    output word_t     rs1,
    
    //rs2 read port
    input reg_index_t rs2_index,
    output word_t     rs2
);

//The registers
word_t [31:1] register;//DON'T USE UNPACKED (we aren't inferring FPGA SRAMs here, so it would be bad practice)

//rd write port
always_ff @(posedge clk, negedge rst_n) begin : rd_write_port
    if (!rst_n) begin
        //Reset all except x0 to garbage values to aid debugging
        for (int reg_index = 1; reg_index < 32; ++reg_index) begin : reset
            register[reg_index] <= 32'hDEADBEEF;
        end : reset
    end else begin//posedge clk
        for (int reg_index = 1; reg_index < 32; ++reg_index) begin : rd_write
            if (rd_write_enable && (reg_index[4:0] == rd_index)) begin
                register[reg_index] <= rd;
            end
        end : rd_write
    end
end : rd_write_port

//rs1 read port
assign rs1 = (rs1_index == 5'd0) ? '0 : register[rs1_index];

//rs2 read port
assign rs2 = (rs2_index == 5'd0) ? '0 : register[rs2_index];

endmodule : core_reg_file
