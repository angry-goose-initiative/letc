/*
 * File:    core_s2_reg_file.sv
 * Brief:   The register file
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

module core_s2_reg_file
    import letc_pkg::*;
    import core_pkg::*;
(
    input   logic       clk,
    input   logic       rst_n,

    //rd write port
    input   reg_index_t rd_index,
    input   word_t      rd_wd,
    input   logic       rd_we,

    //rs1 read port
    input   reg_index_t rs1_index,
    output  word_t      rs1_val,
    
    //rs2 read port
    input   reg_index_t rs2_index,
    output  word_t      rs2_val
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
            if (rd_we && (rd_index == reg_index[4:0])) begin
                register[reg_index] <= rd_wd;
            end
        end : rd_write
    end
end : rd_write_port

//rs1 read port
assign rs1_val = (rs1_index == 5'd0) ? '0 : register[rs1_index];

//rs2 read port
assign rs2_val = (rs2_index == 5'd0) ? '0 : register[rs2_index];

endmodule : core_s2_reg_file
