/*
 * File:    core_s2_reg_file.sv
 * Brief:   The register file
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * This is perhaps more explicit than it needs to be (ex. explicity showing
 * the decoder instead of just indexing with the vector), but that's fine,
 * it's good practice for keeping in mind what's actually going on.
 *
*/

`ifdef IMPORTS_IN_MODULE_SCOPE_UNSUPPORTED
import letc_pkg::*;
import core_pkg::*;
`endif

module core_s2_reg_file
`ifndef IMPORTS_IN_MODULE_SCOPE_UNSUPPORTED
    import letc_pkg::*;
    import core_pkg::*;
`endif
(
    input   logic       clk,
    input   logic       rst_n,

    //rd write port
    input   reg_idx_t   rd_idx,
    input   word_t      rd_wd,
    input   logic       rd_we,

    //rs1 read port
    input   reg_idx_t   rs1_idx,
    output  word_t      rs1_ff,
    
    //rs2 read port
    input   reg_idx_t   rs2_idx,
    output  word_t      rs2_ff
);

//The registers
word_t register_ff [31:1];

//rd_write_port decoder (5-to-32, except for 0)
logic [31:1] register_we;
always_comb begin : rd_write_port_decoder
    for (int reg_idx = 1; reg_idx < 32; ++reg_idx) begin
        if (rd_idx == reg_idx[4:0]) begin
            register_we[reg_idx] = rd_we;
        end else begin
            register_we[reg_idx] = 1'b0;
        end
    end
end : rd_write_port_decoder

//rd write port
always_ff @(posedge clk, negedge rst_n) begin : rd_write_port
    if (!rst_n) begin
        //Reset all except x0 to garbage values to aid debugging
        for (int reg_idx = 1; reg_idx < 32; ++reg_idx) begin : register_reset
            register_ff[reg_idx] <= 32'hDEADBEEF;
        end : register_reset
    end else begin//posedge clk
        for (int reg_idx = 1; reg_idx < 32; ++reg_idx) begin : rd_write
            if (register_we[reg_idx]) begin
                register_ff[reg_idx] <= rd_wd;
            end
        end : rd_write
    end
end : rd_write_port

//rs1 read port (32-to-1 mux)
assign rs1_ff = (rs1_idx == 5'd0) ? '0 : register_ff[rs1_idx];

//rs2 read port (32-to-1 mux)
assign rs2_ff = (rs2_idx == 5'd0) ? '0 : register_ff[rs2_idx];

endmodule : core_s2_reg_file
