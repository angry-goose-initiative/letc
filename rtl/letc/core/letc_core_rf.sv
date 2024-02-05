/*
 * File:    letc_core_rf.sv
 * Brief:   LETC Core Register File
 *
 * Copyright:
 *  Copyright (C) 2023-2024 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * This is perhaps more explicit than it needs to be (ex. explicity showing
 * the decoder instead of just indexing with the vector), but that's fine,
 * it's good practice for keeping in mind what's actually going on.
 *
 * Note that there is internal bypass logic for effective 0-cycle writes
 * (forwarding writes to reads in the same cycle)
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_rf
    import letc_pkg::*;
    import letc_core_pkg::*;
(
    //Clock and reset
    input logic i_clk,
    input logic i_rst_n,

    //rd Write Port
    input   reg_idx_t   i_rd_idx,
    input   word_t      i_rd_wdata,
    input   logic       i_rd_wen,

    //rs1 Read Port
    input   reg_idx_t   i_rs1_idx,
    output  word_t      o_rs1_rdata,
    
    //rs2 Read Port
    input   reg_idx_t   i_rs2_idx,
    output  word_t      o_rs2_rdata
);

/* ------------------------------------------------------------------------------------------------
 * Register State
 * --------------------------------------------------------------------------------------------- */

word_t [31:1] registers;

/* ------------------------------------------------------------------------------------------------
 * rd Write Port
 * --------------------------------------------------------------------------------------------- */

//Decoder (5-to-32, except for 0)
logic [31:1] register_wen;
always_comb begin
    for (int ii = 1; ii < 32; ++ii) begin
        register_wen[ii] = (i_rd_idx == ii) & i_rd_wen;
    end
end

//Write Logic
always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (~i_rst_n) begin
        //Reset all (except x0) to garbage values to aid debugging
        for (int ii = 1; ii < 32; ++ii) begin
            registers[ii] <= 32'hDEADBEEF;
        end
    end else begin
        for (int ii = 1; ii < 32; ++ii) begin
            if (register_wen[ii]) begin
                registers[ii] <= i_rd_wdata;
            end
        end
    end
end

/* ------------------------------------------------------------------------------------------------
 * rs1 and rs2 Read Ports
 * --------------------------------------------------------------------------------------------- */

//Muxes and bypass logic
always_comb begin
    //rs1
    if (i_rs1_idx == '0) begin//x0
        o_rs1_rdata = '0;
    end else if ((i_rs1_idx == i_rd_idx) & i_rd_wen) begin//Need to bypass write -> read
        o_rs1_rdata = i_rd_wdata;
    end else begin
        o_rs1_rdata = registers[i_rs1_idx];
    end

    //rs2
    if (i_rs2_idx == '0) begin//x0
        o_rs2_rdata = '0;
    end else if ((i_rs2_idx == i_rd_idx) & i_rd_wen) begin//Need to bypass write -> read
        o_rs2_rdata = i_rd_wdata;
    end else begin
        o_rs2_rdata = registers[i_rs2_idx];
    end
end

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

//TODO

`endif

endmodule : letc_core_rf