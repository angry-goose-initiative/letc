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
    //Clock
    input logic clk,

    //rd Write Port
    input   reg_idx_t   rd_idx,
    input   word_t      rd_val,
    input   logic       rd_wen,

    //rs1 Read Port
    input   reg_idx_t   rs1_idx,
    output  word_t      rs1_val,

    //rs2 Read Port
    input   reg_idx_t   rs2_idx,
    output  word_t      rs2_val
);

/* ------------------------------------------------------------------------------------------------
 * Register State
 * --------------------------------------------------------------------------------------------- */

//Unpacked only so we infer RAM32M (more efficient than raw LUTs, but not as efficient as BRAM)
//Before this (and the changes below) we consumed ~600 LUTS, now we consume ~100
//word_t [31:1] registers;
word_t registers [31:1];

//RAM32M is really fricking cool! We use the LUT SRAM itself as the asynchrenous-read RAM!
//This doesn't actually infer any slice registers at all!

/* ------------------------------------------------------------------------------------------------
 * rd Write Port
 * --------------------------------------------------------------------------------------------- */

//Decoder (5-to-32, except for 0)
//More explicit but prevents RAM32M inference
/*
logic [31:1] register_wen;
always_comb begin
    for (int ii = 1; ii < 32; ++ii) begin
        register_wen[ii] = (rd_idx == ii) & rd_wen;
    end
end
*/

//Write Logic
always_ff @(posedge clk) begin
    //No resets needed, so don't include them to save resources

    //More explicit but prevents RAM32M inference
    /*
    for (int ii = 1; ii < 32; ++ii) begin
        if (register_wen[ii]) begin
            registers[ii] <= rd_val;
        end
    end
    */

    if (rd_wen & (rd_idx != '0)) begin
        registers[rd_idx] <= rd_val;
    end
end

/* ------------------------------------------------------------------------------------------------
 * rs1 and rs2 Read Ports
 * --------------------------------------------------------------------------------------------- */

//Muxes and bypass logic
always_comb begin
    //rs1
    if (rs1_idx == '0) begin//x0
        rs1_val = '0;
    end else if ((rs1_idx == rd_idx) & rd_wen) begin//Need to bypass write -> read
        rs1_val = rd_val;
    end else begin
        rs1_val = registers[rs1_idx];
    end

    //rs2
    if (rs2_idx == '0) begin//x0
        rs2_val = '0;
    end else if ((rs2_idx == rd_idx) & rd_wen) begin//Need to bypass write -> read
        rs2_val = rd_val;
    end else begin
        rs2_val = registers[rs2_idx];
    end
end

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

//TODO

`endif //SIMULATION

endmodule : letc_core_rf
