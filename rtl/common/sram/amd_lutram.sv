/*
 * File:    amd_lutram.sv
 * Brief:   Inferred LUTRAM For AMD FPGAs
 *
 * Copyright:
 *  Copyright (C) 2024 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * One cycle latency for writes. Combinational reads, so one cycle write-to-read latency.
 *
 * Less area efficient than BRAM, but more efficient than flops since we're using LUTs as SRAM.
 * You likely want to have a flop stage to ease timing near this module...
 *
 * This module infers a "simple dual-port RAM", so only one of each of the read and write ports.
 * More than this requires effectively duplicating the number of LUTs, so if you want that just
 * instanciate this module multiple times.
 *
 * Some byte widths may be more optimal than others (ex multiple of DWIDTH)
 * Unlike amd_bram_bes.sv though, bytes aren't restricted to multiples of 8 or 9 bits
 *
 * If you want to be even more efficient, tie the i_waddr and i_raddr ports together if you only
 * need a single ported SRAM. Even more efficient if you don't use the byte enables (tie i_wben to '1)
 *
 * See https://docs.amd.com/r/2023.1-English/ug953-vivado-7series-libraries/RAM32M
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module amd_lutram #(
    parameter int       DEPTH           = 1024,
    parameter int       DWIDTH          = 32,
    parameter int       BWIDTH          = 8,
    parameter int       INIT            = 0,
    parameter string    INIT_FILE       = "init.vhex",

    localparam int      AWIDTH          = $clog2(DEPTH),
    localparam int      BEWIDTH         = (DWIDTH / BWIDTH) + (((DWIDTH % BWIDTH) != 0) ? 1 : 0)
) (
    //Write Port
    input  logic                i_wclk,
    input  logic                i_wen,
    input  logic [AWIDTH-1:0]   i_waddr,
    input  logic [BEWIDTH-1:0]  i_wben,
    input  logic [DWIDTH-1:0]   i_wdata,

    //Read Port (Combinational)
    input  logic [AWIDTH-1:0]   i_raddr,
    output logic [DWIDTH-1:0]   o_rdata
);

localparam ACTUAL_DWIDTH = BEWIDTH * BWIDTH;

logic [ACTUAL_DWIDTH-1:0] lutram [DEPTH-1:0];//Unpacked arrays are a bad style but necessary for inference

/* ------------------------------------------------------------------------------------------------
 * Write Port
 * --------------------------------------------------------------------------------------------- */

logic [ACTUAL_DWIDTH-1:0] padded_wdata;
assign padded_wdata = (ACTUAL_DWIDTH)'(i_wdata);

always_ff @(posedge i_wclk) begin
    if (i_wen) begin
        for (int ii = 0; ii < BEWIDTH; ++ii) begin
            if (i_wben[ii]) begin
                lutram[i_waddr][ii*BWIDTH +: BWIDTH] <= padded_wdata[ii*BWIDTH +: BWIDTH];
            end
        end
    end
end

/* ------------------------------------------------------------------------------------------------
 * Read Port
 * --------------------------------------------------------------------------------------------- */

always_comb begin
    o_rdata = lutram[i_raddr][DWIDTH-1:0];
end

/* ------------------------------------------------------------------------------------------------
 * Initialisation
 * --------------------------------------------------------------------------------------------- */

//This is the only circumstance in which initial blocks are acceptable: on FPGAs with inferred SRAM
generate if (INIT == 1) begin: g_READ_MEM
    initial begin
        $readmemh(INIT_FILE, lutram);
    end
end endgenerate

endmodule : amd_lutram
