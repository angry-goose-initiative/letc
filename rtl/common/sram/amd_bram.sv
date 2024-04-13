/*
 * File:    amd_bram.sv
 * Brief:   Inferred BRAM For AMD FPGAs
 *
 * Copyright:
 *  Copyright (C) 2024 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * One cycle latency for writes.
 *
 * Two cycle latency for reads due to address/control registers + output flops.
 * You can disable the output flops by setting OUTPUT_FLOPS to 0 but this may
 * have negative timing implications. It is preferable to keep it as 1 even if
 * you have flops afterwards in your design since this makes it more likely to
 * use the BRAM's output registers rather than registers in another slice somewhere.
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module amd_bram #(
    parameter int       DEPTH           = 1024,
    parameter int       DWIDTH          = 32,
    parameter int       OUTPUT_FLOPS    = 1,//Highly recommended to keep this at 1
    parameter int       INIT            = 0,
    parameter string    INIT_FILE       = "init.vhex",

    localparam int      AWIDTH          = $clog2(DEPTH)
) (
    //Write Port
    input  logic                i_wclk,
    input  logic                i_wen,
    input  logic [AWIDTH-1:0]   i_waddr,
    input  logic [DWIDTH-1:0]   i_wdata,

    //Read Port
    input  logic                i_rclk,
    input  logic                i_ren,
    input  logic [AWIDTH-1:0]   i_raddr,
    output logic [DWIDTH-1:0]   o_rdata
);

logic [DWIDTH-1:0] bram [DEPTH-1:0];//Unpacked arrays are a bad style but necessary for inference

/* ------------------------------------------------------------------------------------------------
 * Write Port
 * --------------------------------------------------------------------------------------------- */

always_ff @(posedge i_wclk) begin
    if (i_wen) begin
        bram[i_waddr] <= i_wdata;
    end
end

/* ------------------------------------------------------------------------------------------------
 * Read Port
 * --------------------------------------------------------------------------------------------- */

logic [DWIDTH-1:0] rdata;

always_ff @(posedge i_rclk) begin
    if (i_ren) begin
        rdata <= bram[i_raddr];
    end
end

generate if (OUTPUT_FLOPS == 1) begin : g_FLOP_OUTPUT
    always_ff @(posedge i_rclk) begin
        o_rdata <= rdata;
    end
end else begin
    assign o_rdata = rdata;
end endgenerate

/* ------------------------------------------------------------------------------------------------
 * Initialisation
 * --------------------------------------------------------------------------------------------- */

//This is the only circumstance in which initial blocks are acceptable: on FPGAs with inferred SRAM
generate if (INIT == 1) begin : g_READ_MEM
    initial begin
        $readmemh(INIT_FILE, bram);
    end
end endgenerate

endmodule : amd_bram
