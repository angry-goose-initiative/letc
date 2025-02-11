/*
 * File:    amd_bram.sv
 * Brief:   Inferred BRAM For AMD FPGAs (targeting Zynq)
 *
 * Copyright:
 *  Copyright (C) 2024-2025 John Jekel
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
 * See UG473: https://docs.amd.com/v/u/en-US/ug473_7Series_Memory_Resources
 *
 * Doesn't expose all features (ex. simulatenous writes on both ports, etc)
 * but should be good enough for most general purposes.
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module amd_bram #(
    //You can override the DEPTH and DWIDTH parameters to use more/less than a single BRAM
    //Up to DEPTH = 1024 and DWIDTH = 36 should fit into a single one
    parameter int       DEPTH           = 1024,
    parameter int       DWIDTH          = 32,//Write enables only supported if this is a multiple of 8

    //Highly recommended to keep this at 1
    parameter int       OUTPUT_FLOPS    = 1,

    //Output data register reset values
    parameter int       OUT_RDATA_RST_A = 0,
    parameter int       OUT_RDATA_RST_B = 0,

    //One-time FPGA-programming reset of BRAM contents
    parameter int       INIT            = 0,
    parameter string    INIT_FILE       = "init.vhex",

    localparam int      AWIDTH          = $clog2(DEPTH),
    localparam int      WEWIDTH         = (DWIDTH % 8) == 0 ? (DWIDTH / 8) : 1
) (
    //Read/Write Port (port A)
    input  logic                i_a_clk,
    input  logic [WEWIDTH-1:0]  i_a_we,
    //Whether to enable the SRAM control logic AFTER the address/wdata input register, and also whether to enable writing ***
    input  logic                i_a_en,//<-_/
    input  logic                i_a_out_en,//Whether to enable the output data register
    input  logic                i_a_out_rst,//Whether to reset the output data register to OUT_RDATA_RST_A
    input  logic [AWIDTH-1:0]   i_a_addr,
    input  logic [DWIDTH-1:0]   i_a_wdata,
    output logic [DWIDTH-1:0]   o_a_rdata,

    //Read-Only Port (port B)
    input  logic                i_b_clk,
    input  logic                i_b_en,//Whether to enable the SRAM control logic AFTER the address input register ***
    input  logic                i_b_out_en,//Whether to enable the output data register
    input  logic                i_b_out_rst,//Whether to reset the output data register to OUT_RDATA_RST_B
    input  logic [AWIDTH-1:0]   i_b_addr,
    output logic [DWIDTH-1:0]   o_b_rdata

    //*** So effectively this is a control over the "read address input
    //register" kinda sorta (technically it controls the SRAM output latch
    //before the optional output register so it has an equvalent effect)
    //Confused? Me too. Look at UG473.
);

logic [DWIDTH-1:0] bram [DEPTH-1:0];//Unpacked arrays are a bad style but necessary for inference

/* ------------------------------------------------------------------------------------------------
 * Read/Write Port (port A)
 * --------------------------------------------------------------------------------------------- */

//Reading
logic [DWIDTH-1:0] a_rdata;
always_ff @(posedge i_a_clk) begin
    if (i_a_en) begin
        a_rdata <= bram[i_a_addr];
    end
end

generate
if (OUTPUT_FLOPS == 1) begin : gen_output_flops
    always_ff @(posedge i_a_clk) begin
        if (i_a_out_rst) begin
            o_a_rdata <= OUT_RDATA_RST_A;
        end else begin
            if (i_a_out_en) begin
                o_a_rdata <= a_rdata;
            end
        end
    end
end : gen_output_flops
else begin : gen_no_output_flops
    assign o_a_rdata = a_rdata;
end : gen_no_output_flops
endgenerate

//Writing
generate
if (WEWIDTH == 1) begin : gen_no_byte_wes
    always_ff @(posedge i_a_clk) begin
        if (i_a_en) begin
            if (i_a_we[0]) begin
                bram[i_a_addr] <= i_a_wdata;
            end
        end
    end
end : gen_no_byte_wes
else begin : gen_byte_wes
    always_ff @(posedge i_a_clk) begin
        if (i_a_en) begin
            for (int ii = 0; ii < WEWIDTH; ++ii) begin
                if (i_a_we[ii]) begin
                    bram[i_a_addr][ii*8 +: 8] <= i_a_wdata[ii*8 +: 8];
                end
            end
        end
    end
end : gen_byte_wes
endgenerate

/* ------------------------------------------------------------------------------------------------
 * Read-Only Port (port B)
 * --------------------------------------------------------------------------------------------- */

//Reading
logic [DWIDTH-1:0] b_rdata;
always_ff @(posedge i_b_clk) begin
    if (i_b_en) begin
        b_rdata <= bram[i_b_addr];
    end
end

generate
if (OUTPUT_FLOPS == 1) begin : gen_output_flops
    always_ff @(posedge i_b_clk) begin
        if (i_b_out_rst) begin
            o_b_rdata <= OUT_RDATA_RST_B;
        end else begin
            if (i_b_out_en) begin
                o_b_rdata <= b_rdata;
            end
        end
    end
end : gen_output_flops
else begin : gen_no_output_flops
    assign o_b_rdata = b_rdata;
end : gen_no_output_flops
endgenerate

/* ------------------------------------------------------------------------------------------------
 * Initialization
 * --------------------------------------------------------------------------------------------- */

//This is the only circumstance in which initial blocks are acceptable: on FPGAs with inferred SRAM
generate
if (INIT == 1) begin : gen_init
    initial begin
        $readmemh(INIT_FILE, bram);
    end
end : gen_init
endgenerate

endmodule : amd_bram
