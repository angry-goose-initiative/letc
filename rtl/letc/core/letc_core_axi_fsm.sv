/*
 * File:    letc_core_axi_fsm.sv
 * Brief:   TODO
 *
 * Copyright:
 *  Copyright (C) 2024 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_axi_fsm
    import letc_pkg::*;
    import letc_core_pkg::*;
#(
    parameter NUM_REQUESTERS    = 3,//MMU, instruction cache, and data cache
    parameter AXI_ID            = 0
) (
    //Clock and reset
    input logic i_clk,
    input logic i_rst_n,

    //Core IO
    axi_if.manager axi,

    //Internal Core Connections
    //TODO probably make this into an interface (LIMP)
    input   logic   [NUM_REQUESTERS-1:0]    i_valid,
    output  logic   [NUM_REQUESTERS-1:0]    o_ready,
    input   logic   [NUM_REQUESTERS-1:0]    i_wen_nren,//Write enable and not read enable
    input   size_e  [NUM_REQUESTERS-1:0]    i_size,
    input   paddr_t [NUM_REQUESTERS-1:0]    i_addr,
    output  word_t  [NUM_REQUESTERS-1:0]    o_rdata,
    input   word_t  [NUM_REQUESTERS-1:0]    i_wdata
    //TODO fault signal if unaligned, AXI errors, etc
);

//TODO in future this can be made much more efficient by allowing reads and writes simulataneously
//That change, and also adding more AXI ports, could be made invisible to the requesters

/* ------------------------------------------------------------------------------------------------
 * Internal Signals
 * --------------------------------------------------------------------------------------------- */

logic   selected_wen_nren;
size_e  selected_size;
paddr_t selected_addr;
word_t  selected_wdata;

/* ------------------------------------------------------------------------------------------------
 * Arbiter
 * --------------------------------------------------------------------------------------------- */

//TODO
always_comb begin
    //TEMPORARY
    selected_wen_nren = i_wen_nren[0];
    selected_size     = i_size[0];
    selected_addr     = i_addr[0];
    selected_wdata    = i_wdata[0];
end

/* ------------------------------------------------------------------------------------------------
 * AXI FSM and Dynamic Outputs
 * --------------------------------------------------------------------------------------------- */

//TODO

always_comb begin

    //Ensure addresses are aligned (we handle smaller accesses with the write strobe and muxing)
    axi.awaddr = {selected_addr[33:2], 2'b00};
    axi.araddr = {selected_addr[33:2], 2'b00};

    unique case(selected_size)
        BYTE: begin
            //Binary to one-hot
            unique case(selected_addr[1:0])
                2'b00: axi.wstrb = 4'b0001;
                2'b01: axi.wstrb = 4'b0010;
                2'b10: axi.wstrb = 4'b0100;
                2'b11: axi.wstrb = 4'b1000;
            endcase
        end
        HALFWORD:   axi.wstrb = selected_addr[1] ? 4'b1100 : 4'b0011;
        WORD:       axi.wstrb = 4'b1111;
    endcase
end

/* ------------------------------------------------------------------------------------------------
 * Fixed AXI Signals
 * --------------------------------------------------------------------------------------------- */

always_comb begin
    //LETC Core doesn't take advantage of multiple AXI IDs. Reduces design complexity.
    axi.awid    = (axi_pkg::IDWIDTH)'(AXI_ID);
    axi.wid     = (axi_pkg::IDWIDTH)'(AXI_ID);//Unused in AXI4, but we'll set it for completeness
    axi.bid     = (axi_pkg::IDWIDTH)'(AXI_ID);
    axi.arid    = (axi_pkg::IDWIDTH)'(AXI_ID);
    axi.rid     = (axi_pkg::IDWIDTH)'(AXI_ID);

    //LETC Core doesn't do bursts. Reduces design complexity and resource usage (adders, etc)
    axi.awlen   = '0;//Each transaction is 1 beat only
    axi.awburst = axi_pkg::AXI_BURST_FIXED;
    axi.arlen   = '0;//Each transaction is 1 beat only
    axi.arburst = axi_pkg::AXI_BURST_FIXED;

    //Accesses are always 32-bits so we can avoid narrow transfers
    //(we use write strobes to handle 8-bit and 16-bit writes)
    axi.awsize  = 3'b010;
    axi.arsize  = 3'b010;
end

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

//TODO

endmodule : letc_core_axi_fsm
