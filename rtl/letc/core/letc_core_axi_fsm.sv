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

logic   selected_valid;
logic   selected_wen_nren;
size_e  selected_size;
paddr_t selected_addr;
word_t  selected_wdata;

logic   ready_to_requester;

/* ------------------------------------------------------------------------------------------------
 * Arbiter and Switching
 * --------------------------------------------------------------------------------------------- */

logic [$clog2(NUM_REQUESTERS)-1:0] selected_requester;

always_comb begin
    //Priority decoder; priority increases as requester number decreases
    //FIXME we need to have state so one requestor doesn't steal from another
    selected_requester = '0;
    for (int ii = NUM_REQUESTERS - 1; ii > 0; --ii) begin
        if (i_valid[ii]) begin
            selected_requester = ii;
        end
    end

    selected_valid = |i_valid;//More efficient than a mux

    //Muxes
    selected_wen_nren = i_wen_nren[selected_requester];
    selected_size     = i_size[selected_requester];
    selected_addr     = i_addr[selected_requester];
    selected_wdata    = i_wdata[selected_requester];

    //Demux ready signal to the selected requester
    o_ready = '0;
    o_ready[selected_requester] = ready_to_requester;
end

/* ------------------------------------------------------------------------------------------------
 * FSM Transition Logic
 * --------------------------------------------------------------------------------------------- */

//Mealy FSM
typedef enum logic [2:0] {
    IDLE,
    SEND_RADDR,
    GET_RDATA,
    SEND_WADDR,
    SEND_WDATA
} state_e;

state_e state, next_state;

always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (~i_rst_n) begin
        state <= IDLE;
    end else begin
        state <= next_state;
    end
end

always_comb begin
    unique case (state)
        IDLE: begin
            if (selected_valid) begin
                if (selected_wen_nren) begin//Write
                    if (axi.aw_transfer_complete() && axi.w_transfer_complete()) begin
                        next_state = IDLE;//Done in one cycle!
                    end else if (axi.aw_transfer_complete()) begin
                        next_state = SEND_WDATA;//Still need to send data
                    end else if (axi.w_transfer_complete()) begin
                        next_state = SEND_WADDR;//Still need to send the address
                    end else begin
                        next_state = IDLE;//Waiting on both
                    end
                end else begin//Read
                    if (axi.ar_transfer_complete() && axi.r_transfer_complete()) begin
                        next_state = IDLE;//Done in one cycle!
                    end else if (axi.ar_transfer_complete()) begin
                        next_state = GET_RDATA;//Still need to get the data
                    end else if (axi.r_transfer_complete()) begin
                        next_state = SEND_RADDR;//Still need to send the address
                    end else begin
                        next_state = IDLE;//Waiting on both
                    end
                end
            end else begin
                next_state = IDLE;
            end
        end
        SEND_RADDR: begin
            if (axi.ar_transfer_complete()) begin
                next_state = IDLE;
            end else begin
                next_state = SEND_RADDR;
            end
        end
        GET_RDATA: begin
            if (axi.r_transfer_complete()) begin
                next_state = IDLE;
            end else begin
                next_state = GET_RDATA;
            end
        end
        SEND_WADDR: begin
            if (axi.aw_transfer_complete()) begin
                next_state = IDLE;
            end else begin
                next_state = SEND_WADDR;
            end
        end
        SEND_WDATA: begin
            if (axi.w_transfer_complete()) begin
                next_state = IDLE;
            end else begin
                next_state = SEND_WDATA;
            end
        end
        //TODO extra state for get write response?
    endcase
end

/* ------------------------------------------------------------------------------------------------
 * FSM Outputs
 * --------------------------------------------------------------------------------------------- */

//TODO also set ready_to_requester based on AXI ready signals

always_comb begin
    axi.arvalid = 1'b0;
    axi.rready  = 1'b0;
    axi.awvalid = 1'b0;
    axi.wvalid  = 1'b0;

    if (selected_valid) begin
        unique case (state)
            IDLE: begin
                if (selected_wen_nren) begin//Write
                    axi.awvalid = 1'b1;
                    axi.wvalid  = 1'b1;
                end else begin//Read
                    axi.arvalid = 1'b1;
                    axi.rready  = 1'b1;
                end
            end
            SEND_RADDR: begin
                axi.arvalid = 1'b1;
            end
            GET_RDATA: begin
                axi.rready  = 1'b1;
            end
            SEND_WADDR: begin
                axi.awvalid = 1'b1;
            end
            SEND_WDATA: begin
                axi.wvalid  = 1'b1;
            end
            //TODO extra state for get write response?
        endcase
    end
end

//TODO need to buffer read data on entry into SEND_RADDR state; ACTUALLY nvm it can't come until the data comes first

always_comb begin
    //Ensure addresses are aligned (we handle smaller accesses with the write strobe and muxing)
    axi.araddr = {selected_addr[33:2], 2'b00};
    axi.awaddr = {selected_addr[33:2], 2'b00};

    //Set write strobe properly
    unique case (selected_size)
        SIZE_BYTE: begin
            //Binary to one-hot
            unique case (selected_addr[1:0])
                2'b00: axi.wstrb = 4'b0001;
                2'b01: axi.wstrb = 4'b0010;
                2'b10: axi.wstrb = 4'b0100;
                2'b11: axi.wstrb = 4'b1000;
            endcase
        end
        SIZE_HALFWORD:  axi.wstrb = selected_addr[1] ? 4'b1100 : 4'b0011;
        SIZE_WORD:      axi.wstrb = 4'b1111;
    endcase
end

word_t processed_rdata;
always_comb begin
    //Extract the data we care about from the 32-bit AXI data (bunch of muxes)
    unique case (selected_size)
        SIZE_BYTE: begin
            unique case (selected_addr[1:0])
                2'b00: processed_rdata = axi.rdata[7:0];
                2'b01: processed_rdata = axi.rdata[15:8];
                2'b10: processed_rdata = axi.rdata[23:16];
                2'b11: processed_rdata = axi.rdata[31:24];
            endcase
        end
        SIZE_HALFWORD:  processed_rdata = selected_addr[1] ? axi.rdata[31:16] : axi.rdata[15:0];
        SIZE_WORD:      processed_rdata = axi.rdata;
    endcase

    //Connect the data to all requesters
    for (int ii = 0; ii < NUM_REQUESTERS; ++ii) begin
        o_rdata[ii] = processed_rdata;
    end
end

word_t processed_wdata;
always_comb begin
    //Send the data we care about in the right format for AXI data (bunch of muxes)
    //We replicate the data so no matter the sub-word offset, the data is in the right place
    unique case (selected_size)
        SIZE_BYTE:      processed_wdata = {4{selected_wdata[7:0]}};
        SIZE_HALFWORD:  processed_wdata = {2{selected_wdata[15:0]}};
        SIZE_WORD:      processed_wdata = selected_wdata;
    endcase

    axi.wdata = processed_wdata;
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

    //For now, we ignore the response in write responses. We consume the response right away so we
    //can let the right requestor know the write finished, and this never takes more than one cycle
    axi.bready = 1'b1;
end

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

//TODO

endmodule : letc_core_axi_fsm
