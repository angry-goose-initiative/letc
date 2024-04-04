/*
 * File:    letc_core_axi_fsm.sv
 * Brief:   AXI Manager FSM and logic for LETC Core
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
    parameter NUM_REQUESTORS    = 3,//MMU, caches, and uncached access
    parameter AXI_ID            = 0
) (
    //Clock and reset
    input logic i_clk,
    input logic i_rst_n,

    //Core IO
    axi_if.manager axi,

    //Internal Core Connections
    //Sadly this needs to be unpacked since these are interfaces. But we've
    //ensured this is synthesizable
    letc_core_limp_if.servicer limp [NUM_REQUESTORS-1:0]
);

//TODO in future this can be made much more efficient by allowing reads and writes simulataneously
//That change, and also adding more AXI ports, could be made invisible to the requestors

/* ------------------------------------------------------------------------------------------------
 * "Breaking Out" LIMP Signals
 * --------------------------------------------------------------------------------------------- */

//So they're easier to work with and we can index into them, which is useful for arbitration
logic   [NUM_REQUESTORS-1:0]    limp_valid;
logic   [NUM_REQUESTORS-1:0]    limp_ready;
logic   [NUM_REQUESTORS-1:0]    limp_wen_nren;//Write enable and not read enable
size_e  [NUM_REQUESTORS-1:0]    limp_size;
paddr_t [NUM_REQUESTORS-1:0]    limp_addr;
word_t  [NUM_REQUESTORS-1:0]    limp_rdata;
word_t  [NUM_REQUESTORS-1:0]    limp_wdata;

generate
for (genvar ii = 0; ii < NUM_REQUESTORS; ++ii) begin : g_breakout_limp
    always_comb begin
        limp_valid[ii]      = limp[ii].valid;
        limp[ii].ready      = limp_ready[ii];
        limp_wen_nren[ii]   = limp[ii].wen_nren;
        limp_size[ii]       = limp[ii].size;
        limp_addr[ii]       = limp[ii].addr;
        limp[ii].rdata      = limp_rdata[ii];
        limp_wdata[ii]      = limp[ii].wdata;
    end
end : g_breakout_limp
endgenerate

/* ------------------------------------------------------------------------------------------------
 * Internal Signals
 * --------------------------------------------------------------------------------------------- */

logic   selected_valid;
logic   selected_wen_nren;
size_e  selected_size;
paddr_t selected_addr;
word_t  selected_wdata;

logic   ready_to_requestor;

/* ------------------------------------------------------------------------------------------------
 * Arbiter and Switching
 * --------------------------------------------------------------------------------------------- */

logic [$clog2(NUM_REQUESTORS)-1:0] selected_requestor;

always_comb begin
    //Priority decoder; priority increases as requestor number decreases
    //FIXME we need to have state so one requestor doesn't steal from another
    selected_requestor = '0;
    for (int ii = NUM_REQUESTORS - 1; ii > 0; --ii) begin
        if (limp_valid[ii]) begin
            selected_requestor = ii;
        end
    end

    selected_valid = |limp_valid;//More efficient than a mux

    //Muxes
    selected_wen_nren = limp_wen_nren[selected_requestor];
    selected_size     = limp_size[selected_requestor];
    selected_addr     = limp_addr[selected_requestor];
    selected_wdata    = limp_wdata[selected_requestor];

    //Demux ready signal to the selected requestor
    limp_ready = '0;
    limp_ready[selected_requestor] = ready_to_requestor;
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
    SEND_WDATA,
    GET_BRESP
} state_e;

state_e state, next_state;

always_ff @(posedge i_clk) begin
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
                        next_state = GET_BRESP;//Write done in one cycle! (Waiting on response now)
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
        GET_BRESP: begin
            if (axi.b_transfer_complete()) begin
                next_state = IDLE;
            end else begin
                next_state = GET_BRESP;
            end
        end
        default: next_state = IDLE;//This should never happen
    endcase
end

/* ------------------------------------------------------------------------------------------------
 * FSM Outputs
 * --------------------------------------------------------------------------------------------- */

always_comb begin
    axi.arvalid = 1'b0;
    axi.rready  = 1'b0;
    axi.awvalid = 1'b0;
    axi.wvalid  = 1'b0;
    //axi.bready  = 1'b0;//More efficient to just make this high all of the time as an optimization (the response must come at least one cycle later)
    ready_to_requestor = 1'b0;

    if (selected_valid) begin
        unique0 case (state)
            IDLE: begin
                if (selected_wen_nren) begin//Write
                    axi.awvalid = 1'b1;
                    axi.wvalid  = 1'b1;
                end else begin//Read
                    axi.arvalid = 1'b1;
                    axi.rready  = 1'b1;
                    ready_to_requestor = axi.ar_transfer_complete() && axi.r_transfer_complete();
                end
            end
            SEND_RADDR: begin
                axi.arvalid = 1'b1;
            end
            GET_RDATA: begin
                axi.rready  = 1'b1;
                ready_to_requestor = axi.r_transfer_complete();
            end
            SEND_WADDR: begin
                axi.awvalid = 1'b1;
            end
            SEND_WDATA: begin
                axi.wvalid  = 1'b1;
            end
            GET_BRESP: begin
                //axi.bready  = 1'b1;//More efficient to just make this high all of the time as an optimization (the response must come at least one cycle later)
                ready_to_requestor = axi.b_transfer_complete();
            end
        endcase
    end
end

always_comb begin
    //Ensure addresses are aligned (we handle smaller accesses with the write strobe and muxing)
    axi.araddr = {selected_addr[PADDR_WIDTH-1:2], 2'b00};
    axi.awaddr = {selected_addr[PADDR_WIDTH-1:2], 2'b00};

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
        default: axi.wstrb = 4'b0000;//This should never occur
    endcase
end

word_t processed_rdata;
always_comb begin
    //Extract the data we care about from the 32-bit AXI data (bunch of muxes)
    unique case (selected_size)
        SIZE_BYTE: begin
            unique case (selected_addr[1:0])
                2'b00: processed_rdata = {24'h0, axi.rdata[7:0]};
                2'b01: processed_rdata = {24'h0, axi.rdata[15:8]};
                2'b10: processed_rdata = {24'h0, axi.rdata[23:16]};
                2'b11: processed_rdata = {24'h0, axi.rdata[31:24]};
            endcase
        end
        SIZE_HALFWORD:  processed_rdata = selected_addr[1] ? {16'h0, axi.rdata[31:16]} : {16'h0, axi.rdata[15:0]};
        SIZE_WORD:      processed_rdata = axi.rdata;
        default: processed_rdata = 32'hDEADBEEF;//This should never occur
    endcase

    //Connect the data to all requestors
    for (int ii = 0; ii < NUM_REQUESTORS; ++ii) begin
        limp_rdata[ii] = processed_rdata;
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
        default: processed_wdata = 32'hDEADBEEF;//This should never occur
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
    axi.arid    = (axi_pkg::IDWIDTH)'(AXI_ID);

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
