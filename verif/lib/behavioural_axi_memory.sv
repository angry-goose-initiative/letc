/*
 * File:    behavioural_axi_memory.sv
 * Brief:   TODO
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * Not intended to be synthesizable.
 *
 * TODO support bursts and fancy stuff like that
 *
*/

module behavioural_axi_memory
    import axi_pkg::*;
//TODO allow being init by a file as a parameter
//TODO allow configurable (perhaps even random) latency
(
    input global_s  axi_global,

    //This is a subordinate so the req is an input and the rsp is an output
    input req_s     req,
    output rsp_s    rsp
);

rsp_s rsp_output_reg;

//TODO allow configurable (perhaps even random) latency
always_comb begin
    rsp = rsp_output_reg;
    rsp.awready  = 1'b1;
    rsp.wready   = 1'b1;
    rsp.arready  = 1'b1;
end

//TODO support bursts and fancy stuff like that
logic aw_burst_attempted;
logic ar_burst_attempted;
assign aw_burst_attempted = aw_transfer_complete(req, rsp) && (req.awlen != 0);
assign ar_burst_attempted = ar_transfer_complete(req, rsp) && (req.arlen != 0);

logic irrecoverable_error;
always_ff @(posedge axi_global.aclk, negedge axi_global.aresetn) begin
    if (!axi_global.aresetn) begin
        irrecoverable_error <= 1'b0;
    end else begin
        if (!irrecoverable_error) begin
            if (aw_burst_attempted) begin
                irrecoverable_error <= 1'b1;
            end//TODO other conditions
        end
    end
end

//A write has completed
logic w_complete;

//AW channel logic
logic  aw_current_valid;
addr_t aw_current_addr;
size_t aw_current_size;
id_t   aw_current_id;
//We don't support bursts so this is all we need

always_ff @(posedge axi_global.aclk, negedge axi_global.aresetn) begin
    if (!axi_global.aresetn) begin
        aw_current_valid <= 1'b0;
        aw_current_addr  <= '0;
        aw_current_size  <= '0;
        aw_current_id    <= '0;
    end else begin
        if (aw_transfer_complete(req, rsp)) begin
            aw_current_valid <= 1'b1;
            aw_current_addr  <= req.awaddr;
            aw_current_size  <= req.awsize;
            aw_current_id    <= req.awid;
        end else if (w_complete) begin
            aw_current_valid <= 1'b0;
            aw_current_addr  <= '0;
            aw_current_size  <= '0;
            aw_current_id    <= '0;
        end
    end
end
//TODO only assert awready when this single-element fifo isn't full

//TODO require wid == the most recent awid since we won't support write data interleaving

//W channel logic
logic w_current_valid;
data_t w_current_data;
id_t  w_current_id;
wstrb_t w_current_strb;
logic w_current_last;
//We don't support bursts so this is all we need

always_ff @(posedge axi_global.aclk, negedge axi_global.aresetn) begin
    if (!axi_global.aresetn) begin
        w_current_valid <= 1'b0;
        w_current_data  <= '0;
        w_current_id    <= '0;
        w_current_strb  <= '0;
        w_current_last  <= 1'b0;
    end else begin
        if (w_transfer_complete(req, rsp)) begin
            w_current_valid <= 1'b1;
            w_current_data  <= req.wdata;
            w_current_id    <= req.wid;
            w_current_strb  <= req.wstrb;
            w_current_last  <= req.wlast;
        end else if (w_complete) begin
            w_current_valid <= 1'b0;
            w_current_data  <= '0;
            w_current_id    <= '0;
            w_current_strb  <= '0;
            w_current_last  <= 1'b0;
        end
    end
end
//TODO only assert wready when this single-element fifo isn't full

//B channel logic
data_t memory[logic];//The reason that this module isn't synthesizable

always_ff @(posedge axi_global.aclk, negedge axi_global.aresetn) begin
    if (!axi_global.aresetn) begin
        w_complete <= 1'b0;
        rsp_output_reg.bvalid <= 1'b0;
        rsp_output_reg.bid    <= '0;
        rsp_output_reg.bresp  <= AXI_RESP_OKAY;
    end else begin
        if (aw_current_valid && w_current_valid && !w_complete) begin
            w_complete <= 1'b1;
            rsp_output_reg.bvalid <= 1'b1;
            rsp_output_reg.bid    <= w_current_id;
            rsp_output_reg.bresp  <= AXI_RESP_OKAY;

            $display("Writing %h to %h", w_current_data, aw_current_addr);
            memory[aw_current_addr] = w_current_data;//Not synthesizable
        end else if (b_transfer_complete(req, rsp)) begin
            w_complete <= 1'b0;
            rsp_output_reg.bvalid <= 1'b0;
            rsp_output_reg.bid    <= '0;
            rsp_output_reg.bresp  <= AXI_RESP_OKAY;
        end else begin
            w_complete <= 1'b0;
        end
    end
end

endmodule : behavioural_axi_memory
