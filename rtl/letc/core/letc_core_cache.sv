/*
 * File:    letc_core_cache.sv
 * Brief:   Cache module used for both LETC Core instruction and data caches
 *
 * Copyright:
 *  Copyright (C) 2024 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * A simple write-through, direct-mapped cache
 *
 * INDEX_WIDTH is the number of bits used for the index, so the CACHE_DEPTH is 2 ** INDEX_WIDTH
 * OFFSET_WIDTH is the number of bits used for the WORD offset, so the number of CACHE_LINE_WORDS is 2 ** OFFSET_WIDTH
 *
 * We force the offset width to be a multiple of the word width for simplicity
 * (no need to deal with partial words in a given cache line)
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_cache
    import letc_pkg::*;
    import letc_core_pkg::*;
#(
    parameter INDEX_WIDTH   = 6,//AKA $clog2(CACHE_DEPTH)
    parameter OFFSET_WIDTH  = 4//AKA $clog2(CACHE_LINE_WORDS)
) (//TODO perhaps parameters for read only caches?
    //Clock and reset
    input logic i_clk,
    input logic i_rst_n,

    //Signal to flush all cache lines
    //TODO how to convey if the flush is not yet complete?
    input logic i_flush_cache,

    //Cache interface (LIMP)
    letc_core_limp_if.servicer stage_limp,

    //LIMP interface to AXI FSM
    letc_core_limp_if.requestor axi_fsm_limp
);

/* ------------------------------------------------------------------------------------------------
 * Constants and Types
 * --------------------------------------------------------------------------------------------- */

localparam TAG_WIDTH        = PADDR_WIDTH - INDEX_WIDTH - OFFSET_WIDTH - 2;

localparam CACHE_LINE_WORDS = 2 ** OFFSET_WIDTH;
localparam CACHE_DEPTH      = 2 ** INDEX_WIDTH;

typedef logic [TAG_WIDTH-1:0]    tag_t;
typedef logic [INDEX_WIDTH-1:0]  index_t;
typedef logic [OFFSET_WIDTH-1:0] word_offset_t;
typedef logic [1:0]              byte_offset_t;

typedef struct packed {
    //Valid bits stored outsize of the cache in flops to allow single-cycle flushing
    tag_t                           tag;
    word_t [CACHE_LINE_WORDS-1:0]   data;
} cache_line_s;

/* ------------------------------------------------------------------------------------------------
 * Input Address Splitting
 * --------------------------------------------------------------------------------------------- */

tag_t           stage_tag_compare_value;
index_t         stage_index;
word_offset_t   stage_word_offset;
byte_offset_t   stage_byte_offset;

always_comb begin
    stage_tag_compare_value = stage_limp.addr[INDEX_WIDTH + OFFSET_WIDTH + 2 +: TAG_WIDTH];
    stage_index             = stage_limp.addr[              OFFSET_WIDTH + 2 +: INDEX_WIDTH];
    stage_word_offset       = stage_limp.addr[                             2 +: OFFSET_WIDTH];
    stage_byte_offset       = stage_limp.addr[                             0 +: 2];
end

/* ------------------------------------------------------------------------------------------------
 * SRAM and Valid Flops
 * --------------------------------------------------------------------------------------------- */

//SRAM
//This can just be single ported since this is a write-through cache!
//The refilling FSM is the only thing that needs to write to the SRAM, and
//the stage using the cache only needs to read it! (with tag comparison also being snooped by the
//refilling FSM)
//TODO need to expose byte enables to make things simpler for us
logic        cache_line_wen;
index_t      cache_write_index;
cache_line_s cache_line_to_write, cache_line_to_read;
amd_lutram #(
    .DEPTH (CACHE_DEPTH),
    .BWIDTH(WORD_WIDTH),
    .DWIDTH($bits(cache_line_s))
) sram (
    .i_wclk(i_clk),
    .i_wen(cache_line_wen),
    .i_waddr(cache_write_index),
    .i_wben('1),//TODO
    .i_wdata(cache_line_to_write),

    .i_raddr(stage_index),
    .o_rdata(cache_line_to_read)
);

//Valid Flops
logic [CACHE_DEPTH-1:0] cache_line_valid;
always_ff @(posedge i_clk) begin
    if (!i_rst_n) begin
        cache_line_valid <= '0;
    end else begin
        if (i_flush_cache) begin
            cache_line_valid <= '0;
        end else if (cache_line_wen) begin
            //Since this is a write-through cache, and there is no need to invalidate lines
            //for cache coherency for example, the only time a cache line can
            //become valid is when we write to it; and then it can never become invalid
            //again until the cache is flushed!
            cache_line_valid[cache_write_index] <= 1'b1;
        end
    end
end

/* ------------------------------------------------------------------------------------------------
 * Hit Detection and Read Logic
 * --------------------------------------------------------------------------------------------- */

logic   hit;
word_t  hit_word;

always_comb begin
    if (stage_limp.valid && !stage_limp.wen_nren && cache_line_valid[stage_index]) begin
        hit = cache_line_to_read.tag == stage_tag_compare_value;
    end else begin
        hit = 1'b0;
    end

    hit_word = cache_line_to_read.data[stage_word_offset];

    unique case (stage_limp.size)
        SIZE_BYTE: begin
            unique case (stage_byte_offset)
                2'b00: stage_limp.rdata = {24'h0, hit_word[7:0]};
                2'b01: stage_limp.rdata = {24'h0, hit_word[15:8]};
                2'b10: stage_limp.rdata = {24'h0, hit_word[23:16]};
                2'b11: stage_limp.rdata = {24'h0, hit_word[31:24]};
            endcase
        end
        SIZE_HALFWORD:  stage_limp.rdata = stage_byte_offset[1] ? {16'h0, hit_word[31:16]} : {16'h0, hit_word[15:0]};
        SIZE_WORD:      stage_limp.rdata = hit_word;
        default: stage_limp.rdata = 32'hDEADBEEF;//This should never occur
    endcase
end

/* ------------------------------------------------------------------------------------------------
 * Line Refilling FSM and Write Logic
 * --------------------------------------------------------------------------------------------- */

//TODO

always_comb begin
    cache_line_to_write.tag = stage_tag_compare_value;
end

/* ------------------------------------------------------------------------------------------------
 * Output Logic
 * --------------------------------------------------------------------------------------------- */

//TODO

assign stage_limp.ready     = 1'b0;//TODO
assign axi_fsm_limp.valid   = 1'b0;//TODO

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

//Parameter assertions
initial begin
    assert(TAG_WIDTH > 0);
    assert(INDEX_WIDTH > 0);
    assert(OFFSET_WIDTH > 0);

    assert(CACHE_LINE_WORDS > 0);
    assert(CACHE_DEPTH > 0);
end

//TODO

`endif //SIMULATION

endmodule : letc_core_cache
