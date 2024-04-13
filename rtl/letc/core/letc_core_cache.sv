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
index_t                      cache_write_index;
logic                        cache_line_wen;
logic [CACHE_LINE_WORDS-1:0] cache_line_wben;
cache_line_s                 cache_line_to_write, cache_line_to_read;
amd_lutram #(
    .DEPTH (CACHE_DEPTH),
    .BWIDTH(WORD_WIDTH),
    .DWIDTH($bits(cache_line_s) - $bits(tag_t)) //just storing the data words now
) data_sram (
    .i_wclk(i_clk),
    .i_wen(cache_line_wen),
    .i_waddr(cache_write_index),
    .i_wben(cache_line_wben),
    .i_wdata(cache_line_to_write.data),

    .i_raddr(stage_index),
    .o_rdata(cache_line_to_read.data)
);

logic tag_wen;
amd_lutram #(
    .DEPTH (CACHE_DEPTH),
    .BWIDTH($bits(tag_t)),
    .DWIDTH($bits(tag_t))
) tags_sram (
    .i_wclk(i_clk),
    .i_wen(tag_wen),
    .i_waddr(cache_write_index),
    .i_wben('1),
    .i_wdata(cache_line_to_write.tag),

    .i_raddr(stage_index),
    .o_rdata(cache_line_to_read.tag)
);

//Valid Flops
logic set_line_valid;
logic [CACHE_DEPTH-1:0] cache_line_valid;
always_ff @(posedge i_clk) begin
    if (!i_rst_n) begin
        cache_line_valid <= '0;
    end else begin
        if (i_flush_cache) begin
            cache_line_valid <= '0;
        end else if (set_line_valid) begin //data ready from the axi fsm means the cache line is being written
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
    stage_limp.ready = hit;
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

//address counter
//this module will facilitate fetching multiple words from memory
//to fill one cache line. Can be loaded directly with the address,
//and then will increment it while it is enabled.
logic addr_counter_en;
logic addr_counter_load;
counter #(
    .WIDTH(PADDR_WIDTH),
    .STEP(4)
) address_counter (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),
    .i_addr(stage_limp.addr),
    .o_addr(axi_fsm_limp.addr),
    .i_en(addr_counter_en),
    .i_load(addr_counter_load)
);

//shift register
//since the byte enables will be "one hot", we will use a shift
//register to drive them. When a word is loaded from memory, we can
//shift the enable to the left to enable the next word.
logic sr_rst_n;
logic sr_load;
logic [CACHE_LINE_WORDS-1:0] sr_load_data;
//we will tie off the load data to 1, since we always want to start
//with the first bit set.
assign sr_load_data = 'b1;
shift_register #(
    .WIDTH(CACHE_LINE_WORDS)
) cache_line_wben_shifter (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),
    .i_sdata('0), //if we initialize with 1, only need to shift in 0s
    .i_shift(axi_fsm_limp.ready), //anytime we write a byte, we shift
    .i_load(sr_load),
    .i_ldata(sr_load_data),
    .o_data(cache_line_wben),
    .o_carryout()
);

typedef enum logic [1:0] {
    CACHE_STATE_IDLE = 2'h0,
    CACHE_STATE_FILL,
    CACHE_STATE_WRITE_TAG
} cache_state_e;

logic [1:0] cache_state_current;
logic [1:0] cache_state_next;

//state transitions
always_ff @(posedge i_clk) begin
    if (!i_rst_n) begin
        cache_state_current <= CACHE_STATE_IDLE;
    end else begin
        cache_state_current <= cache_state_next;
    end
end

//fsm state flow
always_comb begin
    unique case (cache_state_current)
        CACHE_STATE_IDLE: begin
            if (!hit) begin
                cache_state_next = CACHE_STATE_FILL;
            end else begin
                cache_state_next = CACHE_STATE_IDLE;
            end
        end
        CACHE_STATE_FILL: begin
            if (axi_fsm_limp.ready) begin
            //filling is complete when the last byte enable has been set
                if (cache_line_wben[CACHE_LINE_WORDS-1]) begin //how to make sure this is a constant?
                    cache_state_next = CACHE_STATE_WRITE_TAG;
                end else begin
                    cache_state_next = CACHE_STATE_FILL;
                end
            end
        end
        CACHE_STATE_WRITE_TAG: begin
            cache_state_next = CACHE_STATE_IDLE;
        end
        default: begin
            cache_state_next = CACHE_STATE_IDLE;
        end
    endcase
end

//write logic
always_comb begin
    //cache lines
    cache_line_to_write.tag  = stage_tag_compare_value;
    //byte enables will take care of allowing the correct word to be written.
    //this means we can connect all of the cache line write words in parallel
    for (int i=0; i<CACHE_LINE_WORDS; i++) begin
        cache_line_to_write.data[i] = axi_fsm_limp.rdata;
    end
    //the write index will always be the same as the read index, since
    //we are filling on a miss to that particular index
    cache_write_index = stage_index;
    //state dependent outputs
end

//FIXME
assign axi_fsm_limp.wen_nren = 1'b0;
assign axi_fsm_limp.size = SIZE_WORD;

/* ------------------------------------------------------------------------------------------------
 * Output Logic
 * --------------------------------------------------------------------------------------------- */
always_comb begin
    unique case (cache_state_current)
        CACHE_STATE_IDLE: begin
            addr_counter_load  = hit ? 1'b0 : 1'b1;
            addr_counter_en    = 1'b0;
            sr_load            = 1'b1;
            tag_wen            = 1'b0;
            axi_fsm_limp.valid = 1'b0;
            set_line_valid     = 1'b0;
            cache_line_wen     = 1'b0;
        end
        CACHE_STATE_FILL: begin
            addr_counter_load  = 1'b0;
            addr_counter_en    = axi_fsm_limp.ready;
            sr_load            = 1'b0;
            tag_wen            = 1'b0;
            axi_fsm_limp.valid = 1'b1;
            set_line_valid     = 1'b0;
            cache_line_wen     = axi_fsm_limp.ready;
        end
        CACHE_STATE_WRITE_TAG: begin
            addr_counter_load  = 1'b0;
            addr_counter_en    = 1'b0;
            sr_load            = 1'b0;
            tag_wen            = 1'b1;
            axi_fsm_limp.valid = 1'b0;
            set_line_valid     = 1'b1;
            cache_line_wen     = 1'b0;
        end
        default: begin
            addr_counter_load  = 1'b0;
            addr_counter_en    = 1'b0;
            sr_load            = 1'b0;
            tag_wen            = 1'b0;
            axi_fsm_limp.valid = 1'b0;
            set_line_valid     = 1'b0;
            cache_line_wen     = 1'b0;
        end
    endcase
end
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
