/*
 * File:    letc_core_stage_fetch1.sv
 * Brief:   LETC Core 1st Fetch Stage
 *
 * Copyright:
 *  Copyright (C) 2024-2025 John Jekel
 *  Copyright (C) 2024 Seb Atkinson
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_stage_fetch1
    import riscv_pkg::*;
    import letc_pkg::*;
    import letc_core_pkg::*;
(
    //Clock and reset
    input logic clk,
    input logic rst_n,

    //Change the PC: useful for branches, exceptions, etc
    input logic pc_load_en,
    input pc_t  pc_load_val,

    //Hazard/backpressure signals
    output logic f1_ready,
    input  logic f1_flush,
    input  logic f1_stall,

    //Communication with the IMSS
    letc_core_imss_if.fetch1 imss_if,

    //To fetch 2
    output logic      f1_to_f2_valid,
    output f1_to_f2_s f1_to_f2
);

//f1 is always ready!
assign f1_ready = 1'b1;

/* ------------------------------------------------------------------------------------------------
 * Post-Reset Initialization
 * --------------------------------------------------------------------------------------------- */

//Needed to deal with PC latency schenanigans and the IMSS
logic f1_init;
always_ff @(posedge clk) begin
    if (!rst_n) begin
        f1_init <= 1'b1;
    end else begin
        if (!f1_stall) begin
            f1_init <= 1'b0;
        end
    end
end

/* ------------------------------------------------------------------------------------------------
 * PC Logic
 * --------------------------------------------------------------------------------------------- */

pc_t pc_ff, next_pc, next_seq_pc;

always_comb begin
    next_seq_pc = pc_ff + 32'h4;

    if (pc_load_en) begin
        next_pc = pc_load_val;
    end else begin
        next_pc = next_seq_pc;
    end
end

always_ff @(posedge clk) begin
    if (!rst_n) begin
        pc_ff <= RESET_PC;
    end else begin
        if (!f1_stall & !f1_init) begin
            pc_ff <= next_pc;
        end
    end
end

/* ------------------------------------------------------------------------------------------------
 * PC Latency Management
 * --------------------------------------------------------------------------------------------- */

//Need to deal with stalling latency/etc because the delayed version of fetch_addr needs to be the
//"same" as the PC even though the imss_if doesn't have an enable for it's address in flops
vaddr_t fetch_addr;
always_comb begin
    if (f1_stall | f1_init) begin
        fetch_addr = pc_ff;
    end else begin
        fetch_addr = next_pc;
    end
end

/* ------------------------------------------------------------------------------------------------
 * IMSS Communication
 * --------------------------------------------------------------------------------------------- */

assign imss_if.req_valid        = !f1_flush & !f1_stall;//TODO or should this just be constant 1?
assign imss_if.req_virtual_addr = fetch_addr;

/* ------------------------------------------------------------------------------------------------
 * Output To F2
 * --------------------------------------------------------------------------------------------- */

assign f1_to_f2_valid   = !f1_init & !f1_flush & !f1_stall;
assign f1_to_f2.pc      = pc_ff;

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

//verilator lint_save
//verilator lint_off UNUSED

//f1_init should only be high for a single cycle after reset
assert property (@(posedge clk) disable iff (!rst_n) f1_init  |=> !f1_init);
assert property (@(posedge clk) disable iff (!rst_n) !f1_init |=> !f1_init);

//When stalled, fetch_addr shouldn't change
assert property (@(posedge clk) disable iff (!rst_n) f1_stall |-> $stable(fetch_addr));

//Control signals should always be known out of reset
assert property (@(posedge clk) disable iff (!rst_n) !$isunknown(pc_load_en));
assert property (@(posedge clk) disable iff (!rst_n) !$isunknown(f1_to_f2_valid));
assert property (@(posedge clk) disable iff (!rst_n) !$isunknown(f1_ready));
assert property (@(posedge clk) disable iff (!rst_n) !$isunknown(f1_flush));
assert property (@(posedge clk) disable iff (!rst_n) !$isunknown(f1_stall));
assert property (@(posedge clk) disable iff (!rst_n) !$isunknown(imss_if.req_valid));

//Valid qualified signals should be known
assert property (@(posedge clk) disable iff (!rst_n) pc_load_en         |-> !$isunknown(pc_load_val));
assert property (@(posedge clk) disable iff (!rst_n) f1_to_f2_valid     |-> !$isunknown(f1_to_f2));
assert property (@(posedge clk) disable iff (!rst_n) imss_if.req_valid  |-> !$isunknown(imss_if.req_virtual_addr));

//If we're not ready, adhesive should stall us (loopback)
assert property (@(posedge clk) disable iff (!rst_n) !f1_ready |-> f1_stall);

//Outputs should stay stable when we're stalled
//FIXME this assertion seems broken when flushing?
//assert property (@(posedge clk) disable iff (!rst_n) f1_stall |-> $stable(f1_to_f2));

//Flushing and stalling a stage at the same time is likely a logic bug in adhesive
assert property (@(posedge clk) disable iff (!rst_n) !(f1_flush & f1_stall));

/*
word_t pc, next_pc, next_seq_pc;//Useful for debugging
assign pc          = {pc_word_ff,       2'b00};
assign next_pc     = {next_pc_word,     2'b00};
assign next_seq_pc = {next_seq_pc_word, 2'b00};
*/

//verilator lint_restore

`endif //SIMULATION

endmodule : letc_core_stage_fetch1
