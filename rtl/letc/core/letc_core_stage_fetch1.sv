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
    input logic     pc_load_en,
    input pc_word_t pc_load_val,

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

/* ------------------------------------------------------------------------------------------------
 * Post-Reset Initialization
 * --------------------------------------------------------------------------------------------- */

//Needed to deal with PC latency schenanigans and the IMSS
logic f1_init;
always_ff @(posedge clk) begin
    if (!rst_n) begin
        f1_init <= 1'b1;
    end else begin
        if (!f1_stall & f1_ready) begin
            f1_init <= 1'b0;
        end
    end
end

/* ------------------------------------------------------------------------------------------------
 * PC Logic
 * --------------------------------------------------------------------------------------------- */

pc_word_t pc_word_ff, next_pc_word, next_seq_pc_word;

always_comb begin
    next_seq_pc_word = pc_word_ff + 30'h1;

    if (pc_load_en) begin
        next_pc_word = pc_load_val;
    end else begin
        next_pc_word = next_seq_pc_word;
    end
end

always_ff @(posedge clk) begin
    if (!rst_n) begin
        pc_word_ff <= RESET_PC_WORD;
    end else begin
        if (!f1_stall & f1_ready & !f1_init) begin
            pc_word_ff <= next_pc_word;
        end
    end
end

/* ------------------------------------------------------------------------------------------------
 * PC Latency Management
 * --------------------------------------------------------------------------------------------- */

//Need to deal with stalling latency/etc because fetch_addr needs to be the "same" as the PC
vaddr_t fetch_addr;
always_comb begin
    if (f1_stall | !f1_ready | f1_init) begin
        fetch_addr = {pc_word_ff, 2'b00};
    end else begin
        fetch_addr = {next_pc_word, 2'b00};
    end
end

/* ------------------------------------------------------------------------------------------------
 * IMSS Communication
 * --------------------------------------------------------------------------------------------- */

assign imss_if.req_valid        = !f1_flush & !f1_stall;
assign imss_if.req_virtual_addr = fetch_addr;
assign f1_ready                 = imss_if.req_ready;

/* ------------------------------------------------------------------------------------------------
 * Output To F2
 * --------------------------------------------------------------------------------------------- */

assign f1_to_f2_valid   = f1_ready & !f1_flush & !f1_stall & !f1_init;
assign f1_to_f2.pc_word = pc_word_ff;

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

//verilator lint_save
//verilator lint_off UNUSED

word_t pc, next_pc, next_seq_pc;//Useful for debugging
assign pc          = {pc_word_ff,       2'b00};
assign next_pc     = {next_pc_word,     2'b00};
assign next_seq_pc = {next_seq_pc_word, 2'b00};

//TODO

//TODO also in simulation init registers to 32'hDEADBEEF to aid debugging

//verilator lint_restore

`endif //SIMULATION

endmodule : letc_core_stage_fetch1
