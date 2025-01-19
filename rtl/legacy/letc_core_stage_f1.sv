/*
 * File:    letc_core_stage_f1.sv
 * Brief:   LETC Core 1st Fetch Stage
 *
 * Copyright:
 *  Copyright (C) 2024 John Jekel
 *  Copyright (C) 2024 Seb Atkinson
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_stage_f1
    import letc_pkg::*;
    import letc_core_pkg::*;
    import riscv_pkg::*;
(
    //Clock and reset
    input logic i_clk,
    input logic i_rst_n,

    //TODO others

    //Branch signals
    input logic     i_branch_taken,
    input pc_word_t i_branch_target,

    //TLB interface
    letc_core_tlb_if.stage itlb_if,

    //Hazard/backpressure signals
    output logic o_stage_ready,
    input  logic i_stage_flush,
    input  logic i_stage_stall,

    //To F2
    output f1_to_f2_s o_f1_to_f2
);

//TODO stall PC logic if tlb not ready
//TODO stall logic if F2 not ready

/* ------------------------------------------------------------------------------------------------
 * PC Logic
 * --------------------------------------------------------------------------------------------- */

pc_word_t pc_word, next_pc_word, next_seq_pc_word, actual_pc_word;

assign next_seq_pc_word = pc_word + 29'h1;

always_comb begin
    if (i_branch_taken) begin
        next_pc_word = i_branch_target;
    end else begin
        next_pc_word = next_seq_pc_word;
    end
end

always_ff @(posedge i_clk) begin
    if (~i_rst_n) begin
        pc_word <= RESET_PC_WORD;
    end else begin
        if (!i_stage_stall) begin
            pc_word <= next_pc_word;
        end
    end
end

//TODO we may need a bypass mux potentially to reduce latency; will have to
//eval timing impact thru TLB of branches. Or simply flush or something
//similar in this case
always_comb begin
    actual_pc_word = pc_word;
end

/* ------------------------------------------------------------------------------------------------
 * Virtual Address Translation
 * --------------------------------------------------------------------------------------------- */

//To mask latency it should be a function of next_pc_word

logic translation_ready;

assign translation_ready = 1'b1;//TODO

paddr_t translated_fetch_addr;

//TODO
assign translated_fetch_addr = {actual_pc_word, 2'h0};//TEMPORARY

/* ------------------------------------------------------------------------------------------------
 * Output Flop Stage
 * --------------------------------------------------------------------------------------------- */

assign o_stage_ready = translation_ready;

always_ff @(posedge i_clk) begin
    if (!i_rst_n) begin
        o_f1_to_f2.valid <= 1'b0;
    end else begin
        if (i_stage_flush) begin
            o_f1_to_f2.valid <= 1'b0;
        end else if (!i_stage_stall) begin
            o_f1_to_f2.valid <= translation_ready;
        end
    end
end

always_ff @(posedge i_clk) begin
    //Save resources by not resetting the datapath; which is fine since `valid` above is reset
    //if (o_stage_ready & !i_stage_stall) begin//More power efficient but worse for timing and area
    if (!i_stage_stall) begin
        o_f1_to_f2.pc_word      <= actual_pc_word;
        o_f1_to_f2.fetch_addr   <= translated_fetch_addr;
    end
end

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

word_t pc, next_seq_pc;//Useful for debugging
assign pc = {actual_pc_word, 2'h0};
assign next_seq_pc = {next_seq_pc_word, 2'h0};

//TODO

//TODO also in simulation init registers to 32'hDEADBEEF to aid debugging

`endif //SIMULATION

endmodule : letc_core_stage_f1
