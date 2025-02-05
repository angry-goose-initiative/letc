/*
 * File:    letc_core_stage_fetch2.sv
 * Brief:   LETC Core 2nd Fetch Stage
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

module letc_core_stage_fetch2
    import riscv_pkg::*;
    import letc_pkg::*;
    import letc_core_pkg::*;
(
    //Clock and reset
    input logic clk,
    input logic rst_n,

    //From fetch 1
    input logic      f1_to_f2_valid,
    input f1_to_f2_s f1_to_f2,

    //Hazard/backpressure signals
    output logic f2_ready,
    input  logic f2_flush,
    input  logic f2_stall,

    //Communication with the IMSS
    letc_core_imss_if.fetch2 imss_if,

    //To decode
    output logic     f2_to_d_valid,
    output f2_to_d_s f2_to_d
);

/* ------------------------------------------------------------------------------------------------
 * Input Flop Stage
 * --------------------------------------------------------------------------------------------- */

logic      f1_to_f2_valid_ff;
f1_to_f2_s f1_to_f2_ff;

always_ff @(posedge clk) begin
    if (!rst_n) begin
        f1_to_f2_valid_ff <= 1'b0;
    end else begin
        if (!f2_stall) begin
            f1_to_f2_valid_ff <= f1_to_f2_valid;
        end
    end
end

always_ff @(posedge clk) begin
    if (!f2_stall) begin
        f1_to_f2_ff <= f1_to_f2;
    end
end

/* ------------------------------------------------------------------------------------------------
 * IMSS Communication and Output Logic
 * --------------------------------------------------------------------------------------------- */

assign f2_to_d_valid    = f1_to_f2_valid_ff & !f2_flush & !f2_stall;

//We're to accept something from F1 if we don't have anything yet, or we have something and the imss is ready to provide it
assign f2_ready         = !f1_to_f2_valid_ff | (f1_to_f2_valid_ff & imss_if.rsp_valid);

assign f2_to_d.pc       = f1_to_f2_ff.pc;
assign f2_to_d.instr    = imss_if.rsp_data[31:0];

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

//verilator lint_save
//verilator lint_off UNUSED

//Useful for debugging
//word_t nice_instr = {f2_to_d.instr, 2'b11};

//TODO

//verilator lint_restore

`endif //SIMULATION

endmodule : letc_core_stage_fetch2
