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

logic      ff_in_valid;
f1_to_f2_s ff_in;

always_ff @(posedge clk) begin
    if (!rst_n) begin
        ff_in_valid <= 1'b0;
    end else begin
        if (!f2_stall) begin
            ff_in_valid <= f1_to_f2_valid;
        end
    end
end

always_ff @(posedge clk) begin
    if (!f2_stall) begin
        ff_in <= f1_to_f2;
    end
end

/* ------------------------------------------------------------------------------------------------
 * IMSS Communication and Output Logic
 * --------------------------------------------------------------------------------------------- */

assign f2_to_d_valid    = ff_in_valid & !f2_flush & !f2_stall;

//We're to accept something from F1 if we don't have anything from it yet, or we have something from it
//and the imss is ready to provide the actual instruction
assign f2_ready         = !ff_in_valid | (ff_in_valid & imss_if.rsp_valid);

assign f2_to_d.pc       = ff_in.pc;
assign f2_to_d.instr    = imss_if.rsp_data[31:0];

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

//verilator lint_save
//verilator lint_off UNUSED

//Control signals should always be known out of reset
assert property (@(posedge clk) disable iff (!rst_n) !$isunknown(f1_to_f2_valid));
assert property (@(posedge clk) disable iff (!rst_n) !$isunknown(f2_to_d_valid));
assert property (@(posedge clk) disable iff (!rst_n) !$isunknown(f2_ready));
assert property (@(posedge clk) disable iff (!rst_n) !$isunknown(f2_flush));
assert property (@(posedge clk) disable iff (!rst_n) !$isunknown(f2_stall));
assert property (@(posedge clk) disable iff (!rst_n) !$isunknown(imss_if.rsp_valid));

//Valid qualified signals should be known
assert property (@(posedge clk) disable iff (!rst_n) f1_to_f2_valid     |-> !$isunknown(f1_to_f2));
assert property (@(posedge clk) disable iff (!rst_n) f2_to_d_valid      |-> !$isunknown(f2_to_d));
assert property (@(posedge clk) disable iff (!rst_n) imss_if.rsp_valid  |-> !$isunknown(imss_if.rsp_data));
assert property (@(posedge clk) disable iff (!rst_n) ff_in_valid        |-> !$isunknown(ff_in));

//If we're not ready, adhesive should stall us (loopback), unless flush took precedence
assert property (@(posedge clk) disable iff (!rst_n) !f2_ready |-> (f2_stall | f2_flush));

//Outputs should stay stable when we're stalled, with the exception of instr
//as the imss may be refilling a cache line
//FIXME this assertion seems broken when flushing?
//assert property (@(posedge clk) disable iff (!rst_n) f2_stall |-> $stable(f2_to_d.pc));

//If we don't have a valid from f1, we shouldn't have one from imss_if
//FIXME however, this doesn't seem to be upheld when flushing occurs, need to tweak this assertion
//assert property (@(posedge clk) disable iff (!rst_n) imss_if.rsp_valid |-> ff_in_valid);//Contrapostive

//Flushing and stalling a stage at the same time is likely a logic bug in adhesive
assert property (@(posedge clk) disable iff (!rst_n) !(f2_flush & f2_stall));

//Useful for debugging
//word_t nice_instr = {f2_to_d.instr, 2'b11};

//verilator lint_restore

`endif //SIMULATION

endmodule : letc_core_stage_fetch2
