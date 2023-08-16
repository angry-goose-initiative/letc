/*
 * File:    core_s1.sv
 * Brief:   TODO
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

`ifdef IMPORTS_IN_MODULE_SCOPE_UNSUPPORTED
import letc_pkg::*;
import core_pkg::*;
`endif

module core_s1
`ifndef IMPORTS_IN_MODULE_SCOPE_UNSUPPORTED
    import letc_pkg::*;
    import core_pkg::*;
`endif
(
    input   logic   clk,
    input   logic   rst_n,

    input   logic   halt_req,//LETC.EXIT instruction encountered in M-mode
    input   logic   s2_busy,//Means s2 is NOT ready to accept a new instruction from s1 this cycle

    //TODO other ports
    input   word_t  trap_target_addr,
    input   logic   trap_occurred,
    input   word_t  s2_to_s1_branch_target_addr,
    input   logic   s2_to_s1_branch_en,

    //TODO interface with imem

    //TODO CSRs

    //TODO s2 outputs
    output  logic   s1_to_s2_valid,//Both _pc and _instr are valid
    output  word_t  s1_to_s2_pc,//The PC of s1_to_s2_instr (not the next PC)
    output  word_t  s1_to_s2_instr
);

/* ------------------------------------------------------------------------------------------------
 * Connections
 * --------------------------------------------------------------------------------------------- */

//Global S1 Stall Signal
logic s1_stall;

//?
logic fetch_exception;

//TODO others

logic bypass_pc_for_fetch_addr;
word_t fetch_addr;

/* ------------------------------------------------------------------------------------------------
 * PC
 * --------------------------------------------------------------------------------------------- */

word_t pc_ff;
word_t next_pc;
word_t next_seq_pc;

always_ff @(posedge clk, negedge rst_n) begin : pc_seq_logic
    if (~rst_n) begin
        pc_ff       <= RESET_PC;
    end else begin
        if (~s1_stall) begin//Hopefully this infers a clock gate :)
            pc_ff       <= next_pc;
        end
    end
end : pc_seq_logic

always_comb begin : next_pc_logic 
    //Note: This dosn't worry about stalling

    //TODO handle branches and traps
    next_pc = next_seq_pc;
end : next_pc_logic

assign next_seq_pc = pc_ff + 32'd4;

/* ------------------------------------------------------------------------------------------------
 * Fetch Address Logic
 * --------------------------------------------------------------------------------------------- */

assign fetch_addr = bypass_pc_for_fetch_addr ? next_pc : pc_ff;

/* ------------------------------------------------------------------------------------------------
 * Output Logic to S2
 * --------------------------------------------------------------------------------------------- */

assign s1_to_s2_valid = 1'b1;//FIXME do this properly
assign s1_to_s2_pc = pc_ff;//It is ALWAYS pc_ff, never next_pc, even if bypassing since the fetch takes a cycle
assign s1_to_s2_instr = 32'h00000013;//FIXME do this properly

/* ------------------------------------------------------------------------------------------------
 * Module Instantiations
 * --------------------------------------------------------------------------------------------- */

//TODO given how simple s1 is, should we just inline it into core_s1.sv?
core_s1_control core_s1_control_inst    (.*);

endmodule : core_s1
