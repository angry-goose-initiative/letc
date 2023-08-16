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
    input   logic   s2_busy//Means s2 is NOT ready to accept a new instruction from s1 this cycle

    //TODO other ports

    //TODO interface with imem
);

/* ------------------------------------------------------------------------------------------------
 * Connections
 * --------------------------------------------------------------------------------------------- */

//Global S1 Stall Signal
logic s1_stall;

//?
logic fetch_exception;

//TODO others

/* ------------------------------------------------------------------------------------------------
 * PC
 * --------------------------------------------------------------------------------------------- */

word_t pc_ff;
word_t next_pc;
word_t next_seq_pc;

always_ff @(posedge clk, negedge rst_n) begin : pc_seq_logic
    if (~rst_n) begin
        pc_ff <= RESET_PC;
    end else begin
        if (~s1_stall) begin//Hopefully this infers a clock gate :)
            pc_ff <= next_pc;
        end
    end
end : pc_seq_logic

always_comb begin : next_pc_logic 
    //Note: This dosn't worry about stalling

    //TODO handle branches
    next_pc = next_seq_pc;
end : next_pc_logic

assign next_seq_pc = pc_ff + 32'd4;

/* ------------------------------------------------------------------------------------------------
 * Module Instantiations
 * --------------------------------------------------------------------------------------------- */

core_s1_control core_s1_control_inst    (.*);

endmodule : core_s1
