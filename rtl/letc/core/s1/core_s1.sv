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

    //Connections to s2
    output  s1_to_s2_s      s1_to_s2,
    input   s2_to_s1_s      s2_to_s1,

    //Connections to the MMU
    output  mmu_instr_req_s  mmu_instr_req,
    input   mmu_instr_rsp_s  mmu_instr_rsp,

    //TODO other ports
    input   word_t  trap_target_addr,
    input   logic   trap_occurred

    //TODO interface with imem

    //TODO CSRs

    //TODO move these signals to the s1_to_s2 and s2_to_s1 structs
    //TODO s2 outputs
);

/* ------------------------------------------------------------------------------------------------
 * S1A: Logic BEFORE the outputs to the MMU (address/valid going to the IMEM)
 * --------------------------------------------------------------------------------------------- */

//Global S1 Stall Signal
logic s1_stall;

//?
logic fetch_exception;

/* PC Logic **************************************************************************************/

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

/* Fetch Address Bypass Mux ***********************************************************************/

//TODO this may introduce a large critical path, but it allows us to reduce latency and complicating
//the pipeline further

logic bypass_pc_for_fetch_addr;

assign mmu_instr_req.addr = bypass_pc_for_fetch_addr ? next_pc : pc_ff;

/* ------------------------------------------------------------------------------------------------
 * S1B: Logic AFTER the MMU (instr/ready/illegal/etc coming from IMEM)
 * --------------------------------------------------------------------------------------------- */

//We add an extra flop stage here to improve timing
always_ff @(posedge clk, negedge rst_n) begin : s1b_output_flops
    if (!rst_n) begin
        s1_to_s2.pc     <= 32'hDEADBEEF;
        s1_to_s2.instr  <= 32'hDEADBEEF;
        //TODO s1_to_s2.valid
    end else begin
        if (~s1_stall) begin//TODO only if the IMEM was ready, and we're not flushing any previous work, etc
            s1_to_s2.pc     <= pc_ff;
            s1_to_s2.instr  <= mmu_instr_rsp.instr;
            s1_to_s2.valid  <= mmu_instr_rsp.ready;
        end
    end
end : s1b_output_flops

/* ------------------------------------------------------------------------------------------------
 * Common Stage Machine
 * --------------------------------------------------------------------------------------------- */

//TODO given how simple s1 is, should we just inline it into core_s1.sv?
core_s1_control core_s1_control_inst    (.*);

endmodule : core_s1
