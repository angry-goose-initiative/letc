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
 * Signals
 * --------------------------------------------------------------------------------------------- */

logic pc_ff_we;
logic s1_to_s2_ff_we;
logic bypass_pc_for_fetch_addr;

/* ------------------------------------------------------------------------------------------------
 * S1A: Logic BEFORE the outputs to the MMU (address/valid going to the IMEM)
 * --------------------------------------------------------------------------------------------- */

/* PC Logic **************************************************************************************/

word_t pc_ff;
word_t next_pc;
word_t next_seq_pc;

always_ff @(posedge clk, negedge rst_n) begin : pc_seq_logic
    if (~rst_n) begin
        pc_ff       <= RESET_PC;
    end else begin
        if (pc_ff_we) begin//Hopefully this infers a clock gate :)
            pc_ff       <= next_pc;
        end
    end
end : pc_seq_logic

/* Next PC Logic *********************************************************************************/

always_comb begin : next_pc_logic 
    //Note: This dosn't worry about stalling
    //TODO what about the priority between traps and branches?
    if (trap_occurred) begin
        next_pc = trap_target_addr;
    end else if (s2_to_s1.branch_en) begin
        next_pc = s2_to_s1.branch_target_addr;
    end else begin
        next_pc = next_seq_pc;
    end
end : next_pc_logic

assign next_seq_pc = pc_ff + 32'd4;

/* Fetch Address Bypass Mux ***********************************************************************/

//Note: this may introduce a large critical path, but it allows us to reduce latency and avoid
//complicating the pipeline further

//TODO in the future, evaluate the timing impact of this long critical path from s2 through next_pc
//into the MMU. If it ends up being too long, just don't bypass and deal with the extra latency in s1

assign mmu_instr_req.addr = bypass_pc_for_fetch_addr ? next_pc : pc_ff;

/* ------------------------------------------------------------------------------------------------
 * S1B: Logic AFTER the MMU (instr/ready/illegal/etc coming from IMEM)
 * --------------------------------------------------------------------------------------------- */

s1_to_s2_s s1_to_s2_ff;

//We add an extra flop stage here to improve timing
always_ff @(posedge clk, negedge rst_n) begin : s1b_output_flops
    if (!rst_n) begin
        s1_to_s2_ff.pc     <= 32'hDEADBEEF;
        s1_to_s2_ff.instr  <= 32'hDEADBEEF;
        s1_to_s2_ff.valid  <= 1'd0;
    end else begin
        if (s1_flush) begin//Flush due to unexpected change in control flow; discard what we would have sent to s2
            s1_to_s2_ff.valid  <= 1'd0;
        end else if (s1_to_s2_ff_we) begin//We are ready to send a new instruction to s2 (if the
            s1_to_s2_ff.pc     <= pc_ff;
            s1_to_s2_ff.instr  <= mmu_instr_rsp.instr;
            s1_to_s2_ff.valid  <= 1'd1;//We're guaranteed mmu...ready is 1 since s1_to_s2_ff_we is 1
        end else if (s1_stall && s1_to_s2_ff.valid) begin//We are stalled, but already sent an instruction to s2, so we don't want to duplicate it
            s1_to_s2_ff.valid  <= 1'd0;
        end
    end
end : s1b_output_flops

assign s1_to_s2.pc     = s1_to_s2_ff.pc;
assign s1_to_s2.instr  = s1_to_s2_ff.instr;

//FIXME is this correct? We already have it be flushed before the flop, but that takes a cycle to take effect, so this is necessary right?...
assign s1_to_s2.valid  = s1_to_s2_ff.valid && ~s1_flush;
//assign s1_to_s2.valid  = s1_to_s2_ff.valid;

/* ------------------------------------------------------------------------------------------------
 * S1 Control Logic and State Machine
 * --------------------------------------------------------------------------------------------- */

/* Stall and Flush Logic *************************************************************************/

//NOTE: None of this depends on the current state because these are cause by
//outside things (ex. the MMU/IMEM not being ready, branches, traps, s2 being busy, etc)

logic  s1_stall;
logic  s1_flush;

assign s1_flush = s2_to_s1.branch_en || trap_occurred;
//We don't stall if we are flushing because we want to flush the pipeline
//registers (so we have to be able to write to them)
assign s1_stall = (~s1_flush) && (~mmu_instr_rsp.ready || s2_busy);

/* State Machine *********************************************************************************/

typedef enum logic [2:0] {
    INIT,//Initial fetch
    FETCHING,//All other fetches
    HALT
} state_e;
state_e state_ff, next_state;

always_ff @(posedge clk, negedge rst_n) begin : state_seq_logic
    if (!rst_n) begin
        state_ff <= INIT;
    end else begin
        state_ff <= next_state;
    end
end : state_seq_logic

always_comb begin : next_state_logic
    unique case (state_ff)
        INIT: begin
            //We remain in INIT until we fetch the first instruction
            if (mmu_instr_rsp.ready) begin
                next_state = FETCHING;
            end else begin
                next_state = INIT;
            end
        end
        HALT: next_state = HALT;//There is no escape except for reset
        FETCHING: begin
            //If the previous instruction was LETC.EXIT, we halt
            if (halt_req) begin
                next_state = HALT;
            end else begin//Otherwise, we'll continue fetching instructions!
                next_state = FETCHING;
            end
        end
        default: next_state = HALT;//We entered an illegal state, so halt
    endcase
end : next_state_logic

/* Control Signals *******************************************************************************/

logic leaving_init_next_posedge;

//These should be equivalent
//assign leaving_init_next_posedge = (state_ff == INIT) && mmu_instr_rsp.ready;
assign leaving_init_next_posedge = next_state == FETCHING;

//We don't want to write to the PC if we are stalling or in INIT or HALT
//Stalling: Because we need to hold the address steady
//INIT:     Because if we allow pc_ff to change, then because we are also bypassing, the bypassed value may change too (since it is pc_ff + 4)
//HALT:     Because no state should change while we are halted
//Note that if we are anticipating leaving INIT next cycle, we want to write to pc_ff so
//    that we are ready to fetch the next instruction immediately when we enter FETCHING (assuming we don't stall)
assign pc_ff_we = (leaving_init_next_posedge || (state_ff == FETCHING)) && ~s1_stall;

//We don't want to bypass pc_ff with next_pc if we are stalling or in INIT or HALT
//Stalling: Because we need to hold the address steady
//INIT:     Because we need to fetch the first instruction, not the instruction after the first instruction
//HALT:     Because no state should change while we are halted
//Note that if we are anticipating leaving INIT next cycle, we want to immediately bypass
//    so we can fetch the next instruction immediately when we enter FETCHING before pc_ff is latched with the new address too (assuming we don't stall)
assign bypass_pc_for_fetch_addr = (leaving_init_next_posedge || (next_state == FETCHING)) && ~s1_stall;

//We don't want to write to the state_ff if we are stalling or in HALT
//TODO why stalling?
//HALT:     Because no state should change while we are halted
assign s1_to_s2_ff_we = (state_ff != HALT) && ~s1_stall;

assign mmu_instr_req.valid = state_ff != HALT;//All of the rest of the time we are fetching instructions

endmodule : core_s1
