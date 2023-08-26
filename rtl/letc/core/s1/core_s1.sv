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
        if (~pc_ff_we) begin//Hopefully this infers a clock gate :)
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
        next_pc = next_seq_pc;
    end else begin
        next_pc = pc_ff;
    end
end : next_pc_logic

assign next_seq_pc = pc_ff + 32'd4;

/* Fetch Address Bypass Mux ***********************************************************************/

//Note: this may introduce a large critical path, but it allows us to reduce latency and avoid
//complicating the pipeline further

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
        //TODO s1_to_s2.valid
    end else begin
        if (s1_to_s2_ff_we) begin
            s1_to_s2_ff.pc     <= pc_ff;
            s1_to_s2_ff.instr  <= mmu_instr_rsp.instr;
            s1_to_s2_ff.valid  <= mmu_instr_rsp.ready;
        end
    end
end : s1b_output_flops

assign s1_to_s2.pc     = s1_to_s2_ff.pc;
assign s1_to_s2.instr  = s1_to_s2_ff.instr;
assign s1_to_s2.valid  = s1_to_s2_ff.valid;
//assign s1_to_s2.valid  = s1_to_s2_ff.valid && ~s1_flush;//FIXME or should this be before the flop? (for both correctness and better timing?)

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

assign pc_ff_we = s1_stall;
assign s1_to_s2_ff_we = s1_stall;

//Not init since we need to fetch the first instruction
//Also don't bypass if we are currently stalling and we need to hold the address while
//we wait for the MMU/IMEM to be ready
assign bypass_pc_for_fetch_addr = (state_ff == FETCHING) && (~s1_stall);

assign mmu_instr_req.valid = (state_ff != HALT);//All of the rest of the time we are fetching instructions

endmodule : core_s1
