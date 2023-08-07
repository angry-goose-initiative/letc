/*
 * File:    core_s2_control.sv
 * Brief:   Control and decode state machine for LETC Core Stage 2
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

module core_s2_control
    import letc_pkg::*;
    import core_pkg::*;
(
    input   logic   clk,
    input   logic   rst_n,

    //Instruction in
    input   word_t  instruction,

    //Stage 1 signals in
    //TODO

    //Stage 1 signals out
    //TODO

    //Control signals out
    output  logic           illegal_instr,
    output  instr_format_e  instr_format,
    output  alu_op_e        alu_operation,
    output  reg_idx_t       rd_idx,
    output  reg_idx_t       rs1_idx,
    output  reg_idx_t       rs2_idx,
    output  logic           rd_we
    //TODO others
);

/* ------------------------------------------------------------------------------------------------
 * Internal connections and state
 * --------------------------------------------------------------------------------------------- */

typedef enum logic [2:0] {
    INIT,
    HALT,
    FETCH_NEXT,
    WAIT_ON_L1DCACHE,
    //TODO any other additional states needed by various instructions
    FINISH_CURRENT_AND_FETCH_NEXT 
} state_e;
state_e state_ff, next_state;

opcode_e opcode;

logic halt_req;
logic unsupported_opcode;

/* ------------------------------------------------------------------------------------------------
 * State machine logic
 * --------------------------------------------------------------------------------------------- */

always_ff @(posedge clk, negedge rst_n) begin : state_seq_logic
    if (!rst_n) begin
        state_ff <= INIT;
    end else begin
        state_ff <= next_state;
    end
end : state_seq_logic

always_comb begin : next_state_logic
    if (halt_req) begin
        next_state = HALT;
    end else begin
        unique case (state_ff)
            INIT: begin
                //In the future we may do more things in INIT
                next_state = FETCH_NEXT;
            end
            HALT: next_state = HALT;
            FETCH_NEXT: begin
                next_state = HALT;//TODO
            end
            WAIT_ON_L1DCACHE: begin
                next_state = HALT;//TODO
            end
            //TODO any other additional states needed by various instructions
            FINISH_CURRENT_AND_FETCH_NEXT: begin
                next_state = HALT;//TODO
            end
            default: next_state = HALT;//We entered an illegal state, so halt
        endcase
    end
end : next_state_logic

/* ------------------------------------------------------------------------------------------------
 * Control signal output logic / Decode logic (Mealy)
 * --------------------------------------------------------------------------------------------- */

//Decode the opcode
assign opcode = opcode_e'(instruction[6:2]);

//Determine if we don't support the opcode
always_comb begin : check_if_opcode_supported
    unique case(opcode)
        OPCODE_LOAD, OPCODE_CUSTOM_0, OPCODE_MISC_MEM, OPCODE_OP_IMM,
        OPCODE_AUIPC, OPCODE_STORE, OPCODE_AMO, OPCODE_OP, OPCODE_LUI,
        OPCODE_BRANCH, OPCODE_JALR, OPCODE_JAL, OPCODE_SYSTEM: begin
            unsupported_opcode = 1'b0;
        end
        default: begin
            unsupported_opcode = 1'b1;
        end
    endcase
end : check_if_opcode_supported

//Determine if the instruction is illegal
//TODO we should check other fields too in addition to the opcode
assign illegal_instr = unsupported_opcode || (instruction[1:0] != 2'b11) || (instruction == 32'd0) || (instruction == 32'hFFFFFFFF);

//Determine the instruction format
always_comb begin : determine_instr_format
    unique case(opcode)
        OPCODE_OP, OPCODE_AMO:                                    instr_format = INSTR_FORMAT_R;
        OPCODE_LOAD, OPCODE_MISC_MEM, OPCODE_OP_IMM, OPCODE_JALR: instr_format = INSTR_FORMAT_I;
        OPCODE_STORE:                                             instr_format = INSTR_FORMAT_S;
        OPCODE_BRANCH:                                            instr_format = INSTR_FORMAT_B;
        OPCODE_LUI, OPCODE_AUIPC:                                 instr_format = INSTR_FORMAT_U;
        OPCODE_JAL:                                               instr_format = INSTR_FORMAT_J;
        OPCODE_SYSTEM: begin
            //TODO CSRs, ecall, ebreak, mret, sret, wfi, sfence.vma, etc
            instr_format = INSTR_FORMAT_OTHER;//TODO system can vary wildly depending on funct3/funct7
        end
        OPCODE_CUSTOM_0: instr_format = INSTR_FORMAT_OTHER;//TODO this may change if we add custom instructions
        default: instr_format = INSTR_FORMAT_OTHER;
    endcase
end : determine_instr_format

always_comb begin : control_signal_logic
    rd_we = 0;
    unique case (state_ff)
        INIT: begin
            //In the future we may do more things in INIT
            //TODO other control signals
        end
        HALT: begin
            //TODO other control signals
        end
        FETCH_NEXT: begin
            //TODO other control signals
        end
        WAIT_ON_L1DCACHE: begin
            //TODO other control signals
        end
        //TODO any other additional states needed by various instructions
        FINISH_CURRENT_AND_FETCH_NEXT: begin
            //rd_we = ?;//TODO this will depend on the instruction
        end
        default: begin end//Illegal state, so do nothing
    endcase
end : control_signal_logic

//TODO organize where this ends up

assign halt_req = opcode == OPCODE_CUSTOM_0;

assign rd_idx  = instruction[11:7];
assign rs1_idx = instruction[19:15];
assign rs2_idx = instruction[24:20];

//TODO other inner goodness (to generate command signals for control, the ALU, muxes, etc)

endmodule : core_s2_control
