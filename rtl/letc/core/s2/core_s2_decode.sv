/*
 * File:    core_s2_decode.sv
 * Brief:   TODO
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

module core_s2_decode
    import core_pkg::*;
(
    input   logic   clk,
    input   logic   rst_n,

    //Instruction in
    input   word_t  instruction,

    //Decoded info out
    output  logic   illegal_instr,
    output  logic   halt_req,
    output  word_t  immediate,
    output  word_t  uimm,
    output  aluop_e alu_operation
    //TODO others
);

/* ------------------------------------------------------------------------------------------------
 * Decode logic
 * --------------------------------------------------------------------------------------------- */

//Decode the opcode
opcode_e opcode;
assign opcode = opcode_e'(instruction[6:2]);

//Determine if we don't support the opcode
logic unsupported_opcode;
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
instr_format_e instr_format;
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

/* ------------------------------------------------------------------------------------------------
 * Output logic
 * --------------------------------------------------------------------------------------------- */

assign halt_req = opcode == OPCODE_CUSTOM_0;

//TODO other inner goodness (to generate command signals for control, the ALU, muxes, etc)

core_s2_gen_imm core_s2_gen_imm_inst (.*);

endmodule : core_s2_decode
