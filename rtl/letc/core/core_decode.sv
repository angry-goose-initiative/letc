/*
 * File:    core_decode.sv
 * Brief:   TODO
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

module core_decode
    import core_pkg::*;
(
    input clk,
    input rst_n,

    //Instruction in
    input word_t instruction,

    //Decoded info out
    //TODO others
    output word_t  immediate,
    output word_t  uimm,
    output aluop_e alu_operation,
    output logic   illegal_instr
);

//Decode the opcode
opcode_e opcode;
assign opcode = opcode_e'(instruction[6:2]);

//Determine if we don't support the opcode
logic unsupported_opcode;
always_comb begin : check_if_opcode_supported
    unique case(opcode)
        OPCODE_LOAD, OPCODE_MISC_MEM, OPCODE_OP_IMM, OPCODE_AUIPC,
        OPCODE_STORE, OPCODE_AMO, OPCODE_OP, OPCODE_LUI,
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
assign illegal_instr = unsupported_opcode || (instruction[1:0] != 2'b11);

//Determine the instruction format
instr_format_e instr_format;
always_comb begin : determine_instr_format
    unique case(opcode)
        //TODO 
        default: begin
            instr_format = INSTR_FORMAT_UNKNOWN;
        end 
    endcase
end : determine_instr_format

//TODO other inner goodness (to generate command signals for control, the ALU, muxes, etc)

core_gen_imm core_gen_imm_instance (.*);

endmodule : core_decode
