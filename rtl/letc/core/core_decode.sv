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
    output aluop_e alu_operation,
    output logic   illegal_instr
);

//Decode the opcode
opcode_e opcode;
assign opcode = instruction[6:2];

//Determine if we don't support the opcode
logic unsupported_opcode;
always_comb begin : check_if_opcode_supported
    unsupported_opcode = 1'd0;//TODO
    /*unique case(opcode) begin
        
    end
    */
end

//Determine if the instruction is illegal
//TODO we should check other fields too in addition to the opcode
assign illegal_instr = unsupported_opcode || (instruction[1:0] != 2'b11);

//TODO the inner goodness
core_gen_imm core_gen_imm_instance (.*);

endmodule : core_decode
