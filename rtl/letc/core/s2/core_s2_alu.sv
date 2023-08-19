/*
 * File:    core_s2_alu.sv
 * Brief:   The ALU
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

module core_s2_alu
`ifndef IMPORTS_IN_MODULE_SCOPE_UNSUPPORTED
    import letc_pkg::*;
    import core_pkg::*;
`endif
(
    input   word_t      alu_operand_1,
    input   word_t      alu_operand_2,
    input   alu_op_e    alu_operation,
    output  word_t      alu_result
);

//Mux alu_result depending on alu_operation
always_comb begin : alu_mux
    unique case (alu_operation)
        ALU_OP_ADD:     alu_result = alu_operand_1 + alu_operand_2;
        ALU_OP_SUB:     alu_result = alu_operand_1 - alu_operand_2;
        ALU_OP_SLL:     alu_result = alu_operand_1 << alu_operand_2[4:0];
        //TODO ensure the signed'() makes this correct
        ALU_OP_SLT:     alu_result = (signed'(alu_operand_1) < signed'(alu_operand_2)) ? 32'd1 : 32'd0;
        ALU_OP_SLTU:    alu_result = (alu_operand_1 < alu_operand_2) ? 32'd1 : 32'd0;
        ALU_OP_SRL:     alu_result = alu_operand_1 >> alu_operand_2[4:0];
        //TODO ensure the signed'() makes this correct
        ALU_OP_SRA:     alu_result = signed'(alu_operand_1) >>> alu_operand_2[4:0];
        ALU_OP_XOR:     alu_result = alu_operand_1 ^ alu_operand_2;
        ALU_OP_OR:      alu_result = alu_operand_1 | alu_operand_2;
        ALU_OP_AND:     alu_result = alu_operand_1 & alu_operand_2;
        //TODO maybe others in the future (ex pass through, etc)
    endcase
end : alu_mux

endmodule : core_s2_alu
