/*
 * File:    letc_core_alu.sv
 * Brief:   LETC ALU for single-cycle integer operations
 *
 * Copyright:
 *  Copyright (C) 2023-2024 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_alu
    import letc_pkg::*;
    import letc_core_pkg::*;
(
    input   word_t [1:0]    i_alu_operands,//i_alu_operands[0] OP i_alu_operands[1]
    input   alu_op_e        i_alu_operation,
    output  word_t          o_alu_result
);

always_comb begin
    unique case (i_alu_operation)
        ALU_OP_ADD:     o_alu_result =          i_alu_operands[0]  +          i_alu_operands[1];
        ALU_OP_SUB:     o_alu_result =          i_alu_operands[0]  -          i_alu_operands[1];
        ALU_OP_SLL:     o_alu_result =          i_alu_operands[0]  <<         i_alu_operands[1][4:0];
        ALU_OP_SLT:     o_alu_result = (signed'(i_alu_operands[0]) <  signed'(i_alu_operands[1])) ? 32'd1 : 32'd0;
        ALU_OP_SLTU:    o_alu_result =         (i_alu_operands[0]  <          i_alu_operands[1])  ? 32'd1 : 32'd0;
        ALU_OP_SRL:     o_alu_result =          i_alu_operands[0]  >>         i_alu_operands[1][4:0];
        ALU_OP_SRA:     o_alu_result =  signed'(i_alu_operands[0]) >>>        i_alu_operands[1][4:0];
        ALU_OP_XOR:     o_alu_result =          i_alu_operands[0]  ^          i_alu_operands[1];
        ALU_OP_OR:      o_alu_result =          i_alu_operands[0]  |          i_alu_operands[1];
        ALU_OP_AND:     o_alu_result =          i_alu_operands[0]  &          i_alu_operands[1];
        default:        o_alu_result = 32'hDEADBEEF;
    endcase
end

endmodule : letc_core_alu
