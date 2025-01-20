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
    import riscv_pkg::*;
(
    input   word_t [1:0]    alu_operands,//alu_operands[0] OP alu_operands[1]
    input   alu_op_e        alu_operation,
    output  word_t          alu_result
);

always_comb begin
    unique case (alu_operation)
        ALU_OP_ADD:     alu_result =          alu_operands[0]  +          alu_operands[1];
        ALU_OP_SUB:     alu_result =          alu_operands[0]  -          alu_operands[1];
        ALU_OP_SLL:     alu_result =          alu_operands[0]  <<         alu_operands[1][4:0];
        ALU_OP_SLT:     alu_result = (signed'(alu_operands[0]) <  signed'(alu_operands[1])) ? 32'd1 : 32'd0;
        ALU_OP_SLTU:    alu_result =         (alu_operands[0]  <          alu_operands[1])  ? 32'd1 : 32'd0;
        ALU_OP_SRL:     alu_result =          alu_operands[0]  >>         alu_operands[1][4:0];
        ALU_OP_SRA:     alu_result =  signed'(alu_operands[0]) >>>        alu_operands[1][4:0];
        ALU_OP_XOR:     alu_result =          alu_operands[0]  ^          alu_operands[1];
        ALU_OP_OR:      alu_result =          alu_operands[0]  |          alu_operands[1];
        ALU_OP_AND:     alu_result =          alu_operands[0]  &          alu_operands[1];
        // FIXME: Need case for JALR
        //ALU_OP_PASS1:   alu_result = alu_operands[0];//Not really needed for any instruction
        //ALU_OP_PASS2:   alu_result = alu_operands[1];//Using ADD and making the first operand 0 instead
        default:        alu_result = 32'hDEADBEEF;
    endcase
end

endmodule : letc_core_alu
