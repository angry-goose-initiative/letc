/*
 * File:    letc_core_branch_comparator.sv
 * Brief:   Comparison logic for branch instructions
 *
 * Copyright:
 *  Copyright (C) 2023-2024 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * Partialy based on JZJCoreF's BranchALU.sv
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_branch_comparator
    import letc_pkg::*;
    import letc_core_pkg::*;
(
    input   word_t      i_rs1,
    input   word_t      i_rs2,
    input   cmp_op_e    i_cmp_operation,
    output  logic       o_cmp_result
);

//Mux o_cmp_result depending on the comparison and the values of rs1 and rs2
always_comb begin
    unique case (i_cmp_operation)
        CMP_OP_EQ:  o_cmp_result =          i_rs1  ==           i_rs2;
        CMP_OP_NE:  o_cmp_result =          i_rs1  !=           i_rs2;
        CMP_OP_LT:  o_cmp_result =  signed'(i_rs1) <    signed'(i_rs2);
        CMP_OP_GE:  o_cmp_result =  signed'(i_rs1) >=   signed'(i_rs2);
        CMP_OP_LTU: o_cmp_result =          i_rs1  <            i_rs2;
        CMP_OP_GEU: o_cmp_result =          i_rs1  >=           i_rs2;
        default:    o_cmp_result = 1'b0;
    endcase
end

endmodule : letc_core_branch_comparator
