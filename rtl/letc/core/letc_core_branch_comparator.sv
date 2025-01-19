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
    import riscv_pkg::*;
(
    input   word_t      rs1_val,
    input   word_t      rs2_val,
    input   cmp_op_e    cmp_operation,
    output  logic       cmp_result
);

//Mux cmp_result depending on the comparison and the values of rs1 and rs2
always_comb begin
    unique case (cmp_operation)
        CMP_OP_EQ:  cmp_result =          rs1_val  ==           rs2_val;
        CMP_OP_NE:  cmp_result =          rs1_val  !=           rs2_val;
        CMP_OP_LT:  cmp_result =  signed'(rs1_val) <    signed'(rs2_val);
        CMP_OP_GE:  cmp_result =  signed'(rs1_val) >=   signed'(rs2_val);
        CMP_OP_LTU: cmp_result =          rs1_val  <            rs2_val;
        CMP_OP_GEU: cmp_result =          rs1_val  >=           rs2_val;
        default:    cmp_result = 1'b0;
    endcase
end

endmodule : letc_core_branch_comparator
