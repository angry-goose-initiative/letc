/*
 * File:    core_s2_comparator.sv
 * Brief:   TODO
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
 * Partily based on JZJCoreF's BranchALU.sv
 *
*/

`ifdef IMPORTS_IN_MODULE_SCOPE_UNSUPPORTED
import letc_pkg::*;
import core_pkg::*;
`endif

module core_s2_comparator
`ifndef IMPORTS_IN_MODULE_SCOPE_UNSUPPORTED
    import letc_pkg::*;
    import core_pkg::*;
`endif
(
    input   cmp_op_e    cmp_operation,
    input   word_t      rs1_ff,
    input   word_t      rs2_ff,
    output  logic       branch_en
);

//Mux branch_en depending on the comparison and the values of rs1 and rs2
always_comb begin : comparator_mux
    unique case (cmp_operation)
        CMP_OP_EQ:  branch_en = rs1_ff == rs2_ff;
        CMP_OP_NE:  branch_en = rs1_ff != rs2_ff;
        CMP_OP_LT:  branch_en = signed'(rs1_ff) < signed'(rs2_ff);
        CMP_OP_GE:  branch_en = signed'(rs1_ff) >= signed'(rs2_ff);
        CMP_OP_LTU: branch_en = rs1_ff < rs2_ff;
        CMP_OP_GEU: branch_en = rs1_ff >= rs2_ff;
    endcase
end : comparator_mux

endmodule : core_s2_comparator
