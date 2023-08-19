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
    output  logic       cmp_result
);

//Mux cmp_result depending on the comparison and the values of rs1 and rs2
always_comb begin : comparator_mux
    unique case (cmp_operation)
        CMP_OP_EQ:  cmp_result = rs1_ff == rs2_ff;
        CMP_OP_NE:  cmp_result = rs1_ff != rs2_ff;
        //TODO ensure the signed'() makes this correct
        CMP_OP_LT:  cmp_result = signed'(rs1_ff) < signed'(rs2_ff);
        CMP_OP_GE:  cmp_result = signed'(rs1_ff) >= signed'(rs2_ff);
        CMP_OP_LTU: cmp_result = rs1_ff < rs2_ff;
        CMP_OP_GEU: cmp_result = rs1_ff >= rs2_ff;
    endcase
end : comparator_mux

endmodule : core_s2_comparator
