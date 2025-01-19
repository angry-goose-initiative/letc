/**
 * File    letc_core_branch_comparator_tb.sv
 * Brief   TODO
 *
 * Copyright:
 *  Copyright (C) 2024-2025 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_branch_comparator_tb;

import letc_pkg::*;
import letc_core_pkg::*;

/* ------------------------------------------------------------------------------------------------
 * DUT Connections
 * --------------------------------------------------------------------------------------------- */

word_t      rs1_val;
word_t      rs2_val;
cmp_op_e    cmp_operation;
logic       cmp_result;

/* ------------------------------------------------------------------------------------------------
 * DUT
 * --------------------------------------------------------------------------------------------- */

letc_core_branch_comparator dut (.*);

/* ------------------------------------------------------------------------------------------------
 * Clocking
 * --------------------------------------------------------------------------------------------- */

//Purely combinational so no clocking needed

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

initial begin
    //CMP_OP_EQ
    rs1_val         = 32'hABCD1234;
    rs2_val         = 32'hABCD1234;
    cmp_operation   = CMP_OP_EQ;
    #1;
    assert(cmp_result == 1'b1);
    rs1_val         = 32'h01010101;
    rs2_val         = 32'hF0F0F0F0;
    cmp_operation   = CMP_OP_EQ;
    #1;
    assert(cmp_result == 1'b0);

    //CMP_OP_NE
    rs1_val         = 32'hABCD1234;
    rs2_val         = 32'hABCD1234;
    cmp_operation   = CMP_OP_NE;
    #1;
    assert(cmp_result == 1'b0);
    rs1_val         = 32'h01010101;
    rs2_val         = 32'hF0F0F0F0;
    cmp_operation   = CMP_OP_NE;
    #1;
    assert(cmp_result == 1'b1);

    //CMP_OP_LT
    rs1_val         = 32'hFFFFFFFF;//Signed -1
    rs2_val         = 32'h00001234;
    cmp_operation   = CMP_OP_LT;
    #1;
    assert(cmp_result == 1'b1);
    rs1_val         = 32'hAAAAAAAA;
    rs2_val         = 32'hAAAAAAAA;
    cmp_operation   = CMP_OP_LT;
    #1;
    assert(cmp_result == 1'b0);
    rs1_val         = 32'h0000ABCD;
    rs2_val         = 32'h00001234;
    cmp_operation   = CMP_OP_LT;
    #1;
    assert(cmp_result == 1'b0);
    rs1_val         = 32'h00001234;
    rs2_val         = 32'h0000ABCD;
    cmp_operation   = CMP_OP_LT;
    #1;
    assert(cmp_result == 1'b1);

    //CMP_OP_GE
    rs1_val         = 32'hFFFFFFFF;//Signed -1
    rs2_val         = 32'h00001234;
    cmp_operation   = CMP_OP_GE;
    #1;
    assert(cmp_result == 1'b0);
    rs1_val         = 32'hAAAAAAAA;
    rs2_val         = 32'hAAAAAAAA;
    cmp_operation   = CMP_OP_GE;
    #1;
    assert(cmp_result == 1'b1);
    rs1_val         = 32'h0000ABCD;
    rs2_val         = 32'h00001234;
    cmp_operation   = CMP_OP_GE;
    #1;
    assert(cmp_result == 1'b1);
    rs1_val         = 32'h00001234;
    rs2_val         = 32'h0000ABCD;
    cmp_operation   = CMP_OP_GE;
    #1;
    assert(cmp_result == 1'b0);

    //CMP_OP_LTU
    rs1_val         = 32'hFFFFFFFF;
    rs2_val         = 32'h00001234;
    cmp_operation   = CMP_OP_LTU;
    #1;
    assert(cmp_result == 1'b0);
    rs1_val         = 32'hAAAAAAAA;
    rs2_val         = 32'hAAAAAAAA;
    cmp_operation   = CMP_OP_LTU;
    #1;
    assert(cmp_result == 1'b0);
    rs1_val         = 32'h0000ABCD;
    rs2_val         = 32'h00001234;
    cmp_operation   = CMP_OP_LTU;
    #1;
    assert(cmp_result == 1'b0);
    rs1_val         = 32'h00001234;
    rs2_val         = 32'h0000ABCD;
    cmp_operation   = CMP_OP_LTU;
    #1;
    assert(cmp_result == 1'b1);

    //CMP_OP_GE
    rs1_val         = 32'hFFFFFFFF;
    rs2_val         = 32'h00001234;
    cmp_operation   = CMP_OP_GEU;
    #1;
    assert(cmp_result == 1'b1);
    rs1_val         = 32'hAAAAAAAA;
    rs2_val         = 32'hAAAAAAAA;
    cmp_operation   = CMP_OP_GEU;
    #1;
    assert(cmp_result == 1'b1);
    rs1_val         = 32'h0000ABCD;
    rs2_val         = 32'h00001234;
    cmp_operation   = CMP_OP_GEU;
    #1;
    assert(cmp_result == 1'b1);
    rs1_val         = 32'h00001234;
    rs2_val         = 32'h0000ABCD;
    cmp_operation   = CMP_OP_GEU;
    #1;
    assert(cmp_result == 1'b0);

    $finish;
end

endmodule : letc_core_branch_comparator_tb
