/**
 * File    letc_core_branch_comparator_tb.sv
 * Brief   TODO
 * 
 * Copyright:
 *  Copyright (C) 2024 John Jekel
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

word_t      i_rs1;
word_t      i_rs2;
cmp_op_e    i_cmp_operation;
logic       o_cmp_result;

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
    i_rs1 = 32'hABCD1234;
    i_rs2 = 32'hABCD1234;
    i_cmp_operation = CMP_OP_EQ;
    #1;
    assert(o_cmp_result == 1'b1);
    i_rs1 = 32'h01010101;
    i_rs2 = 32'hF0F0F0F0;
    i_cmp_operation = CMP_OP_EQ;
    #1;
    assert(o_cmp_result == 1'b0);

    //CMP_OP_NE
    i_rs1 = 32'hABCD1234;
    i_rs2 = 32'hABCD1234;
    i_cmp_operation = CMP_OP_NE;
    #1;
    assert(o_cmp_result == 1'b0);
    i_rs1 = 32'h01010101;
    i_rs2 = 32'hF0F0F0F0;
    i_cmp_operation = CMP_OP_NE;
    #1;
    assert(o_cmp_result == 1'b1);

    //CMP_OP_LT
    i_rs1 = 32'hFFFFFFFF;//Signed -1
    i_rs2 = 32'h00001234;
    i_cmp_operation = CMP_OP_LT;
    #1;
    assert(o_cmp_result == 1'b1);
    i_rs1 = 32'hAAAAAAAA;
    i_rs2 = 32'hAAAAAAAA;
    i_cmp_operation = CMP_OP_LT;
    #1;
    assert(o_cmp_result == 1'b0);
    i_rs1 = 32'h0000ABCD;
    i_rs2 = 32'h00001234;
    i_cmp_operation = CMP_OP_LT;
    #1;
    assert(o_cmp_result == 1'b0);
    i_rs1 = 32'h00001234;
    i_rs2 = 32'h0000ABCD;
    i_cmp_operation = CMP_OP_LT;
    #1;
    assert(o_cmp_result == 1'b1);

    //CMP_OP_GE
    i_rs1 = 32'hFFFFFFFF;//Signed -1
    i_rs2 = 32'h00001234;
    i_cmp_operation = CMP_OP_GE;
    #1;
    assert(o_cmp_result == 1'b0);
    i_rs1 = 32'hAAAAAAAA;
    i_rs2 = 32'hAAAAAAAA;
    i_cmp_operation = CMP_OP_GE;
    #1;
    assert(o_cmp_result == 1'b1);
    i_rs1 = 32'h0000ABCD;
    i_rs2 = 32'h00001234;
    i_cmp_operation = CMP_OP_GE;
    #1;
    assert(o_cmp_result == 1'b1);
    i_rs1 = 32'h00001234;
    i_rs2 = 32'h0000ABCD;
    i_cmp_operation = CMP_OP_GE;
    #1;
    assert(o_cmp_result == 1'b0);

    //CMP_OP_LTU
    i_rs1 = 32'hFFFFFFFF;
    i_rs2 = 32'h00001234;
    i_cmp_operation = CMP_OP_LTU;
    #1;
    assert(o_cmp_result == 1'b0);
    i_rs1 = 32'hAAAAAAAA;
    i_rs2 = 32'hAAAAAAAA;
    i_cmp_operation = CMP_OP_LTU;
    #1;
    assert(o_cmp_result == 1'b0);
    i_rs1 = 32'h0000ABCD;
    i_rs2 = 32'h00001234;
    i_cmp_operation = CMP_OP_LTU;
    #1;
    assert(o_cmp_result == 1'b0);
    i_rs1 = 32'h00001234;
    i_rs2 = 32'h0000ABCD;
    i_cmp_operation = CMP_OP_LTU;
    #1;
    assert(o_cmp_result == 1'b1);

    //CMP_OP_GE
    i_rs1 = 32'hFFFFFFFF;
    i_rs2 = 32'h00001234;
    i_cmp_operation = CMP_OP_GEU;
    #1;
    assert(o_cmp_result == 1'b1);
    i_rs1 = 32'hAAAAAAAA;
    i_rs2 = 32'hAAAAAAAA;
    i_cmp_operation = CMP_OP_GEU;
    #1;
    assert(o_cmp_result == 1'b1);
    i_rs1 = 32'h0000ABCD;
    i_rs2 = 32'h00001234;
    i_cmp_operation = CMP_OP_GEU;
    #1;
    assert(o_cmp_result == 1'b1);
    i_rs1 = 32'h00001234;
    i_rs2 = 32'h0000ABCD;
    i_cmp_operation = CMP_OP_GEU;
    #1;
    assert(o_cmp_result == 1'b0);

    $finish;
end

endmodule : letc_core_branch_comparator_tb
