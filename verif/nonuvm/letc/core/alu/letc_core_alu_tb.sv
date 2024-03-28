/**
 * File    letc_core_alu_tb.sv
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

module letc_core_alu_tb;

import letc_pkg::*;
import letc_core_pkg::*;

/* ------------------------------------------------------------------------------------------------
 * DUT Connections
 * --------------------------------------------------------------------------------------------- */

word_t [1:0]    i_alu_operands;//i_alu_operands[0] OP i_alu_operands[1]
alu_op_e        i_alu_operation;
word_t          o_alu_result;

/* ------------------------------------------------------------------------------------------------
 * DUT
 * --------------------------------------------------------------------------------------------- */

letc_core_alu dut (.*);

/* ------------------------------------------------------------------------------------------------
 * Clocking
 * --------------------------------------------------------------------------------------------- */

//Purely combinational so no clocking needed

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

initial begin
    //ALU_OP_ADD
    i_alu_operands[0] = 32'h00000001;
    i_alu_operands[1] = 32'h00000002;
    i_alu_operation = ALU_OP_ADD;
    #1;
    assert(o_alu_result == 32'h00000003);

    //ALU_OP_SUB
    i_alu_operands[0] = 32'h00000003;
    i_alu_operands[1] = 32'h00000004;
    i_alu_operation = ALU_OP_SUB;
    #1;
    assert(o_alu_result == 32'hFFFFFFFF);

    //ALU_OP_SLL
    i_alu_operands[0] = 32'hABCD1234;
    i_alu_operands[1] = 32'h00000004;
    i_alu_operation = ALU_OP_SLL;
    #1;
    assert(o_alu_result == 32'hBCD12340);

    //ALU_OP_SLT
    i_alu_operands[0] = 32'hFFFFFFFF;//Remeber that signed this is -1
    i_alu_operands[1] = 32'h00001234;
    i_alu_operation = ALU_OP_SLT;
    #1;
    assert(o_alu_result == 32'h00000001);

    //ALU_OP_SLTU
    i_alu_operands[0] = 32'hFFFFFFFF;//Now this is unsigned, so a large number
    i_alu_operands[1] = 32'h00001234;
    i_alu_operation = ALU_OP_SLTU;
    #1;
    assert(o_alu_result == 32'h00000000);

    //ALU_OP_SRL
    i_alu_operands[0] = 32'hABCD1234;
    i_alu_operands[1] = 32'h00000004;
    i_alu_operation = ALU_OP_SRL;
    #1;
    assert(o_alu_result == 32'h0ABCD123);

    //ALU_OP_SRA
    i_alu_operands[0] = 32'hABCD1234;
    i_alu_operands[1] = 32'h00000004;
    i_alu_operation = ALU_OP_SRA;
    #1;
    assert(o_alu_result == 32'hFABCD123);

    //ALU_OP_XOR
    i_alu_operands[0] = 32'hAAAA5555;
    i_alu_operands[1] = 32'hFF00FF00;
    i_alu_operation = ALU_OP_XOR;
    #1;
    assert(o_alu_result == 32'h55AAAA55);

    //ALU_OP_OR
    i_alu_operands[0] = 32'hAAAA5555;
    i_alu_operands[1] = 32'hFF00FF00;
    i_alu_operation = ALU_OP_OR;
    #1;
    assert(o_alu_result == 32'hFFAAFF55);

    //ALU_OP_AND
    i_alu_operands[0] = 32'hAAAA5555;
    i_alu_operands[1] = 32'hFF00FF00;
    i_alu_operation = ALU_OP_AND;
    #1;
    assert(o_alu_result == 32'hAA005500);

    //ALU_OP_MCLR
    i_alu_operands[0] = 32'hAAAA5555;
    i_alu_operands[1] = 32'hFF00FF00;
    i_alu_operation = ALU_OP_MCLR;
    #1;
    assert(o_alu_result == 32'h00AA0055);

    /*
    //ALU_OP_PASS1
    i_alu_operands[0] = 32'hAAAA5555;
    i_alu_operands[1] = 32'hFF00FF00;
    i_alu_operation = ALU_OP_PASS1;
    #1;
    assert(o_alu_result == 32'hAAAA5555);

    //ALU_OP_PASS2
    i_alu_operands[0] = 32'hAAAA5555;
    i_alu_operands[1] = 32'hFF00FF00;
    i_alu_operation = ALU_OP_PASS2;
    #1;
    assert(o_alu_result == 32'hFF00FF00);
    */


    $finish;
end

endmodule : letc_core_alu_tb
