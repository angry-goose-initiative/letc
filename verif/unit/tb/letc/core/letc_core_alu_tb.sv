/**
 * File    letc_core_alu_tb.sv
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

module letc_core_alu_tb;

import letc_pkg::*;
import letc_core_pkg::*;
import riscv_pkg::*;

/* ------------------------------------------------------------------------------------------------
 * DUT Connections
 * --------------------------------------------------------------------------------------------- */

word_t [1:0]    alu_operands;//alu_operands[0] OP alu_operands[1]
alu_op_e        alu_operation;
word_t          alu_result;

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
    alu_operands[0] = 32'h00000001;
    alu_operands[1] = 32'h00000002;
    alu_operation = ALU_OP_ADD;
    #1;
    assert(alu_result == 32'h00000003);

    //ALU_OP_SUB
    alu_operands[0] = 32'h00000003;
    alu_operands[1] = 32'h00000004;
    alu_operation = ALU_OP_SUB;
    #1;
    assert(alu_result == 32'hFFFFFFFF);

    //ALU_OP_SLL
    alu_operands[0] = 32'hABCD1234;
    alu_operands[1] = 32'h00000004;
    alu_operation = ALU_OP_SLL;
    #1;
    assert(alu_result == 32'hBCD12340);

    //ALU_OP_SLT
    alu_operands[0] = 32'hFFFFFFFF;//Remeber that signed this is -1
    alu_operands[1] = 32'h00001234;
    alu_operation = ALU_OP_SLT;
    #1;
    assert(alu_result == 32'h00000001);

    //ALU_OP_SLTU
    alu_operands[0] = 32'hFFFFFFFF;//Now this is unsigned, so a large number
    alu_operands[1] = 32'h00001234;
    alu_operation = ALU_OP_SLTU;
    #1;
    assert(alu_result == 32'h00000000);

    //ALU_OP_SRL
    alu_operands[0] = 32'hABCD1234;
    alu_operands[1] = 32'h00000004;
    alu_operation = ALU_OP_SRL;
    #1;
    assert(alu_result == 32'h0ABCD123);

    //ALU_OP_SRA
    alu_operands[0] = 32'hABCD1234;
    alu_operands[1] = 32'h00000004;
    alu_operation = ALU_OP_SRA;
    #1;
    assert(alu_result == 32'hFABCD123);

    //ALU_OP_XOR
    alu_operands[0] = 32'hAAAA5555;
    alu_operands[1] = 32'hFF00FF00;
    alu_operation = ALU_OP_XOR;
    #1;
    assert(alu_result == 32'h55AAAA55);

    //ALU_OP_OR
    alu_operands[0] = 32'hAAAA5555;
    alu_operands[1] = 32'hFF00FF00;
    alu_operation = ALU_OP_OR;
    #1;
    assert(alu_result == 32'hFFAAFF55);

    //ALU_OP_AND
    alu_operands[0] = 32'hAAAA5555;
    alu_operands[1] = 32'hFF00FF00;
    alu_operation = ALU_OP_AND;
    #1;
    assert(alu_result == 32'hAA005500);

    /*
    //ALU_OP_PASS1
    alu_operands[0] = 32'hAAAA5555;
    alu_operands[1] = 32'hFF00FF00;
    alu_operation = ALU_OP_PASS1;
    #1;
    assert(alu_result == 32'hAAAA5555);

    //ALU_OP_PASS2
    alu_operands[0] = 32'hAAAA5555;
    alu_operands[1] = 32'hFF00FF00;
    alu_operation = ALU_OP_PASS2;
    #1;
    assert(alu_result == 32'hFF00FF00);
    */


    $finish;
end

endmodule : letc_core_alu_tb
