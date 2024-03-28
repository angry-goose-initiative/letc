/**
 * File    letc_core_stage_d_tb.sv
 * Brief   TODO
 *
 * Copyright:
 *  Copyright (C) 2024 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

`default_nettype none

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_stage_d_tb;

import letc_pkg::*;
import letc_core_pkg::*;

/* ------------------------------------------------------------------------------------------------
 * Parameters
 * --------------------------------------------------------------------------------------------- */

localparam CLOCK_PERIOD = 10;

/* ------------------------------------------------------------------------------------------------
 * DUT Connections
 * --------------------------------------------------------------------------------------------- */

//Clock and reset
logic i_clk;
logic i_rst_n;

//TODO

//Hazard/backpressure signals
logic o_stage_ready;
logic i_stage_flush;
logic i_stage_stall;

//rs1 Read Port
reg_idx_t    o_rs1_idx;//Also goes to TGHM
word_t       i_rs1_rdata;

//rs2 Read Port
reg_idx_t    o_rs2_idx;//Also goes to TGHM
word_t       i_rs2_rdata;

//Bypass signals
logic     i_bypass_rs1;
logic     i_bypass_rs2;
word_t    i_bypass_rs1_rdata;
word_t    i_bypass_rs2_rdata;

//CSR Read Port
logic        o_csr_explicit_ren;
csr_idx_t    o_csr_explicit_ridx;
word_t       i_csr_explicit_rdata;
logic        i_csr_explicit_rill;

//Branch signals
logic        o_branch_taken;
pc_word_t    o_branch_target;

//From F2
f2_to_d_s i_f2_to_d;

//To E1
d_to_e1_s o_d_to_e1;

/* ------------------------------------------------------------------------------------------------
 * DUT
 * --------------------------------------------------------------------------------------------- */

letc_core_stage_d dut (.*);

/* ------------------------------------------------------------------------------------------------
 * Clocking
 * --------------------------------------------------------------------------------------------- */

initial begin
    forever begin
        i_clk = 1'b0;
        #(CLOCK_PERIOD / 2);
        i_clk = 1'b1;
        #(CLOCK_PERIOD / 2);
    end
end

default clocking cb @(posedge i_clk);
    //Not sure why Verilator complains...
    /* verilator lint_off UNUSEDSIGNAL */

    //Reset
    output i_rst_n;

    //TODO

    //Hazard/backpressure signals
    input  o_stage_ready;
    output i_stage_flush;
    output i_stage_stall;

    //rs1 Read Port
    input  o_rs1_idx;//Also goes to TGHM
    output i_rs1_rdata;

    //rs2 Read Port
    input  o_rs2_idx;//Also goes to TGHM
    output i_rs2_rdata;

    //Bypass signals
    output i_bypass_rs1;
    output i_bypass_rs2;
    output i_bypass_rs1_rdata;
    output i_bypass_rs2_rdata;

    //CSR Read Port
    input  o_csr_explicit_ren;
    input  o_csr_explicit_ridx;
    output i_csr_explicit_rdata;
    output i_csr_explicit_rill;

    //Branch signals
    input  o_branch_taken;
    input  o_branch_target;

    //From F2
    output i_f2_to_d;

    //To E1
    input  o_d_to_e1;

    /* verilator lint_on UNUSEDSIGNAL */
endclocking

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

initial begin
    //Setup
    cb.i_stage_flush        <= 1'b0;
    cb.i_stage_stall        <= 1'b0;
    cb.i_csr_explicit_rill  <= 1'b0;
    cb.i_bypass_rs1         <= 1'b0;
    cb.i_bypass_rs2         <= 1'b0;
    cb.i_f2_to_d            <= '0;

    //Reset things
    cb.i_rst_n <= 1'b0;
    ##2;
    cb.i_rst_n <= 1'b1;
    ##2;

    /////////////////////////////////////////
    //Testing valid timing
    /////////////////////////////////////////

    cb.i_f2_to_d.valid <= 1'b1;
    ##1;//One cycle for clocking block
    assert(!cb.o_d_to_e1.valid);//Too soon
    ##1;//One cycle for the decode stage
    assert(cb.o_d_to_e1.valid);

    cb.i_f2_to_d.valid <= 1'b0;
    ##1;//One cycle for clocking block
    assert(cb.o_d_to_e1.valid);//Too soon
    ##1;//One cycle for the decode stage
    assert(!cb.o_d_to_e1.valid);

    cb.i_f2_to_d.valid <= 1'b1;//Remaining tests can assume this
    ##1;

`ifndef VERILATOR
    //Something is causing problems in Verilator, but works fine in xsim
    //(signals barely change and the dumped FST is corrupt due to enums; VCDs are fineish)


    /////////////////////////////////////////
    //Testing other timing
    /////////////////////////////////////////

    //TODO test the timing of other combinational vs sequential logic

    /////////////////////////////////////////
    //Testing immediate generation, rd ctrl, memory ctrl
    /////////////////////////////////////////

    //I type instructions
    cb.i_f2_to_d.instr <= 30'(32'h1684c783 >> 2);//lbu a5, 360(s1)
    ##2;//One cycle for clocking block, one for the decode stage
    assert(cb.o_d_to_e1.immediate     == 32'd360);
    assert(cb.o_d_to_e1.rd_we         == 1'b1);
    assert(cb.o_d_to_e1.rd_src        == RD_SRC_MEM);
    assert(cb.o_d_to_e1.memory_op     == MEM_OP_LOAD);
    assert(cb.o_d_to_e1.memory_signed == 1'b0);
    assert(cb.o_d_to_e1.memory_size   == SIZE_BYTE);
    cb.i_f2_to_d.instr <= 30'(32'hf8518293 >> 2);//addi t0, gp, -123
    ##2;
    assert(cb.o_d_to_e1.immediate == 32'hffffff85);
    assert(cb.o_d_to_e1.rd_we     == 1'b1);
    assert(cb.o_d_to_e1.rd_src    == RD_SRC_ALU);
    assert(cb.o_d_to_e1.memory_op == MEM_OP_NOP);

    //S type instructions
    cb.i_f2_to_d.instr <= 30'(32'h00112623 >> 2);//sw ra, 12(sp)
    ##2;
    assert(cb.o_d_to_e1.immediate   == 32'd12);
    assert(cb.o_d_to_e1.rd_we       == 1'b0);
    assert(cb.o_d_to_e1.memory_op   == MEM_OP_STORE);
    assert(cb.o_d_to_e1.memory_size == SIZE_WORD);
    cb.i_f2_to_d.instr <= 30'(32'he2489c23 >> 2);//sh tp, -456(a7)
    ##2;
    assert(cb.o_d_to_e1.immediate     == 32'hfffffe38);
    assert(cb.o_d_to_e1.rd_we         == 1'b0);
    assert(cb.o_d_to_e1.memory_op     == MEM_OP_STORE);
    assert(cb.o_d_to_e1.memory_size   == SIZE_HALFWORD);

    //B type instructions
    cb.i_f2_to_d.instr <= 30'(32'h00078a63 >> 2);//beqz a5, offset 0x14
    //Branches are handled in decode, so it's no longer guaranteed the output immediate will be correct
    //##2;//One cycle for clocking block, one for the decode stage
    //assert(cb.o_d_to_e1.immediate == 32'h00000014);
    ##1;//One cycle for clocking block
    assert(dut.imm_b          == 32'h00000014);
    assert(dut.ctrl.rd_we     == 1'b0);
    assert(dut.ctrl.memory_op == MEM_OP_NOP);
    cb.i_f2_to_d.instr <= 30'(32'hfc20e6e3 >> 2);//bltu x1, x2, offset -0x34
    ##1;//One cycle for clocking block
    assert(dut.imm_b          == 32'hffffffcc);
    assert(dut.ctrl.rd_we     == 1'b0);
    assert(dut.ctrl.memory_op == MEM_OP_NOP);

    //U type instructions
    cb.i_f2_to_d.instr <= 30'(32'h000067b7 >> 2);//lui a5, 0x6
    ##2;
    assert(cb.o_d_to_e1.immediate == 32'h00006000);
    assert(cb.o_d_to_e1.rd_we     == 1'b1);
    assert(cb.o_d_to_e1.rd_src    == RD_SRC_ALU);
    assert(cb.o_d_to_e1.memory_op == MEM_OP_NOP);
    cb.i_f2_to_d.instr <= 30'(32'habcd1117 >> 2);//auipc sp, 0xabcd1
    ##2;
    assert(cb.o_d_to_e1.immediate == 32'habcd1000);
    assert(cb.o_d_to_e1.rd_we     == 1'b1);
    assert(cb.o_d_to_e1.rd_src    == RD_SRC_ALU);
    assert(cb.o_d_to_e1.memory_op == MEM_OP_NOP);

    //J type instructions
    cb.i_f2_to_d.instr <= 30'(32'hfd9fc0ef >> 2);//jal offset -0x3028
    //Branches are handled in decode, so it's no longer guaranteed the output immediate will be correct
    //##2;//One cycle for clocking block, one for the decode stage
    //assert(cb.o_d_to_e1.immediate == 32'hffffcfd8);
    ##1;
    assert(dut.imm_j          == 32'hffffcfd8);
    assert(dut.ctrl.rd_we     == 1'b1);
    assert(dut.ctrl.rd_src    == RD_SRC_ALU);
    assert(dut.ctrl.memory_op == MEM_OP_NOP);
    cb.i_f2_to_d.instr <= 30'(32'h0040006f >> 2);//jal offset +4
    ##1;
    assert(dut.imm_j          == 32'h4);
    assert(dut.ctrl.rd_we     == 1'b1);
    assert(dut.ctrl.rd_src    == RD_SRC_ALU);
    assert(dut.ctrl.memory_op == MEM_OP_NOP);

    //CSR micro immediates and index
    cb.i_f2_to_d.instr <= 30'(32'h34417073 >> 2);//csrci mip, 2
    ##2;
    assert(cb.o_d_to_e1.immediate == 32'h00000002);
    assert(cb.o_d_to_e1.csr_idx   == 12'h344);//mip
    assert(cb.o_d_to_e1.rd_we     == 1'b1);
    assert(cb.o_d_to_e1.rd_src    == RD_SRC_CSR);
    assert(cb.o_d_to_e1.memory_op == MEM_OP_NOP);

    /////////////////////////////////////////
    //Testing alu/alu op mux ctrl signals
    /////////////////////////////////////////

    //ALU_OP_ADD, pc, imm
    cb.i_f2_to_d.instr <= 30'(32'h0007b197 >> 2);//auipc x3, 123
    ##2;
    assert(cb.o_d_to_e1.alu_op      == ALU_OP_ADD);
    assert(cb.o_d_to_e1.alu_op1_src == ALU_OP1_SRC_PC);
    assert(cb.o_d_to_e1.alu_op2_src == ALU_OP2_SRC_IMM);

    //ALU_OP_ADD, 0, imm
    cb.i_f2_to_d.instr <= 30'(32'h0cafe2b7 >> 2);//lui t0, 0xcafe
    ##2;
    assert(cb.o_d_to_e1.alu_op      == ALU_OP_ADD);
    assert(cb.o_d_to_e1.alu_op1_src == ALU_OP1_SRC_ZERO);
    assert(cb.o_d_to_e1.alu_op2_src == ALU_OP2_SRC_IMM);

    //ALU_OP_ADD, pc, 4
    cb.i_f2_to_d.instr <= 30'(32'hfd9fc0ef >> 2);//jal offset -0x3028
    ##2;
    assert(cb.o_d_to_e1.alu_op      == ALU_OP_ADD);
    assert(cb.o_d_to_e1.alu_op1_src == ALU_OP1_SRC_PC);
    assert(cb.o_d_to_e1.alu_op2_src == ALU_OP2_SRC_FOUR);

    //ALU_OP_ADD, 0, rs1
    cb.i_f2_to_d.instr <= 30'(32'h30401073 >> 2);//csrw mie, zero
    ##2;
    assert(cb.o_d_to_e1.alu_op      == ALU_OP_ADD);
    assert(cb.o_d_to_e1.alu_op1_src == ALU_OP1_SRC_ZERO);
    assert(cb.o_d_to_e1.alu_op2_src == ALU_OP2_SRC_RS1);

    //ALU_OP_SUB, rs1, rs2
    cb.i_f2_to_d.instr <= 30'(32'h40208033 >> 2);//sub x0, x1, x2
    ##2;
    assert(cb.o_d_to_e1.alu_op      == ALU_OP_SUB);
    assert(cb.o_d_to_e1.alu_op1_src == ALU_OP1_SRC_RS1);
    assert(cb.o_d_to_e1.alu_op2_src == ALU_OP2_SRC_RS2);

    //ALU_OP_SLL, rs1, imm
    cb.i_f2_to_d.instr <= 30'(32'h00c59513 >> 2);//slli x10, x11, 12
    ##2;
    assert(cb.o_d_to_e1.alu_op      == ALU_OP_SLL);
    assert(cb.o_d_to_e1.alu_op1_src == ALU_OP1_SRC_RS1);
    assert(cb.o_d_to_e1.alu_op2_src == ALU_OP2_SRC_IMM);

    //ALU_OP_SLT, rs1, imm
    cb.i_f2_to_d.instr <= 30'(32'h01ea2513 >> 2);//slti x10, x20, 30
    ##2;
    assert(cb.o_d_to_e1.alu_op      == ALU_OP_SLT);
    assert(cb.o_d_to_e1.alu_op1_src == ALU_OP1_SRC_RS1);
    assert(cb.o_d_to_e1.alu_op2_src == ALU_OP2_SRC_IMM);

    //ALU_OP_SLTU, rs1, rs2
    cb.i_f2_to_d.instr <= 30'(32'h009433b3 >> 2);//sltu x7, x8, x9
    ##2;
    assert(cb.o_d_to_e1.alu_op      == ALU_OP_SLTU);
    assert(cb.o_d_to_e1.alu_op1_src == ALU_OP1_SRC_RS1);
    assert(cb.o_d_to_e1.alu_op2_src == ALU_OP2_SRC_RS2);

    //ALU_OP_SRL, rs1, rs2
    cb.i_f2_to_d.instr <= 30'(32'h00005033 >> 2);//srl x0, x0, x0
    ##2;
    assert(cb.o_d_to_e1.alu_op      == ALU_OP_SRL);
    assert(cb.o_d_to_e1.alu_op1_src == ALU_OP1_SRC_RS1);
    assert(cb.o_d_to_e1.alu_op2_src == ALU_OP2_SRC_RS2);

    //ALU_OP_SRA, rs1, imm
    cb.i_f2_to_d.instr <= 30'(32'h41df5f93 >> 2);//srai x31, x30, 29
    ##2;
    assert(cb.o_d_to_e1.alu_op      == ALU_OP_SRA);
    assert(cb.o_d_to_e1.alu_op1_src == ALU_OP1_SRC_RS1);
    assert(cb.o_d_to_e1.alu_op2_src == ALU_OP2_SRC_IMM);

    //ALU_OP_OR, csr, imm
    cb.i_f2_to_d.instr <= 30'(32'h300ae6f3 >> 2);//csrrsi x13, mstatus, 0b10101
    ##2;
    assert(cb.o_d_to_e1.alu_op      == ALU_OP_OR);
    assert(cb.o_d_to_e1.alu_op1_src == ALU_OP1_SRC_CSR);
    assert(cb.o_d_to_e1.alu_op2_src == ALU_OP2_SRC_IMM);

    //ALU_OP_AND, rs1, imm
    cb.i_f2_to_d.instr <= 30'(32'hedc0f093 >> 2);//andi x1, x1, ~0x123
    ##2;
    assert(cb.o_d_to_e1.alu_op      == ALU_OP_AND);
    assert(cb.o_d_to_e1.alu_op1_src == ALU_OP1_SRC_RS1);
    assert(cb.o_d_to_e1.alu_op2_src == ALU_OP2_SRC_IMM);

    //ALU_OP_MCLR, csr, rs1
    cb.i_f2_to_d.instr <= 30'(32'h301fba73 >> 2);//csrrc x20, misa, x31
    ##2;
    assert(cb.o_d_to_e1.alu_op      == ALU_OP_MCLR);
    assert(cb.o_d_to_e1.alu_op1_src == ALU_OP1_SRC_CSR);
    assert(cb.o_d_to_e1.alu_op2_src == ALU_OP2_SRC_RS1);

    /////////////////////////////////////////
    //Testing rf access and bypassing
    /////////////////////////////////////////

    cb.i_rs1_rdata          <= 32'hAAAAAAAA;
    cb.i_rs2_rdata          <= 32'hBBBBBBBB;
    cb.i_bypass_rs1_rdata   <= 32'hCCCCCCCC;
    cb.i_bypass_rs2_rdata   <= 32'hDDDDDDDD;
    cb.i_bypass_rs1         <= 1'b0;
    cb.i_bypass_rs2         <= 1'b0;
    cb.i_f2_to_d.instr      <= 30'(32'h009433b3 >> 2);//sltu x7, x8, x9
    ##2;
    assert(cb.o_d_to_e1.rd_idx      == 7);
    assert(cb.o_d_to_e1.rs1_idx     == 8);
    assert(cb.o_d_to_e1.rs2_idx     == 9);
    assert(cb.o_d_to_e1.rs1_rdata   == 32'hAAAAAAAA);
    assert(cb.o_d_to_e1.rs2_rdata   == 32'hBBBBBBBB);
    cb.i_bypass_rs1 <= 1'b0;
    cb.i_bypass_rs2 <= 1'b1;
    ##2;
    assert(cb.o_d_to_e1.rs1_rdata   == 32'hAAAAAAAA);
    assert(cb.o_d_to_e1.rs2_rdata   == 32'hDDDDDDDD);
    cb.i_bypass_rs1 <= 1'b1;
    cb.i_bypass_rs2 <= 1'b0;
    ##2;
    assert(cb.o_d_to_e1.rs1_rdata   == 32'hCCCCCCCC);
    assert(cb.o_d_to_e1.rs2_rdata   == 32'hBBBBBBBB);
    cb.i_bypass_rs1 <= 1'b1;
    cb.i_bypass_rs2 <= 1'b1;
    ##2;
    assert(cb.o_d_to_e1.rs1_rdata   == 32'hCCCCCCCC);
    assert(cb.o_d_to_e1.rs2_rdata   == 32'hDDDDDDDD);

    //TODO test other instructions for RF indexes

    /////////////////////////////////////////
    //Testing CSR reads and ctrl signals
    /////////////////////////////////////////

    //CSR micro immediates and index
    cb.i_csr_explicit_rdata <= 32'hABCD1234;
    cb.i_f2_to_d.instr      <= 30'(32'h34417073 >> 2);//csrci mip, 2
    ##2;
    assert(cb.o_csr_explicit_ren    == 1'b1);
    assert(cb.o_d_to_e1.csr_op      == CSR_OP_ACCESS);
    assert(cb.o_d_to_e1.immediate   == 32'h00000002);
    assert(cb.o_d_to_e1.csr_idx     == 12'h344);//mip
    assert(cb.o_d_to_e1.csr_rdata   == 32'hABCD1234);

    //TODO test other CSR indexes

    /////////////////////////////////////////
    //Testing branching
    /////////////////////////////////////////

    cb.i_rs1_rdata          <= 32'h11111111;
    cb.i_rs2_rdata          <= 32'h22222222;
    cb.i_bypass_rs1_rdata   <= 32'h33333333;
    cb.i_bypass_rs2_rdata   <= 32'h44444444;
    cb.i_bypass_rs1         <= 1'b0;
    cb.i_bypass_rs2         <= 1'b0;
    cb.i_f2_to_d.pc_word    <= 30'h1234;
    cb.i_f2_to_d.instr      <= 30'(32'hfc20e6e3 >> 2);//bltu x1, x2, offset -0x34
    ##2;
    assert(cb.o_branch_taken  == 1'b1);
    assert(cb.o_branch_target == (30'h1234 - (32'h34 >> 2)));

    //TODO test other branches, conditional and unconditional

    /////////////////////////////////////////
    //Testing cache management signals
    /////////////////////////////////////////

    //TODO

    /////////////////////////////////////////
    //Testing exceptions
    /////////////////////////////////////////

    //TODO

`endif //VERILATOR

    ##10;
    $finish;
end

endmodule : letc_core_stage_d_tb
