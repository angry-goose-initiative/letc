/**
 * File    letc_core_stage_decode_tb.sv
 * Brief   Testing the LETC core decode stage
 *
 * Copyright:
 *  Copyright (C) 2024 John Jekel
 *  Copyright (C) 2025 Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
*/

// verilator lint_save
// verilator lint_off UNUSEDSIGNAL

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_stage_decode_tb;

import letc_pkg::*;
import letc_core_pkg::*;
import riscv_pkg::*;

/* ------------------------------------------------------------------------------------------------
 * Parameters
 * --------------------------------------------------------------------------------------------- */

localparam CLOCK_PERIOD = 10;

/* ------------------------------------------------------------------------------------------------
 * DUT Connections
 * --------------------------------------------------------------------------------------------- */

logic       clk;
logic       rst_n;
logic       stage_ready;
logic       stage_flush;
logic       stage_stall;
reg_idx_t   rf_rs1_idx;
word_t      rf_rs1_val;
reg_idx_t   rf_rs2_idx;
word_t      rf_rs2_val;
csr_idx_t   csr_de_expl_idx;
word_t      csr_de_expl_rdata;
logic       csr_de_expl_rill;
logic       csr_de_expl_will;
logic       f2_to_d_valid;
f2_to_d_s   f2_to_d;
logic       d_to_e_valid;
d_to_e_s    d_to_e;

/* ------------------------------------------------------------------------------------------------
 * DUT
 * --------------------------------------------------------------------------------------------- */

letc_core_stage_decode dut (.*);

/* ------------------------------------------------------------------------------------------------
 * Clocking
 * --------------------------------------------------------------------------------------------- */

clock_generator #(
    .PERIOD(CLOCK_PERIOD)
) clock_gen_inst (
    .clk(clk)
);

/* ------------------------------------------------------------------------------------------------
 * Tasks
 * --------------------------------------------------------------------------------------------- */

task test_instr_op(
    input   string      assembly,
    input   word_t      instr,
    input   logic       expected_rd_we,
    input   alu_op_e    expected_alu_op
);
    $display("Testing op instruction: %s", assembly);
    f2_to_d.instr = instr;
    @(negedge clk);
    assert(d_to_e.rd_src        == RD_SRC_ALU);
    assert(d_to_e.rd_we         == expected_rd_we);
    assert(d_to_e.csr_expl_wen  == 1'b0);
    assert(d_to_e.alu_op        == expected_alu_op);
    assert(d_to_e.alu_op1_src   == ALU_OP1_SRC_RS1);
    assert(d_to_e.alu_op2_src   == ALU_OP2_SRC_RS2);
    assert(d_to_e.memory_op     == MEM_OP_NOP);
endtask

task test_instr_op_imm(
    input   string      assembly,
    input   instr_t     instr,
    input   logic       expected_rd_we,
    input   word_t      expected_immediate,
    input   alu_op_e    expected_alu_op
);
    $display("Testing op_imm instruction: %s", assembly);
    f2_to_d.instr = instr;
    @(negedge clk);
    assert(d_to_e.rd_src        == RD_SRC_ALU);
    assert(d_to_e.rd_we         == expected_rd_we);
    assert(d_to_e.csr_expl_wen  == 1'b0);
    assert(d_to_e.immediate     == expected_immediate);
    assert(d_to_e.alu_op        == expected_alu_op);
    assert(d_to_e.alu_op1_src   == ALU_OP1_SRC_RS1);
    assert(d_to_e.alu_op2_src   == ALU_OP2_SRC_IMM);
    assert(d_to_e.memory_op     == MEM_OP_NOP);
endtask

task test_instr_load(
    input   string  assembly,
    input   instr_t instr,
    input   logic   expected_rd_we,
    input   word_t  expected_immediate,
    input   logic   expected_signed,
    input   size_e  expected_size
);
    $display("Testing load instruction: %s", assembly);
    f2_to_d.instr = instr;
    @(negedge clk);
    assert(d_to_e.rd_src        == RD_SRC_MEM);
    assert(d_to_e.rd_we         == expected_rd_we);
    assert(d_to_e.csr_expl_wen  == 1'b0);
    assert(d_to_e.immediate     == expected_immediate);
    assert(d_to_e.alu_op        == ALU_OP_ADD);
    assert(d_to_e.alu_op1_src   == ALU_OP1_SRC_RS1);
    assert(d_to_e.alu_op2_src   == ALU_OP2_SRC_IMM);
    assert(d_to_e.memory_op     == MEM_OP_LOAD);
    assert(d_to_e.memory_signed == expected_signed);
    assert(d_to_e.memory_size   == expected_size);
endtask

task test_instr_csr(
    input   string          assembly,
    input   instr_t         instr,
    input   logic           expected_rd_we,
    input   csr_alu_op_e    expected_csr_alu_op,
    input   logic           expected_csr_expl_wen,
    input   csr_op_src_e    expected_csr_op_src
);
    $display("Testing csr instruction: %s", assembly);
    f2_to_d.instr = instr;
    @(negedge clk);
    assert(d_to_e.rd_src        == RD_SRC_CSR);
    assert(d_to_e.rd_we         == expected_rd_we);
    assert(d_to_e.csr_alu_op    == expected_csr_alu_op);
    assert(d_to_e.csr_expl_wen  == expected_csr_expl_wen);
    assert(d_to_e.csr_op_src    == expected_csr_op_src);
    assert(d_to_e.memory_op     == MEM_OP_NOP);
endtask

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

logic in_valid;
assign f2_to_d_valid = in_valid;
logic out_valid;
assign out_valid = d_to_e_valid;

logic ff_out_valid;
always_ff @(posedge clk) begin
    ff_out_valid <= out_valid;
end

initial begin
    // Setup
    stage_flush         = 1'b0;
    stage_stall         = 1'b0;
    csr_de_expl_rill    = 1'b0;
    csr_de_expl_will    = 1'b0;
    f2_to_d             = '0;

    // Reset things
    rst_n = 1'b0;
    @(negedge clk);
    rst_n = 1'b1;
    @(negedge clk);

    /////////////////////////////////////////
    // Testing valid signal timing
    /////////////////////////////////////////

    in_valid = 1'b1;
    @(negedge clk);
    assert(out_valid);

    in_valid = 1'b0;
    @(negedge clk);
    assert(!out_valid);

    in_valid = 1'b1;
    @(negedge clk);
    assert(out_valid);

    // Stall
    stage_stall = 1'b1;
    in_valid = 1'b0;
    @(negedge clk);
    assert(!out_valid);

    // Resume
    stage_stall = 1'b0;
    in_valid = 1'b1;
    @(negedge clk);
    assert(ff_out_valid);
    assert(out_valid);

    // Flush
    stage_flush = 1'b1;
    in_valid = 1'b0;
    @(negedge clk);
    assert(!out_valid);

    // Deassert flush
    stage_flush = 1'b0;
    in_valid = 1'b1;
    @(negedge clk);
    assert(!ff_out_valid);
    assert(out_valid);

    // ---------- Register file -----------------------------------------------
    rf_rs1_val      = 32'hAAAAAAAA;
    rf_rs2_val      = 32'hBBBBBBBB;
    f2_to_d.instr   = 32'h009433b3; // sltu x7, x8, x9
    @(negedge clk);
    assert(d_to_e.rd_idx    == 7);
    assert(d_to_e.rs1_idx   == 8);
    assert(d_to_e.rs2_idx   == 9);
    assert(d_to_e.rs1_val   == 32'hAAAAAAAA);
    assert(d_to_e.rs2_val   == 32'hBBBBBBBB);

    // ---------- OP ----------------------------------------------------------
    test_instr_op(
        .assembly("sltu x7, x8, x9"),
        .instr(32'h009433b3),
        .expected_rd_we(1'b1),
        .expected_alu_op(ALU_OP_SLTU)
    );
    test_instr_op(
        .assembly("srl x0, x0, x0"),
        .instr(32'h00005033),
        .expected_rd_we(1'b0),
        .expected_alu_op(ALU_OP_SRL)
    );

    // ---------- OP_IMM ------------------------------------------------------
    test_instr_op_imm(
        .assembly("addi t0, gp, -123"),
        .instr(32'hf8518293),
        .expected_rd_we(1'b1),
        .expected_immediate(32'hffffff85),
        .expected_alu_op(ALU_OP_ADD)
    );
    test_instr_op_imm(
        .assembly("andi x1, x2, -2048"),
        .instr(32'h80017093),
        .expected_rd_we(1'b1),
        .expected_immediate(-32'd2048),
        .expected_alu_op(ALU_OP_AND)
    );
    test_instr_op_imm(
        .assembly("ori x0, x0, 2047"),
        .instr(32'h7ff06013),
        .expected_rd_we(1'b0),
        .expected_immediate(32'd2047),
        .expected_alu_op(ALU_OP_OR)
    );
    test_instr_op_imm(
        .assembly("slti x10, x20, 30"),
        .instr(32'h01ea2513),
        .expected_rd_we(1'b1),
        .expected_immediate(32'd30),
        .expected_alu_op(ALU_OP_SLT)
    );
    test_instr_op_imm(
        .assembly("slli x10, x11, 12"),
        .instr(32'h00c59513),
        .expected_rd_we(1'b1),
        .expected_immediate(32'd12),
        .expected_alu_op(ALU_OP_SLL)
    );
    test_instr_op_imm(
        .assembly("srai x31, x30, 29"),
        .instr(32'h41df5f93),
        .expected_rd_we(1'b1),
        .expected_immediate(32'd29 | 32'h400),
        .expected_alu_op(ALU_OP_SRA)
    );

    // ---------- LOAD --------------------------------------------------------
    test_instr_load(
        .assembly("lbu a5, 360(s1)"),
        .instr(32'h1684c783),
        .expected_rd_we(1'b1),
        .expected_immediate(32'd360),
        .expected_signed(1'b0),
        .expected_size(SIZE_BYTE)
    );

    // ---------- STORE -------------------------------------------------------

    // S-type instructions
    f2_to_d.instr = 32'h00112623; // sw ra, 12(sp)
    @(negedge clk);
    assert(d_to_e.immediate   == 32'd12);
    assert(d_to_e.rd_we       == 1'b0);
    assert(d_to_e.memory_op   == MEM_OP_STORE);
    assert(d_to_e.memory_size == SIZE_WORD);
    f2_to_d.instr = 32'he2489c23; // sh tp, -456(a7)
    @(negedge clk);
    assert(d_to_e.immediate     == 32'hfffffe38);
    assert(d_to_e.rd_we         == 1'b0);
    assert(d_to_e.memory_op     == MEM_OP_STORE);
    assert(d_to_e.memory_size   == SIZE_HALFWORD);

    // ---------- BRANCH ------------------------------------------------------

    // // B-type instructions
    // f2_to_d.instr = 32'h00078a63; // beqz a5, offset 0x14
    // @(negedge clk);
    // assert(d_to_e.immediate == 32'h00000014);
    // assert(d_to_e.rd_we     == 1'b0);
    // assert(d_to_e.memory_op == MEM_OP_NOP);
    // f2_to_d.instr = 32'hfc20e6e3; // bltu x1, x2, offset -0x34
    // @(negedge clk);
    // assert(d_to_e.immediate == 32'hffffffcc);
    // assert(d_to_e.rd_we     == 1'b0);
    // assert(d_to_e.memory_op == MEM_OP_NOP);

    // // U-type instructions
    // f2_to_d.instr = 32'h000067b7; // lui a5, 0x6
    // @(negedge clk);
    // assert(d_to_e.immediate == 32'h00006000);
    // assert(d_to_e.rd_we     == 1'b1);
    // assert(d_to_e.rd_src    == RD_SRC_ALU);
    // assert(d_to_e.memory_op == MEM_OP_NOP);
    // f2_to_d.instr = 32'habcd1117; // auipc sp, 0xabcd1
    // @(negedge clk);
    // assert(d_to_e.immediate == 32'habcd1000);
    // assert(d_to_e.rd_we     == 1'b1);
    // assert(d_to_e.rd_src    == RD_SRC_ALU);
    // assert(d_to_e.memory_op == MEM_OP_NOP);

    // // J-type instructions
    // f2_to_d.instr = 32'hfd9fc0ef; // jal offset -0x3028
    // @(negedge clk);
    // assert(d_to_e.immediate == 32'hffffcfd8);
    // assert(d_to_e.rd_we     == 1'b1);
    // assert(d_to_e.rd_src    == RD_SRC_ALU);
    // assert(d_to_e.memory_op == MEM_OP_NOP);
    // f2_to_d.instr = 32'h0040006f; // jal x0 offset +4
    // @(negedge clk);
    // assert(d_to_e.immediate == 32'h4);
    // assert(d_to_e.rd_we     == 1'b0);
    // assert(d_to_e.rd_src    == RD_SRC_ALU);
    // assert(d_to_e.memory_op == MEM_OP_NOP);

    // ---------- CSR ---------------------------------------------------------

    test_instr_csr(
        .assembly("csrw mie, zero"),
        .instr(32'h30401073),
        .expected_rd_we(1'b0),
        .expected_csr_alu_op(CSR_ALU_OP_PASSTHRU),
        .expected_csr_expl_wen(1'b1),
        .expected_csr_op_src(CSR_OP_SRC_RS1)
    );

    test_instr_csr(
        .assembly("csrrsi x13, mstatus, 0b10101"),
        .instr(32'h300ae6f3),
        .expected_rd_we(1'b1),
        .expected_csr_alu_op(CSR_ALU_OP_BITSET),
        .expected_csr_expl_wen(1'b1),
        .expected_csr_op_src(CSR_OP_SRC_RS1)
    );

    test_instr_csr(
        .assembly("csrrci mip, 2"),
        .instr(32'h34417073),
        .expected_rd_we(1'b0),
        .expected_csr_alu_op(CSR_ALU_OP_BITCLEAR),
        .expected_csr_expl_wen(1'b1),
        .expected_csr_op_src(CSR_OP_SRC_UIMM)
    );

    f2_to_d.instr = 32'h301fba73; // csrrc x20, misa, x31

    // ---------- AMO ---------------------------------------------------------

    // TODO


    // f2_to_d.instr = 32'h0007b197; // auipc x3, 123
    // @(negedge clk);
    // assert(d_to_e.alu_op      == ALU_OP_ADD);
    // assert(d_to_e.alu_op1_src == ALU_OP1_SRC_PC);
    // assert(d_to_e.alu_op2_src == ALU_OP2_SRC_IMM);

    // f2_to_d.instr = 32'h0cafe2b7; // lui t0, 0xcafe
    // @(negedge clk);
    // assert(d_to_e.alu_op      == ALU_OP_ADD);
    // assert(d_to_e.alu_op1_src == ALU_OP1_SRC_ZERO);
    // assert(d_to_e.alu_op2_src == ALU_OP2_SRC_IMM);

    // f2_to_d.instr = 32'hfd9fc0ef; // jal offset -0x3028
    // @(negedge clk);
    // assert(d_to_e.alu_op      == ALU_OP_ADD);
    // assert(d_to_e.alu_op1_src == ALU_OP1_SRC_PC);
    // assert(d_to_e.alu_op2_src == ALU_OP2_SRC_FOUR);

    // /////////////////////////////////////////
    // //Testing CSR reads and ctrl signals
    // /////////////////////////////////////////

    // //CSR micro immediates and index
    // csr_de_expl_rdata   = 32'hABCD1234;
    // f2_to_d.instr       = 32'h34417073; // csrci mip, 2
    // @(negedge clk);
    // // assert(csr_expl_ren   == 1'b1);
    // // assert(d_to_e.csr_op      == CSR_OP_ACCESS);
    // assert(d_to_e.csr_zimm    == 5'd2);
    // assert(d_to_e.csr_idx     == 12'h344);//mip
    // assert(d_to_e.csr_rdata   == 32'hABCD1234);

    /////////////////////////////////////////
    //Testing cache management signals
    /////////////////////////////////////////

    // TODO

    /////////////////////////////////////////
    //Testing exceptions
    /////////////////////////////////////////

    // TODO

    repeat(10) @(negedge clk);
    $finish;
end

endmodule : letc_core_stage_decode_tb
