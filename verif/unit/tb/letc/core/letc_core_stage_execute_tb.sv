/**
 * File    letc_core_stage_execute_tb.sv
 * Brief   Testbench for LETC Core Execute stage
 *
 * Copyright:
 *  Copyright (C) 2024-2025 John Jekel
 *  Copyright (C) 2024 Eric Jessee
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO Longer description
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_stage_execute_tb;

import riscv_pkg::*;
import letc_pkg::*;
import letc_core_pkg::*;

/* ------------------------------------------------------------------------------------------------
 * Parameters:
 *
 * --------------------------------------------------------------------------------------------- */

localparam CLOCK_PERIOD = 10;

/* ------------------------------------------------------------------------------------------------
 * DUT Connections
 * --------------------------------------------------------------------------------------------- */

//verilator lint_save
//verilator lint_off UNUSEDSIGNAL

//Clock and reset
logic clk;
logic rst_n;

//IO
//letc_core_tlb_if dtlb_if(.clk(clk), .rst_n(rst_n));
d_to_e_s d_to_e;
e_to_m_s e_to_m;

/*
//Bypass signals
logic     bypass_rs1;
logic     bypass_rs2;
word_t    bypassed_rs1_data;
word_t    bypassed_rs2_data;


//Hazards
logic o_stage_ready;
logic stage_flush;
logic stage_stall;
*/

//verilator lint_restore

/* ------------------------------------------------------------------------------------------------
 * DUT
 * --------------------------------------------------------------------------------------------- */

letc_core_stage_execute dut (.*);

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

//verilator lint_save
//verilator lint_off INITIALDLY

task original_test_sequence();
    //assign initial values
    //stage_stall <= 1'b0;
    //stage_flush <= 1'b0;
    d_to_e      <= '0;
    //bypass_rs1  <= 1'b0;
    //bypass_rs2  <= 1'b0;

    //reset things
    rst_n <= 1'b0;
    repeat(2) @(negedge clk);

    //let's add 5 and 5 to make a!
    d_to_e.valid        <= 1'b1;
    d_to_e.rs1_rdata    <= 32'h5;
    d_to_e.rs2_rdata    <= 32'h5;
    d_to_e.alu_op1_src  <= ALU_OP1_SRC_RS1;
    d_to_e.alu_op2_src  <= ALU_OP2_SRC_RS2;
    d_to_e.alu_op       <= ALU_OP_ADD;
    @(negedge clk);

    //take the stage out of reset
    rst_n <= 1'b1;
    repeat(2) @(negedge clk);

    //data valid will trigger the alu operation
    d_to_e.valid <= 1'b1;
    @(negedge clk);
    assert(e_to_m.valid         == 1'b1);
    assert(e_to_m.alu_result    == 32'hA);
    d_to_e.valid <= 1'b0;

    //now let's try to subtract an immediate from rs1
    d_to_e.alu_op <= ALU_OP_SUB;
    d_to_e.alu_op2_src <= ALU_OP2_SRC_IMM;
    d_to_e.rs1_rdata <= 32'hf;
    d_to_e.immediate <= 32'h6;
    repeat(2) @(negedge clk);
    d_to_e.valid <= 1'b1;
    @(negedge clk);
    assert(e_to_m.valid         == 1'b1);
    assert(e_to_m.alu_result    == 32'h9);
    d_to_e.valid <= 1'b0;

    //next let's try to increment the program counter
    d_to_e.pc_word <= 30'h100000;
    d_to_e.alu_op <= ALU_OP_ADD;
    d_to_e.alu_op1_src <= ALU_OP1_SRC_PC;
    d_to_e.alu_op2_src <= ALU_OP2_SRC_FOUR;
    repeat(2) @(negedge clk);
    d_to_e.valid <= 1'b1;
    repeat(1) @(negedge clk);
    assert(e_to_m.valid         == 1'b1);
    assert(e_to_m.alu_result    == ({30'h100000, 2'b00} + 32'h4));

    //wait another 5 clock cycles and exit
    repeat(5) @(negedge clk);
endtask

task reset();
    d_to_e <= '0;
    rst_n <= 1'b0;
    repeat(2) @(negedge clk);
    rst_n <= 1'b1;
    repeat(2) @(negedge clk);
endtask

task test_alu();
    //TODO
endtask

task test_branching();
    d_to_e.valid        <= 1'b1;
    d_to_e.rs1_rdata    <= 32'h5;
    d_to_e.rs2_rdata    <= 32'h5;
    d_to_e.cmp_op       <= CMP_OP_EQ;
    @(negedge clk);
    assert(d_to_e.valid == 1'b1);
    assert(e_to_m.branch_taken == 1'b1);

    d_to_e.cmp_op       <= CMP_OP_NE;
    @(negedge clk);
    assert(e_to_m.valid == 1'b1);
    assert(e_to_m.branch_taken == 1'b0);

    d_to_e <= '0;
    @(negedge clk);
endtask

task test_csr_manip();
    d_to_e.valid        <= 1'b1;
    d_to_e.csr_op       <= CSR_OP_RW;
    d_to_e.csr_op_src   <= CSR_OP_SRC_RS1;
    d_to_e.csr_idx      <= 12'hABC;
    d_to_e.csr_rdata    <= 32'hA5A5A5A5;
    d_to_e.rs1_rdata    <= 32'hB4B4B4B4;
    @(negedge clk);
    assert(e_to_m.valid == 1'b1);
    assert(e_to_m.csr_op == CSR_OP_RW);
    assert(e_to_m.csr_idx == 12'hABC);
    assert(e_to_m.old_csr_value == 32'hA5A5A5A5);
    assert(e_to_m.new_csr_value == 32'hB4B4B4B4);
    d_to_e.csr_op       <= CSR_OP_RS;
    @(negedge clk);
    assert(e_to_m.valid == 1'b1);
    assert(e_to_m.csr_op == CSR_OP_RS);
    assert(e_to_m.csr_idx == 12'hABC);
    assert(e_to_m.old_csr_value == 32'hA5A5A5A5);
    assert(e_to_m.new_csr_value == (32'hA5A5A5A5 | 32'hB4B4B4B4));
    d_to_e.csr_op       <= CSR_OP_RC;
    @(negedge clk);
    assert(e_to_m.valid == 1'b1);
    assert(e_to_m.csr_op == CSR_OP_RC);
    assert(e_to_m.csr_idx == 12'hABC);
    assert(e_to_m.old_csr_value == 32'hA5A5A5A5);
    assert(e_to_m.new_csr_value == (32'hA5A5A5A5 & ~32'hB4B4B4B4));

    d_to_e.csr_op       <= CSR_OP_RW;
    d_to_e.csr_op_src   <= CSR_OP_SRC_UIMM;
    d_to_e.csr_uimm     <= 5'h1C;
    @(negedge clk);
    assert(e_to_m.valid == 1'b1);
    assert(e_to_m.csr_op == CSR_OP_RW);
    assert(e_to_m.csr_idx == 12'hABC);
    assert(e_to_m.old_csr_value == 32'hA5A5A5A5);
    assert(e_to_m.new_csr_value == 32'h1C);
    d_to_e.csr_op   <= CSR_OP_RC;
    @(negedge clk);
    assert(e_to_m.valid == 1'b1);
    assert(e_to_m.csr_op == CSR_OP_RC);
    assert(e_to_m.csr_idx == 12'hABC);
    assert(e_to_m.old_csr_value == 32'hA5A5A5A5);
    assert(e_to_m.new_csr_value == (32'hA5A5A5A5 & ~32'h1C));
    d_to_e.csr_op   <= CSR_OP_RS;
    @(negedge clk);
    assert(e_to_m.valid == 1'b1);
    assert(e_to_m.csr_op == CSR_OP_RS);
    assert(e_to_m.csr_idx == 12'hABC);
    assert(e_to_m.old_csr_value == 32'hA5A5A5A5);
    assert(e_to_m.new_csr_value == (32'hA5A5A5A5 | 32'h1C));


    //TODO
endtask

//verilator lint_restore

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

initial begin
    //verilator lint_save
    //verilator lint_off INITIALDLY

    //Run the original test sequence
    original_test_sequence();

    //Reset things again
    reset();

    //Test arithmetic
    test_alu();

    //Test branch comparison
    test_branching();

    //Test csr manipulation
    test_csr_manip();

    //Et fini!
    repeat(10) @(negedge clk);
    $finish;

    //verilator lint_restore
end

endmodule : letc_core_stage_execute_tb
