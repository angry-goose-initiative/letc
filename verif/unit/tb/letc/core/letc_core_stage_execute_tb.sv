/**
 * File    letc_core_stage_execute_tb.sv
 * Brief   Testbench for LETC Core Execute stage
 *
 * Copyright:
 *  Copyright (C) 2024-2025 John Jekel
 *  Copyright (C) 2024 Eric Jessee
 *  Copyright (C) 2025 Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
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

//Forwarding logic
letc_core_forwardee_if e_forwardee_rs1();
letc_core_forwardee_if e_forwardee_rs2();

//Hazard/backpressure signals
logic e_ready;
logic e_flush;
logic e_stall;

//From D
logic       d_to_e_valid;
d_to_e_s    d_to_e;

//To M1
logic       e_to_m1_valid;
e_to_m1_s   e_to_m1;

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
    d_to_e      <= '0;

    //reset things
    rst_n <= 1'b0;
    repeat(2) @(negedge clk);

    //let's add 5 and 5 to make a!
    d_to_e_valid        <= 1'b1;
    d_to_e.rs1_val      <= 32'h5;
    d_to_e.rs2_val      <= 32'h5;
    d_to_e.alu_op1_src  <= ALU_OP1_SRC_RS1;
    d_to_e.alu_op2_src  <= ALU_OP2_SRC_RS2;
    d_to_e.alu_op       <= ALU_OP_ADD;
    @(negedge clk);

    //take the stage out of reset
    rst_n <= 1'b1;
    repeat(2) @(negedge clk);

    //data valid will trigger the alu operation
    d_to_e_valid <= 1'b1;
    @(negedge clk);
    assert(e_to_m1_valid        == 1'b1);
    assert(e_to_m1.alu_result   == 32'hA);
    d_to_e_valid <= 1'b0;

    //now let's try to subtract an immediate from rs1
    d_to_e.alu_op <= ALU_OP_SUB;
    d_to_e.alu_op2_src <= ALU_OP2_SRC_IMM;
    d_to_e.rs1_val <= 32'hf;
    d_to_e.immediate <= 32'h6;
    repeat(2) @(negedge clk);
    d_to_e_valid <= 1'b1;
    @(negedge clk);
    assert(e_to_m1_valid        == 1'b1);
    assert(e_to_m1.alu_result   == 32'h9);
    d_to_e_valid <= 1'b0;

    //next let's try to increment the program counter
    d_to_e.pc <= 32'h100000;
    d_to_e.alu_op <= ALU_OP_ADD;
    d_to_e.alu_op1_src <= ALU_OP1_SRC_PC;
    d_to_e.alu_op2_src <= ALU_OP2_SRC_FOUR;
    repeat(2) @(negedge clk);
    d_to_e_valid <= 1'b1;
    repeat(1) @(negedge clk);
    assert(e_to_m1_valid        == 1'b1);
    assert(e_to_m1.alu_result   == (32'h100000 + 32'h4));

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
    d_to_e_valid        <= 1'b1;
    d_to_e.rs1_val      <= 32'h5;
    d_to_e.rs2_val      <= 32'h5;
    d_to_e.branch_type  <= BRANCH_COND;
    d_to_e.cmp_op       <= CMP_OP_EQ;
    @(negedge clk);
    assert(d_to_e_valid == 1'b1);
    assert(e_to_m1.branch_taken == 1'b1);

    d_to_e.cmp_op <= CMP_OP_NE;
    @(negedge clk);
    assert(e_to_m1_valid == 1'b1);
    assert(e_to_m1.branch_taken == 1'b0);

    d_to_e <= '0;

    d_to_e_valid        <= 1'b1;
    d_to_e.branch_type  <= BRANCH_JAL;
    @(negedge clk);
    assert(e_to_m1_valid == 1'b1);
    assert(e_to_m1.branch_taken == 1'b1);

    d_to_e_valid        <= 1'b1;
    d_to_e.branch_type  <= BRANCH_JALR;
    @(negedge clk);
    assert(e_to_m1_valid == 1'b1);
    assert(e_to_m1.branch_taken == 1'b1);

    d_to_e_valid        <= 1'b1;
    d_to_e.branch_type  <= BRANCH_NOP;
    @(negedge clk);
    assert(e_to_m1_valid == 1'b1);
    assert(e_to_m1.branch_taken == 1'b0);

    d_to_e_valid    <= 1'b0;
    d_to_e          <= '0;
    @(negedge clk);
endtask

task test_csr_manip();
    d_to_e_valid        <= 1'b1;
    d_to_e.csr_alu_op   <= CSR_ALU_OP_PASSTHRU;
    d_to_e.csr_op_src   <= CSR_OP_SRC_RS1;
    d_to_e.csr_idx      <= 12'hABC;
    d_to_e.csr_old_val  <= 32'hA5A5A5A5;
    d_to_e.rs1_val      <= 32'hB4B4B4B4;
    @(negedge clk);
    assert(e_to_m1_valid == 1'b1);
    assert(e_to_m1.csr_idx == 12'hABC);
    assert(e_to_m1.csr_old_val == 32'hA5A5A5A5);
    assert(e_to_m1.csr_new_val == 32'hB4B4B4B4);
    d_to_e.csr_alu_op <= CSR_ALU_OP_BITSET;
    @(negedge clk);
    assert(e_to_m1_valid == 1'b1);
    assert(e_to_m1.csr_idx == 12'hABC);
    assert(e_to_m1.csr_old_val == 32'hA5A5A5A5);
    assert(e_to_m1.csr_new_val == (32'hA5A5A5A5 | 32'hB4B4B4B4));
    d_to_e.csr_alu_op <= CSR_ALU_OP_BITCLEAR;
    @(negedge clk);
    assert(e_to_m1_valid == 1'b1);
    assert(e_to_m1.csr_idx == 12'hABC);
    assert(e_to_m1.csr_old_val == 32'hA5A5A5A5);
    assert(e_to_m1.csr_new_val == (32'hA5A5A5A5 & ~32'hB4B4B4B4));

    d_to_e.csr_alu_op   <= CSR_ALU_OP_PASSTHRU;
    d_to_e.csr_op_src   <= CSR_OP_SRC_ZIMM;
    d_to_e.csr_zimm     <= 5'h1C;
    @(negedge clk);
    assert(e_to_m1_valid == 1'b1);
    assert(e_to_m1.csr_idx == 12'hABC);
    assert(e_to_m1.csr_old_val == 32'hA5A5A5A5);
    assert(e_to_m1.csr_new_val == 32'h1C);
    d_to_e.csr_alu_op <= CSR_ALU_OP_BITCLEAR;
    @(negedge clk);
    assert(e_to_m1_valid == 1'b1);
    assert(e_to_m1.csr_idx == 12'hABC);
    assert(e_to_m1.csr_old_val == 32'hA5A5A5A5);
    assert(e_to_m1.csr_new_val == (32'hA5A5A5A5 & ~32'h1C));
    d_to_e.csr_alu_op <= CSR_ALU_OP_BITSET;
    @(negedge clk);
    assert(e_to_m1_valid == 1'b1);
    assert(e_to_m1.csr_idx == 12'hABC);
    assert(e_to_m1.csr_old_val == 32'hA5A5A5A5);
    assert(e_to_m1.csr_new_val == (32'hA5A5A5A5 | 32'h1C));


    //TODO
endtask

//verilator lint_restore

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

initial begin
    //verilator lint_save
    //verilator lint_off INITIALDLY
    e_flush <= 1'b0;
    e_stall <= 1'b0;
    e_forwardee_rs1.use_fwd <= 1'b0;
    e_forwardee_rs2.use_fwd <= 1'b0;
    e_forwardee_rs1.fwd_val <= '0;
    e_forwardee_rs2.fwd_val <= '0;

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
