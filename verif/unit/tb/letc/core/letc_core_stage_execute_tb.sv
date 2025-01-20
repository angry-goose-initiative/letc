/**
 * File    letc_core_stage_e1_tb.sv
 * Brief   Testbench for LETC Core 1st Execute stage
 *
 * Copyright:
 *  Copyright (C) 2024 John Jekel
 *  Copyright (C) 2024 Eric Jessee
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO Longer description
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_stage_e1_tb;

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

//Clock and reset
logic i_clk;
logic i_rst_n;

//IO
letc_core_tlb_if dtlb_if(.i_clk(i_clk), .i_rst_n(i_rst_n));
d_to_e1_s i_d_to_e1;
e1_to_e2_s o_e1_to_e2;

//Bypass signals
logic     i_bypass_rs1;
logic     i_bypass_rs2;
word_t    i_bypassed_rs1_data;
word_t    i_bypassed_rs2_data;


//Hazards
logic o_stage_ready;
logic i_stage_flush;
logic i_stage_stall;

//Debug
logic [7:0] o_debug;

/* ------------------------------------------------------------------------------------------------
 * DUT
 * --------------------------------------------------------------------------------------------- */

letc_core_stage_e1 dut (.*);

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

    output i_rst_n;

    //IO
    output i_d_to_e1;
    input  o_e1_to_e2;

    output i_bypass_rs1;
    output i_bypass_rs2;
    output i_bypassed_rs1_data;
    output i_bypassed_rs2_data;

    //Hazards
    input  o_stage_ready;
    output i_stage_flush;
    output i_stage_stall;

    //Debug
    input  o_debug;

    /* verilator lint_on UNUSEDSIGNAL */
endclocking

/* ------------------------------------------------------------------------------------------------
 * Tasks
 * --------------------------------------------------------------------------------------------- */

//Note: due to quirks with Verilator, sadly we should try to avoid waiting for the next posedge in tasks

task setup();
    //Set initial input states
    cb.i_stage_stall <= 1'b0;
    cb.i_stage_flush <= 1'b0;
    cb.i_d_to_e1.valid <= 1'b0;
    cb.i_bypass_rs1 <= 1'b0;
    cb.i_bypass_rs2 <= 1'b0;
endtask

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

initial begin
    //assign initial values
    setup();
    //reset things
    cb.i_rst_n <= 1'b0;
    //let's add 5 and 5 to make a!
    cb.i_d_to_e1.rs1_rdata <= 32'h5;
    cb.i_d_to_e1.rs2_rdata <= 32'h5;
    cb.i_d_to_e1.alu_op1_src <= ALU_OP1_SRC_RS1;
    cb.i_d_to_e1.alu_op2_src <= ALU_OP2_SRC_RS2;
    cb.i_d_to_e1.alu_op <= ALU_OP_ADD;
    ##2;
    //take the stage out of reset
    cb.i_rst_n <= 1'b1;
    ##2;
    //data valid will trigger the alu operation
    cb.i_d_to_e1.valid <= 1'b1;
    ##1;
    cb.i_d_to_e1.valid <= 1'b0;
    //now let's try to subtract an immediate from rs1
    cb.i_d_to_e1.alu_op <= ALU_OP_SUB;
    cb.i_d_to_e1.alu_op2_src <= ALU_OP2_SRC_IMM;
    cb.i_d_to_e1.rs1_rdata <= 32'hf;
    cb.i_d_to_e1.immediate <= 32'h6;
    ##2;
    cb.i_d_to_e1.valid <= 1'b1;
    ##1;
    cb.i_d_to_e1.valid <= 1'b0;
    //next let's try to increment the program counter
    cb.i_d_to_e1.pc_word <= 32'h100000;
    cb.i_d_to_e1.alu_op <= ALU_OP_ADD;
    cb.i_d_to_e1.alu_op1_src <= ALU_OP1_SRC_PC;
    cb.i_d_to_e1.alu_op2_src <= ALU_OP2_SRC_FOUR;
    #2;
    cb.i_d_to_e1.valid <= 1'b1;
    //wait another 5 clock cycles and exit
    ##5;
    $finish;
end

endmodule : letc_core_stage_e1_tb
