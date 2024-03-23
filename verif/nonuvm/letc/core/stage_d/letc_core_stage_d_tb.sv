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
endclocking

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

initial begin
    //Setup
    cb.i_stage_flush        <= 1'b0;
    cb.i_stage_stall        <= 1'b0;
    cb.i_csr_explicit_rill  <= 1'b0;
    cb.i_f2_to_d.valid      <= 1'b0;

    //Reset things
    cb.i_rst_n <= 1'b0;
    ##2;
    cb.i_rst_n <= 1'b1;
    ##2;

    /////////////////////////////////////////
    //Testing immediate generation
    /////////////////////////////////////////

`ifndef VERILATOR //Something is causing problems in Verilator, but works fine in xsim

    //TODO test more that stress sign extension

    //lw a5, 360(s1)
    cb.i_f2_to_d.valid <= 1'b1;
    cb.i_f2_to_d.instr <= 32'h1684a783 >> 2;
    ##2;//Once cycle for clocking block, one for the decode stage
    assert(cb.o_d_to_e1.immediate == 32'd360);

    //sw ra, 12(sp)
    cb.i_f2_to_d.valid <= 1'b1;
    cb.i_f2_to_d.instr <= 32'h00112623 >> 2;
    ##2;//Once cycle for clocking block, one for the decode stage
    assert(cb.o_d_to_e1.immediate == 32'd12);

    //beqz a5, offset 0x14
    cb.i_f2_to_d.valid <= 1'b1;
    cb.i_f2_to_d.instr <= 32'h00078a63 >> 2;
    ##2;//Once cycle for clocking block, one for the decode stage
    assert(cb.o_d_to_e1.immediate == 32'h00000014);

    //lui a5, 0x6
    cb.i_f2_to_d.valid <= 1'b1;
    cb.i_f2_to_d.instr <= 32'h000067b7 >> 2;
    ##2;//Once cycle for clocking block, one for the decode stage
    assert(cb.o_d_to_e1.immediate == 32'h00006000);

    //jal offset -0x3028
    cb.i_f2_to_d.valid <= 1'b1;
    cb.i_f2_to_d.instr <= 32'hfd9fc0ef >> 2;
    ##2;//Once cycle for clocking block, one for the decode stage
    assert(cb.o_d_to_e1.immediate == 32'hffffcfd8);

    //csrci mip, 2
    cb.i_f2_to_d.valid <= 1'b1;
    cb.i_f2_to_d.instr <= 32'h34417073 >> 2;
    ##2;//Once cycle for clocking block, one for the decode stage
    assert(cb.o_d_to_e1.immediate == 32'h00000002);
    assert(cb.o_d_to_e1.csr_idx == 32'h00000344);//mip

`endif //VERILATOR

    //TODO other decode tests more

    ##10;
    $finish;
end

endmodule : letc_core_stage_d_tb
