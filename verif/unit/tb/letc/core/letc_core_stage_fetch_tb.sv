/**
 * File    letc_core_stage_fetch_tb.sv
 * Brief   Combined testbench for LETC Core fetch stages
 *
 * Copyright:
 *  Copyright (C) 2025 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_stage_fetch_tb;

import riscv_pkg::*;
import letc_pkg::*;
import letc_core_pkg::*;

/* ------------------------------------------------------------------------------------------------
 * Parameters
 * --------------------------------------------------------------------------------------------- */

localparam CLOCK_PERIOD = 10;

/* ------------------------------------------------------------------------------------------------
 * DUT Connections
 * --------------------------------------------------------------------------------------------- */

//verilator lint_save
//verilator lint_off UNUSEDSIGNAL

logic clk;
logic rst_n;

letc_core_imss_if imss_if (.*);

logic     pc_load_en;
pc_word_t pc_load_val;

logic f1_ready, f2_ready;
logic f1_flush, f2_flush;
logic f1_stall, f2_stall;

//Datapath
logic      f1_to_f2_valid;
f1_to_f2_s f1_to_f2;
logic      f2_to_d_valid;
f2_to_d_s  f2_to_d;

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
 * DUTs
 * --------------------------------------------------------------------------------------------- */

letc_core_stage_fetch1 dut1 (.*);
letc_core_stage_fetch2 dut2 (.*);

/* ------------------------------------------------------------------------------------------------
 * Fake IMSS
 * --------------------------------------------------------------------------------------------- */

//Make it smaller else SV2V complains and xsim won't show it in the gui
letc_core_imss #(.SIZE_BYTES(1024)) verif_imss (.*);

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

task reset();
    pc_load_en  <= 1'b0;
    pc_load_val <= '0;
    f1_flush    <= 1'b0;
    f2_flush    <= 1'b0;
    f1_stall    <= 1'b0;
    f2_stall    <= 1'b0;

    rst_n <= 1'b0;
    repeat(2) @(negedge clk);
    rst_n <= 1'b1;
    repeat(2) @(negedge clk);
endtask

task write_imem(word_t addr, word_t data);
    verif_imss.imem[addr    ] <= data[7:0];
    verif_imss.imem[addr + 1] <= data[15:8];
    verif_imss.imem[addr + 2] <= data[23:16];
    verif_imss.imem[addr + 3] <= data[31:24];
endtask

task init_imem();
    write_imem(0, 32'hAAAAAAA << 2);
    write_imem(4, 32'hBBBBBBB << 2);
    write_imem(8, 32'hCCCCCCC << 2);
    write_imem(12, 32'hDDDDDDD << 2);
    write_imem(16, 32'hEEEEEEE << 2);
    write_imem(20, 32'hFFFFFFF << 2);
endtask

//verilator lint_restore

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

initial begin
    //verilator lint_save
    //verilator lint_off INITIALDLY

    //Reset things
    init_imem();
    reset();

    //See if it's fetching things sequentially!
    //assert(f2_to_d.instr == 30'hAAAAAAA);
    @(negedge clk);
    //assert(f2_to_d.instr == 30'hBBBBBBB);
    @(negedge clk);
    //assert(f2_to_d.instr == 30'hCCCCCCC);
    @(negedge clk);
    //assert(f2_to_d.instr == 30'hDDDDDDD);
    @(negedge clk);
    //assert(f2_to_d.instr == 30'hEEEEEEE);
    @(negedge clk);
    //assert(f2_to_d.instr == 30'hFFFFFFF);
    @(negedge clk);

    //TODO

    //Et fini!
    repeat(10) @(negedge clk);
    $finish;

    //verilator lint_restore
end

endmodule : letc_core_stage_fetch_tb
