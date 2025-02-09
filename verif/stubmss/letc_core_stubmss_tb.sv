/*
 * File:    letc_core_stubmss_tb.sv
 * Brief:   Testbench for letc_core_top with stubbed-out IMSS and DMSS
 *
 * Copyright (C) 2025 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_stubmss_tb;

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

//Clock and reset
logic clk;
logic rst_n;

//IO
axi_if  axi_instr (.i_aclk(clk), .i_arst_n(rst_n));//Won't be used because we stubbed out the MSSes
axi_if  axi_data  (.i_aclk(clk), .i_arst_n(rst_n));//Same here
logic   timer_irq_pending;
logic   external_irq_pending;

//Debug (Logic Analyzer)
logic [7:0]      o_debug;

//verilator lint_restore

/* ------------------------------------------------------------------------------------------------
 * DUT
 * --------------------------------------------------------------------------------------------- */

letc_core_top dut (.*);

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

function string get_test_program_path();
    string test_program_path;
    assert($value$plusargs("TEST_PROGRAM_PATH=%s", test_program_path));
    return test_program_path;
endfunction

function string get_trace_path();
    string trace_path;
    assert($value$plusargs("OUTPUT_TRACE_PATH=%s", trace_path));
    return trace_path;
endfunction

//verilator lint_restore

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

integer trace_file_handle;

initial begin
    //verilator lint_save
    //verilator lint_off INITIALDLY
    timer_irq_pending       <= 1'b0;
    external_irq_pending    <= 1'b0;

    rst_n <= 1'b0;
    repeat(2) @(negedge clk);

    $display("Running test program in stubmss mode: %s", get_test_program_path());
    $readmemh(get_test_program_path(), dut.imss.imem);
    $readmemh(get_test_program_path(), dut.dmss.dmem);

    $display("Saving output trace to: %s", get_trace_path());
    trace_file_handle = $fopen(get_trace_path(), "w");

    rst_n <= 1'b1;

    //The sim exit logic is handled below when we get an IRVE.EXIT instruction
    //verilator lint_restore
end

/* ------------------------------------------------------------------------------------------------
 * Tracing and Exit Logic
 * --------------------------------------------------------------------------------------------- */

always_ff @(posedge clk) begin
    if (rst_n) begin
        //Tracing Logic
        // if (dut.rf_rd_we & (dut.rf_rd_idx != '0)) begin
        //     $fdisplay(trace_file_handle, "[letc_core_rf]: %h was written to register %d", dut.rf_rd_val, dut.rf_rd_idx);
        // end

        if (dut.stage_writeback.ff_in_valid && !dut.stage_writeback.sim_should_exit) begin
            if (dut.rf_rd_we) begin
                $fdisplay(trace_file_handle,
                          "0x%h | 0x%h -> x%0d",
                          dut.stage_writeback.ff_in.pc,
                          dut.rf_rd_val,
                          dut.rf_rd_idx);
            end else begin
                $fdisplay(trace_file_handle, "0x%h", dut.stage_writeback.ff_in.pc);
            end
        end

        //TODO perhaps more tracing in the future?

        //Exit Logic
        if (dut.stage_writeback.sim_should_exit) begin
            $display("Got IRVE.EXIT instruction, exiting simulation...");
            $fclose(trace_file_handle);
            $finish;
        end
    end
end

endmodule : letc_core_stubmss_tb
