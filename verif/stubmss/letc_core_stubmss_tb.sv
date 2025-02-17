/*
 * File:    letc_core_stubmss_tb.sv
 * Brief:   Testbench for letc_core_top with stubbed-out IMSS and DMSS
 *
 * Copyright (C) 2025 John Jekel
 * Copyright (C) 2025 Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
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

localparam MAX_SIM_CYCLES = 1000000;

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

initial begin
    repeat (MAX_SIM_CYCLES) @(posedge clk) begin
        if (rst_n) begin
            //Tracing Logic
            if (dut.stage_writeback.ff_in_valid & !dut.stage_writeback.sim_should_exit) begin
                string msg = $sformatf(
                    "R 0x%h",
                    dut.stage_writeback.ff_in.pc
                );

                if (dut.rf_rd_we) begin
                    msg = {msg, $sformatf(
                        " | RF: 0x%h -> x%0d",
                        dut.rf_rd_val,
                        dut.rf_rd_idx
                    )};
                end
                if (dut.dmss.dmss2_req_store_ff & dut.dmss_if.dmss2_req_commit) begin
                    msg = {msg, $sformatf(
                        " | Mem: 0x%h -> 0x%h",
                        dut.stage_writeback.ff_in.rs2_val,
                        dut.dmss.dmss2_req_addr_ff
                    )};

                    if (dut.dmss.dmss2_req_addr_ff == 32'hFFFFFFFF) begin
                        //TODO also log to a file perhaps?
                        $write("\x1b[1m\x1b[96m%s\x1b[0m", string'(dut.stage_writeback.ff_in.rs2_val));
                    end
                end

                $fdisplay(trace_file_handle, msg);
            end

            //Exit Logic
            if (dut.stage_writeback.sim_should_exit) begin
                $display("Got IRVE.EXIT instruction, exiting simulation...");
                $fclose(trace_file_handle);
                $finish;
            end
        end
    end

    $display("Simulation timed out after %d cycles", MAX_SIM_CYCLES);
    $fclose(trace_file_handle);
    $finish;
end

endmodule : letc_core_stubmss_tb
