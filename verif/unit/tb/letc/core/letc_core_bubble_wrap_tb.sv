/**
 * File    letc_core_bubble_wrap_tb.sv
 * Brief   TODO
 *
 * Copyright:
 *  Copyright (C) 2025 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_bubble_wrap_tb;

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

//Just used for assertions at the moment
logic clk;
logic rst_n;

logic [NUM_STAGES-1:0] stage_ready;
logic [NUM_STAGES-1:0] stage_flush;
logic [NUM_STAGES-1:0] stage_stall;

logic branch_taken;
//TODO also add exception in writeback signal, which should take precedence over branch_taken

logic [NUM_STAGES-1:0] unforwardable_stage_hazard;

/* ------------------------------------------------------------------------------------------------
 * DUT
 * --------------------------------------------------------------------------------------------- */

letc_core_bubble_wrap dut (.*);

/* ------------------------------------------------------------------------------------------------
 * Clocking
 * --------------------------------------------------------------------------------------------- */

clock_generator #(
    .PERIOD(CLOCK_PERIOD)
) clock_gen_inst (
    .clk(clk)
);

/* ------------------------------------------------------------------------------------------------
 * Clocking
 * --------------------------------------------------------------------------------------------- */

task check_scenario(
    input logic [NUM_STAGES-1:0] new_stage_ready,
    input logic                  new_branch_taken,
    input logic [NUM_STAGES-1:0] new_unforwardable_stage_hazard,
    input logic [NUM_STAGES-1:0] expected_stage_flush,
    input logic [NUM_STAGES-1:0] expected_stage_stall
);
    //verilator lint_save
    //verilator lint_off INITIALDLY

    stage_ready  <= new_stage_ready;
    branch_taken <= new_branch_taken;
    unforwardable_stage_hazard <= new_unforwardable_stage_hazard;
    //verilator lint_restore

    //Using negedge instead of pound delay, even though bubble wrap is combinational
    //so the assertions in bubble wrap are happy :)
    @(negedge clk);

    $display("start check_scenario");
    $display("    stage_ready:                'b%b", new_stage_ready);
    $display("    branch_taken:               'b%b", new_branch_taken);
    $display("    unforwardable_stage_hazard: 'b%b", new_unforwardable_stage_hazard);
    $display("    expected stage_flush:       'b%b", expected_stage_flush);
    $display("    expected stage_stall:       'b%b", expected_stage_stall);
    $display("    actual   stage_flush:       'b%b", stage_flush);
    $display("    actual   stage_stall:       'b%b", stage_stall);
    $display("end check_scenario");

    assert(stage_flush == expected_stage_flush);
    assert(stage_stall == expected_stage_stall);
endtask

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

initial begin
    //verilator lint_save
    //verilator lint_off INITIALDLY
    //verilator lint_off UNUSEDSIGNAL
    int temp;

    //Reset
    rst_n                       <= 1'b0;
    stage_ready                 <= '0;
    branch_taken                <= 1'b0;
    unforwardable_stage_hazard  <= '0;
    @(negedge clk);

    //Testing just backpressure
    check_scenario(
        '1,
        1'b0,
        '0,
        '0,
        '0
    );
    temp = 0;
    for (int ii = 0; ii < NUM_STAGES; ++ii) begin//One backpressured at a time
        temp |= 1 << ii;
        check_scenario(
            (NUM_STAGES)'(~(1 << ii)),
            1'b0,
            '0,
            '0,
            (NUM_STAGES)'(temp)
        );
    end
    for (int ii = 0; ii < 128; ++ii) begin//Iterate through all possible ready signals
        int expected_stall = 0;

        for (int jj = NUM_STAGES - 1; jj >= 0; --jj) begin
            if (!ii[jj]) begin
                expected_stall = (1 << (jj + 1)) - 1;
                break;
            end
        end

        check_scenario(
            (NUM_STAGES)'(ii),
            1'b0,
            '0,
            '0,
            (NUM_STAGES)'(expected_stall)
        );
    end

    //Testing backpressure + branch taken
    check_scenario(
        '1,
        1'b1,
        '0,
        7'b0001111,
        '0
    );
    temp = 0;
    for (int ii = 0; ii < NUM_STAGES; ++ii) begin//One backpressured at a time
        temp |= 1 << ii;
        check_scenario(
            (NUM_STAGES)'(~(1 << ii)),
            1'b1,
            '0,
            7'b0001111,
            (NUM_STAGES)'(temp) & 7'b1110000
        );
    end
    for (int ii = 0; ii < 128; ++ii) begin//Iterate through all possible ready signals
        int expected_stall = 0;

        for (int jj = NUM_STAGES - 1; jj >= 0; --jj) begin
            if (!ii[jj]) begin
                expected_stall = (1 << (jj + 1)) - 1;
                break;
            end
        end

        expected_stall &= (32)'(7'b1110000);

        check_scenario(
            (NUM_STAGES)'(ii),
            1'b1,
            '0,
            7'b0001111,
            (NUM_STAGES)'(expected_stall)
        );
    end

    //Testing random inputs
    for (int ii = 0; ii < 1000; ++ii) begin
        int new_stage_ready                 = $urandom_range(0, 127);
        int new_branch_taken                = $urandom_range(0, 1);
        int new_unforwardable_stage_hazard  = $urandom_range(0, 127);
        int effective_readiness             = new_stage_ready & ~new_unforwardable_stage_hazard;
        int expected_stall = 0;

        for (int jj = NUM_STAGES - 1; jj >= 0; --jj) begin
            if (!effective_readiness[jj]) begin
                expected_stall = (1 << (jj + 1)) - 1;
                break;
            end
        end

        if (new_branch_taken[0]) begin
            expected_stall &= (32)'(7'b1110000);
        end

        check_scenario(
            (NUM_STAGES)'(new_stage_ready),
            (1)'(new_branch_taken),
            (NUM_STAGES)'(new_unforwardable_stage_hazard),
            new_branch_taken[0] ? 7'b0001111 : '0,
            (NUM_STAGES)'(expected_stall)
        );
    end

    repeat (10) @(negedge clk);
    $finish;
    //verilator lint_restore
end

endmodule : letc_core_bubble_wrap_tb
