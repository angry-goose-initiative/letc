/*
 * File:    core_s1_tb.sv
 * Brief:   TODO
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

module core_s1_tb();

logic clk;
logic rst_n;

logic                       halt_req;
logic                       s2_busy;

core_pkg::s1_to_s2_s        s1_to_s2;
core_pkg::s2_to_s1_s        s2_to_s1;

core_pkg::mmu_instr_req_s   mmu_instr_req;
core_pkg::mmu_instr_rsp_s   mmu_instr_rsp;

letc_pkg::word_t            trap_target_addr;
logic                       trap_occurred;

core_s1 dut(.*);

initial begin
    $display("Starting core_s1_tb!");
    $dumpfile(`CORE_S1_TB_DUMPFILE_PATH);
    $dumpvars(0, firsttb);

    clk = 1'b0;

    //We expect a negedge on reset
    rst_n = 1'b1;
    #1 rst_n = 1'b0;
    #1 rst_n = 1'b1;

    repeat(1000) begin
        #1 clk = ~clk;
    end

    $display("Bye bye!");
    $finish;
end

endmodule
