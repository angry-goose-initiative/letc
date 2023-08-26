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

localparam DEPTH = 2 ** 24;//Should be plenty large for testing purposes

//We just access addresses as-is, without any translation since this is just
//a block-level testbench

//We also have a fixed 1 cycle latency (the minimum that is acceptable for
//core_s1)
//TODO vary the latency randomly in the future

logic [31:0] instruction_memory [DEPTH - 1:0];

always_ff @(posedge clk) begin
    if (mmu_instr_req.valid) begin
        mmu_instr_rsp.instr <= instruction_memory[mmu_instr_req.addr];
        mmu_instr_rsp.ready <= 1'd1;//TODO randomize this (how long it takes in # of clock cycles)
    end else begin//core_s1 shouldn't assume the data will be held if it deasserts valid
        mmu_instr_rsp.instr <= 32'hDEADBEEF;
        mmu_instr_rsp.ready <= 1'd0;
    end
end

assign illegal = 1'd0;

endmodule
