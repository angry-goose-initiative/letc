/*
 * File:    letc_core_imss.sv
 * Brief:   Stubbed LETC Core Instruction Memory Subsystem
 *
 * Copyright:
 *  Copyright (C) 2025 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_imss
    import riscv_pkg::*;
    import letc_pkg::*;
    import letc_core_pkg::*;
#(
    parameter int SIZE_BYTES = 64 * (1 << 20) //64 MiB, like IRVE
) (
    //Clock and reset
    input logic clk,
    input logic rst_n,

    //Stage <-> Memory Subsystem
    letc_core_imss_if.subsystem imss_if

    //TODO others (CSR accesses, etc)
);

//TODO support virtual memory with this stubbed variant in the future
//For now, just treat virtual and physical addresses the same

//It is expected the testbench will reach in and initialize this
//verilator lint_save
//verilator lint_off UNDRIVEN
byte_t imem [SIZE_BYTES-1:0];
//verilator lint_restore

//Service requests "combinationally"
logic  rsp_valid;
logic  rsp_illegal;
word_t rsp_virtual_addr;
word_t rsp_data;

assign rsp_valid        = imss_if.req_valid;
assign rsp_illegal      = 1'b0;
assign rsp_virtual_addr = imss_if.req_virtual_addr;
assign rsp_data         = {//Little endian
    imem[rsp_virtual_addr + 3],
    imem[rsp_virtual_addr + 2],
    imem[rsp_virtual_addr + 1],
    imem[rsp_virtual_addr]
};

//Delay by two cycles to match hardware
logic  rsp_valid_ff;
logic  rsp_illegal_ff;
word_t rsp_virtual_addr_ff;
word_t rsp_data_ff;
always_ff @(posedge clk) begin
    if (!rst_n) begin
        rsp_valid_ff        <= 1'b0;
        imss_if.rsp_valid   <= 1'b0;
    end else begin
        rsp_valid_ff        <= rsp_valid;
        rsp_illegal_ff      <= rsp_illegal;
        rsp_virtual_addr_ff <= rsp_virtual_addr;
        rsp_data_ff         <= rsp_data;

        if (!imss_if.req_stall2) begin
            imss_if.rsp_valid           <= rsp_valid_ff;
            imss_if.rsp_illegal         <= rsp_illegal_ff;
            imss_if.rsp_virtual_addr    <= rsp_virtual_addr_ff;
            imss_if.rsp_data            <= rsp_data_ff;
        end
    end
end

endmodule : letc_core_imss
