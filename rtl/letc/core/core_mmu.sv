/*
 * File:    core_mmu.sv
 * Brief:   The memory management unit
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

`ifdef IMPORTS_IN_MODULE_SCOPE_UNSUPPORTED
import letc_pkg::*;
import core_pkg::*;
`endif

module core_mmu
`ifndef IMPORTS_IN_MODULE_SCOPE_UNSUPPORTED
    import letc_pkg::*;
    import core_pkg::*;
`endif
(
    input   logic   clk,
    input   logic   rst_n,

    //Implicitly read CSRs
    input   word_t  csr_mstatus_ff,
    input   word_t  csr_satp_ff,

    //Connections to s1
    input   mmu_instr_req_s  mmu_instr_req,
    output  mmu_instr_rsp_s  mmu_instr_rsp

    //TODO other ports
);

//TESTING just hooking up directly to an SRAM for now

/*
intel_fpga_sram_generic #(
    .DEPTH(1024),
    .WIDTH(32),
    .OUTPUT_REGISTER(0)
) testing_imem (
    .clk({1'd0, clk}),
    .addr(mmu_instr_req.addr),
    .re(mmu_instr_req.valid),
    .rdata(mmu_instr_rsp.instr),
    .we(2'd0),
    .wdata('0)
);
*/

assign rdata = 32'hDEADBEEF;//TESTING

endmodule : core_mmu
