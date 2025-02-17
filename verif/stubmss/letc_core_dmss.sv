/*
 * File:    letc_core_dmss.sv
 * Brief:   Stubbed LETC Core Data Memory Subsystem
 *
 * Copyright:
 *  Copyright (C) 2025 Nick Chan
 *  Copyright (C) 2025 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_dmss
    import riscv_pkg::*;
    import letc_pkg::*;
    import letc_core_pkg::*;
#(
    parameter int SIZE_BYTES = 64 * (1 << 20) // 64 MiB, like IRVE
) (
    input logic clk,
    input logic rst_n,

    letc_core_dmss_if.subsystem dmss_if
);

//TODO support virtual memory with this stubbed variant in the future

//For now, just treat virtual and physical addresses the same
byte_t dmem [SIZE_BYTES-1:0];

/* ------------------------------------------------------------------------------------------------
 * First Stage (In line with M1 kinda sorta)
 * --------------------------------------------------------------------------------------------- */

logic dmss0_req_load_ff, dmss0_req_store_ff;
vaddr_t dmss0_req_addr_ff;

always_ff @(posedge clk) begin
    if (!rst_n) begin
        dmss0_req_load_ff  <= 1'b0;
        dmss0_req_store_ff <= 1'b0;
        dmss1_req_addr_ff  <= 32'hDEADBEEF;
    end else begin
        if (!dmss_if.dmss0_req_stall) begin
            dmss0_req_load_ff  <= dmss_if.dmss0_req_load;
            dmss0_req_store_ff <= dmss_if.dmss0_req_store;
            dmss0_req_addr_ff  <= dmss_if.dmss0_req_addr;
        end
    end
end

/* ------------------------------------------------------------------------------------------------
 * Second Stage (In line with M2)
 * --------------------------------------------------------------------------------------------- */

logic load_conflict_with_store;

logic dmss1_req_load_ff, dmss1_req_store_ff;
paddr_t dmss1_req_addr_ff;

//This stage cannot be stalled externally, only when a load conflicts with a store
always_ff @(posedge clk) begin
    if (!rst_n) begin
        dmss1_req_load_ff  <= 1'b0;
        dmss1_req_store_ff <= 1'b0;
        dmss1_req_addr_ff  <= 32'hDEADBEEF;
    end else begin
        if (!load_conflict_with_store) begin
            dmss1_req_load_ff  <= dmss0_req_load_ff;
            dmss1_req_store_ff <= dmss0_req_store_ff;
            dmss1_req_addr_ff  <= dmss0_req_addr_ff;
        end
    end
end

word_t dmss1_req_word_addr;
assign dmss1_req_word_addr = {dmss1_req_addr_ff[31:2], 2'b00};

always_comb begin
    if (load_conflict_with_store) begin
        dmss_if.dmss1_rsp_load_data = 32'hDEADBEEF;
    end else begin
        dmss_if.dmss1_rsp_load_data = {//Little endian
            dmem[dmss1_req_word_addr + 3],//Using dmss1_req_word_addr so this stays in the same stage while still being
            dmem[dmss1_req_word_addr + 2],//combinational (we don't have to worry about timing since this doesn't
            dmem[dmss1_req_word_addr + 1],//synthesize)
            dmem[dmss1_req_word_addr]
        };
    end
end

//Stubmss doesn't actually implement a cache, so this is the only possible stall
assign dmss_if.dmss1_rsp_ready = !load_conflict_with_store;

/* ------------------------------------------------------------------------------------------------
 * Third Stage (In line with WB)
 * --------------------------------------------------------------------------------------------- */

logic /*dmss2_req_load_ff, */ dmss2_req_store_ff;
paddr_t dmss2_req_addr_ff;

//No stalling this stage
always_ff @(posedge clk) begin
    if (!rst_n) begin
        //dmss2_req_load_ff  <= 1'b0;
        dmss2_req_store_ff <= 1'b0;
        dmss2_req_addr_ff  <= 32'hDEADBEEF;
    end else begin
        //dmss2_req_load_ff  <= dmss1_req_load_ff;
        dmss2_req_store_ff <= dmss1_req_store_ff;
        dmss2_req_addr_ff  <= dmss1_req_addr_ff;
    end
end

word_t dmss2_req_word_addr;
assign dmss2_req_word_addr = {dmss2_req_addr_ff[31:2], 2'b00};

//Detecting store conflicts
assign load_conflict_with_store =
    dmss1_req_load_ff && dmss2_req_store_ff && (dmss1_req_word_addr == dmss2_req_word_addr);

//Actual storing
always_ff @(posedge clk) begin
    if (dmss2_req_store_ff & dmss_if.dmss2_req_commit) begin
        //Little endian
        dmem[dmss2_req_word_addr]     <= dmss_if.dmss2_req_store_data[7:0];
        dmem[dmss2_req_word_addr + 1] <= dmss_if.dmss2_req_store_data[15:8];
        dmem[dmss2_req_word_addr + 2] <= dmss_if.dmss2_req_store_data[23:16];
        dmem[dmss2_req_word_addr + 3] <= dmss_if.dmss2_req_store_data[31:24];
    end
end

endmodule : letc_core_dmss
