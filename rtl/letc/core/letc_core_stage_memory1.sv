/**
 * File    letc_core_stage_memory1.sv
 * Brief   LETC Core Memory 1 Stage
 *
 * Copyright:
 *  Copyright (C) 2025 Nick Chan
 *  Copyright (C) 2025 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
*/

module letc_core_stage_memory1
    import letc_pkg::*;
    import letc_core_pkg::*;
    import riscv_pkg::*;
(
    input   logic       clk,
    input   logic       rst_n,

    output  logic       m1_ready,
    input   logic       m1_flush,
    input   logic       m1_stall,

    input   logic       e_to_m1_valid,
    input   e_to_m1_s   e_to_m1,
    output  logic       m1_to_m2_valid,
    output  m1_to_m2_s  m1_to_m2,

    letc_core_dmss_if.memory1 dmss_if
);

logic ff_in_valid;
always_ff @(posedge clk) begin
    if (!rst_n) begin
        ff_in_valid <= 1'b0;
    end else if (!m1_stall) begin
        ff_in_valid <= e_to_m1_valid;
    end
end

// verilator lint_save
// verilator lint_off UNUSEDSIGNAL
e_to_m1_s ff_in;
// verilator lint_restore
always_ff @(posedge clk) begin
    if (!m1_stall) begin
        ff_in <= e_to_m1;
    end
end

assign m1_ready = 1'b1; // TODO: DMSS could cause stall

logic out_valid;
assign out_valid = ff_in_valid && !m1_flush && !m1_stall;

assign dmss_if.load_addr = e_to_m1.alu_result;

assign m1_to_m2_valid = out_valid;
assign m1_to_m2 = '{
    pc:             ff_in.pc,
    rd_src:         ff_in.rd_src,
    rd_idx:         ff_in.rd_idx,
    rd_we:          ff_in.rd_we,
    csr_expl_wen:   ff_in.csr_expl_wen,
    csr_idx:        ff_in.csr_idx,
    csr_old_val:    ff_in.csr_old_val,
    csr_new_val:    ff_in.csr_new_val,
    alu_result:     ff_in.alu_result,
    mem_op:         ff_in.mem_op,
    mem_signed:     ff_in.mem_signed,
    mem_size:       ff_in.mem_size,
    amo_alu_op:     ff_in.amo_alu_op,
    rs2_val:        ff_in.rs2_val
};

endmodule : letc_core_stage_memory1
