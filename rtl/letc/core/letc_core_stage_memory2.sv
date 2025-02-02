/**
 * File    letc_core_stage_memory2.sv
 * Brief   LETC Core Memory 2 Stage
 *
 * Copyright:
 *  Copyright (C) 2025 Nick Chan
 *  Copyright (C) 2025 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
*/

module letc_core_stage_memory2
    import letc_pkg::*;
    import letc_core_pkg::*;
    import riscv_pkg::*;
(
    input   logic       clk,
    input   logic       rst_n,

    output  logic       m2_ready,
    input   logic       m2_flush,
    input   logic       m2_stall,

    input   logic       m1_to_m2_valid,
    input   m1_to_m2_s  m1_to_m2,
    output  logic       m2_to_w_valid,
    output  m2_to_w_s   m2_to_w,

    letc_core_dmss_if.memory2 dmss_if
);

logic ff_in_valid;
always_ff @(posedge clk) begin
    if (!rst_n) begin
        ff_in_valid <= 1'b0;
    end else if (!m2_stall) begin
        ff_in_valid <= m1_to_m2_valid;
    end
end

// verilator lint_save
// verilator lint_off UNUSEDSIGNAL
m1_to_m2_s ff_in;
// verilator lint_restore
always_ff @(posedge clk) begin
    if (!m2_stall) begin
        ff_in <= m1_to_m2;
    end
end

assign m2_ready = 1'b1; // TODO: DMSS could cause stall

logic out_valid;
assign out_valid = ff_in_valid && !m2_flush && !m2_stall;

word_t amo_alu_result;
word_t mem_wdata;
word_t mem_rdata;
always_comb begin
    mem_rdata = dmss_if.load_data;
    unique case (ff_in.amo_alu_op)
        AMO_OP_SWAP:    amo_alu_result = ff_in.rs2_val;
        AMO_OP_ADD:     amo_alu_result = mem_rdata + ff_in.rs2_val;
        AMO_OP_AND:     amo_alu_result = mem_rdata & ff_in.rs2_val;
        AMO_OP_OR:      amo_alu_result = mem_rdata | ff_in.rs2_val;
        AMO_OP_XOR:     amo_alu_result = mem_rdata ^ ff_in.rs2_val;
        AMO_OP_MIN:     amo_alu_result = (signed'(mem_rdata) < signed'(ff_in.rs2_val))
                                            ? mem_rdata : ff_in.rs2_val;
        AMO_OP_MAX:     amo_alu_result = (signed'(mem_rdata) > signed'(ff_in.rs2_val))
                                            ? mem_rdata : ff_in.rs2_val;
        AMO_OP_MINU:    amo_alu_result = (mem_rdata < ff_in.rs2_val)
                                            ? mem_rdata : ff_in.rs2_val;
        AMO_OP_MAXU:    amo_alu_result = (mem_rdata > ff_in.rs2_val)
                                            ? mem_rdata : ff_in.rs2_val;
        default:        amo_alu_result = 32'hDEADBEEF;
    endcase
    mem_wdata = (ff_in.mem_op == MEM_OP_AMO) ? amo_alu_result : ff_in.rs2_val;
end

assign m2_to_w_valid = out_valid;
assign m2_to_w = '{
    pc_word:        ff_in.pc_word,
    rd_src:         ff_in.rd_src,
    rd_idx:         ff_in.rd_idx,
    rd_we:          ff_in.rd_we,
    csr_expl_wen:   ff_in.csr_expl_wen,
    csr_idx:        ff_in.csr_idx,
    csr_old_val:    ff_in.csr_old_val,
    csr_new_val:    ff_in.csr_new_val,
    alu_result:     ff_in.alu_result,
    mem_rdata:      dmss_if.load_data,
    mem_op:         ff_in.mem_op,
    mem_size:       ff_in.mem_size,
    mem_wdata:      mem_wdata
};

endmodule : letc_core_stage_memory2
