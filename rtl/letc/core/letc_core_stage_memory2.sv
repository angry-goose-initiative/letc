/*
 * File:    letc_core_stage_memory2.sv
 * Brief:   LETC Core Memory 2 Stage
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

    letc_core_dmss_if.memory2 dmss_if,

    letc_core_forwarder_if.stage m2_forwarder,
    letc_core_forwardee_if.stage m2_forwardee_rs2
);

/* ------------------------------------------------------------------------------------------------
 * Input Flop Stage
 * --------------------------------------------------------------------------------------------- */

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
    end else begin//We are stalled...
        //But we're currently the recpient of forwarded data, so save it for
        //later in case we lose access as the rest of the pipeline continues onwards
        if (m2_forwardee_rs2.use_fwd) begin
            ff_in.rs2_val <= m2_forwardee_rs2.fwd_val;
        end
    end
end

assign m2_ready = dmss_if.dmss1_rsp_ready || ff_in.mem_op == MEM_OP_NOP || !ff_in_valid;

logic out_valid;
assign out_valid = ff_in_valid && !m2_flush && !m2_stall;

/* ------------------------------------------------------------------------------------------------
 * Forwarding
 * --------------------------------------------------------------------------------------------- */

// Forwarder
always_comb begin
    m2_forwarder.instr_produces_rd = ff_in.rd_we && ff_in_valid;
    m2_forwarder.rd_idx = ff_in.rd_idx;
    m2_forwarder.rd_val_avail = ff_in.mem_op != MEM_OP_LOAD; // FIXME: Account for atomics
    unique case (ff_in.rd_src)
        RD_SRC_ALU: m2_forwarder.rd_val = ff_in.alu_result;
        RD_SRC_CSR: m2_forwarder.rd_val = ff_in.csr_old_val;
        default:    m2_forwarder.rd_val = 32'hDEADBEEF;
    endcase
end

// Forwardee
assign m2_forwardee_rs2.stage_uses_reg = 1'b0;
assign m2_forwardee_rs2.reg_idx = ff_in.rs2_idx;

word_t rs2_val;
assign rs2_val = m2_forwardee_rs2.use_fwd ? m2_forwardee_rs2.fwd_val : ff_in.rs2_val;

/* ------------------------------------------------------------------------------------------------
 * DMSS
 * --------------------------------------------------------------------------------------------- */

word_t mem_rdata;

word_t loaded_word;
halfword_t loaded_hw;
byte_t loaded_byte;
logic extend_bit_hw;
logic extend_bit_byte;

always_comb begin
    loaded_word = dmss_if.dmss1_rsp_load_data;
    loaded_hw   = ff_in.alu_result[1] ? loaded_word[31:16] : loaded_word[15:0];
    loaded_byte = ff_in.alu_result[0] ? loaded_hw[15:8] : loaded_hw[7:0];
    extend_bit_hw = loaded_hw[15] & ff_in.mem_signed;
    extend_bit_byte = loaded_byte[7] & ff_in.mem_signed;
    if (ff_in.mem_op == MEM_OP_LOAD) begin
        unique case (ff_in.mem_size)
            MEM_SIZE_BYTE:      mem_rdata = {{24{extend_bit_byte}}, loaded_byte};
            MEM_SIZE_HALFWORD:  mem_rdata = {{16{extend_bit_hw}}, loaded_hw};
            default:            mem_rdata = loaded_word;
        endcase
    end else begin
        mem_rdata = loaded_word;
    end
end

/* ------------------------------------------------------------------------------------------------
 * AMO ALU
 * --------------------------------------------------------------------------------------------- */

// TODO: This will live in writeback
/*
word_t amo_alu_result;
word_t mem_wdata;
word_t mem_rdata;
always_comb begin
    mem_rdata = dmss_if.dmss1_rsp_load_data;
    unique case (ff_in.amo_alu_op)
        AMO_OP_SWAP:    amo_alu_result = rs2_val;
        AMO_OP_ADD:     amo_alu_result = mem_rdata + rs2_val;
        AMO_OP_AND:     amo_alu_result = mem_rdata & rs2_val;
        AMO_OP_OR:      amo_alu_result = mem_rdata | rs2_val;
        AMO_OP_XOR:     amo_alu_result = mem_rdata ^ rs2_val;
        AMO_OP_MIN:     amo_alu_result = (signed'(mem_rdata) < signed'(rs2_val))
                                            ? mem_rdata : rs2_val;
        AMO_OP_MAX:     amo_alu_result = (signed'(mem_rdata) > signed'(rs2_val))
                                            ? mem_rdata : rs2_val;
        AMO_OP_MINU:    amo_alu_result = (mem_rdata < rs2_val)
                                            ? mem_rdata : rs2_val;
        AMO_OP_MAXU:    amo_alu_result = (mem_rdata > rs2_val)
                                            ? mem_rdata : rs2_val;
        default:        amo_alu_result = 32'hDEADBEEF;
    endcase
    mem_wdata = (ff_in.mem_op == MEM_OP_AMO) ? amo_alu_result : rs2_val;
end
*/

/* ------------------------------------------------------------------------------------------------
 * Output Connections
 * --------------------------------------------------------------------------------------------- */

always_comb begin
    m2_to_w_valid = out_valid;
    m2_to_w = '{
`ifdef SIMULATION
        sim_exit_req:   ff_in.sim_exit_req,
`endif // SIMULATION
        pc:             ff_in.pc,
        rd_src:         ff_in.rd_src,
        rd_idx:         ff_in.rd_idx,
        rd_we:          ff_in.rd_we,
        csr_expl_wen:   ff_in.csr_expl_wen,
        csr_idx:        ff_in.csr_idx,
        csr_old_val:    ff_in.csr_old_val,
        csr_new_val:    ff_in.csr_new_val,
        alu_result:     ff_in.alu_result,
        mem_rdata:      mem_rdata,
        mem_op:         ff_in.mem_op,
        mem_size:       ff_in.mem_size,
        rs2_val:        rs2_val
    };
end

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

assert property (@(posedge clk) disable iff (!rst_n) (m2_stall || m2_flush) |-> !m1_to_m2_valid);

`endif // SIMULATION

endmodule : letc_core_stage_memory2
