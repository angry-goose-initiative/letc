/*
 * File:    letc_core_stage_memory1.sv
 * Brief:   LETC Core Memory 1 Stage
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

    output  logic       branch_taken,
    output  word_t      branch_target,

    input   logic       e_to_m1_valid,
    input   e_to_m1_s   e_to_m1,
    output  logic       m1_to_m2_valid,
    output  m1_to_m2_s  m1_to_m2,

    letc_core_dmss_if.memory1 dmss_if,

    letc_core_forwarder_if.stage m1_forwarder,
    letc_core_forwardee_if.stage m1_forwardee_rs2
);

/* ------------------------------------------------------------------------------------------------
 * Input Flop Stage
 * --------------------------------------------------------------------------------------------- */

logic ff_in_valid;
always_ff @(posedge clk) begin
    if (!rst_n) begin
        ff_in_valid <= 1'b0;
    end else if (!m1_stall) begin
        ff_in_valid <= e_to_m1_valid;
    end
end

e_to_m1_s ff_in;
always_ff @(posedge clk) begin
    if (!m1_stall) begin
        ff_in <= e_to_m1;
    end else begin//We are stalled...
        //But we're currently the recpient of forwarded data, so save it for
        //later in case we lose access as the rest of the pipeline continues onwards
        if (m1_forwardee_rs2.use_fwd) begin
            ff_in.rs2_val <= m1_forwardee_rs2.fwd_val;
        end
    end
end

assign m1_ready = 1'b1;

logic out_valid;
assign out_valid = ff_in_valid && !m1_flush && !m1_stall;

/* ------------------------------------------------------------------------------------------------
 * DMSS
 * --------------------------------------------------------------------------------------------- */

// The DMSS has its own input flops that are at the same point in the pipeline
// as memory 1's input flops, so the input values are passed to the DMSS
// directly (no using ff_in).
assign dmss_if.dmss0_req_addr   = e_to_m1.alu_result;
assign dmss_if.dmss0_req_load   = e_to_m1.mem_op != MEM_OP_NOP;
assign dmss_if.dmss0_req_store  = e_to_m1.mem_op == MEM_OP_STORE;
assign dmss_if.dmss0_req_stall  = m1_stall;

/* ------------------------------------------------------------------------------------------------
 * Forwarding
 * --------------------------------------------------------------------------------------------- */

// Forwarder
always_comb begin
    m1_forwarder.instr_produces_rd = ff_in.rd_we && ff_in_valid;
    m1_forwarder.rd_idx = ff_in.rd_idx;
    m1_forwarder.rd_val_avail = ff_in.mem_op != MEM_OP_LOAD; // FIXME: Account for atomics
    unique case (ff_in.rd_src)
        RD_SRC_ALU: m1_forwarder.rd_val = ff_in.alu_result;
        RD_SRC_CSR: m1_forwarder.rd_val = ff_in.csr_old_val;
        default:    m1_forwarder.rd_val = 32'hDEADBEEF;
    endcase
end

// Forwardee
assign m1_forwardee_rs2.stage_uses_reg = 1'b0;
assign m1_forwardee_rs2.reg_idx = ff_in.rs2_idx;

word_t rs2_val;
assign rs2_val = m1_forwardee_rs2.use_fwd ? m1_forwardee_rs2.fwd_val : ff_in.rs2_val;

/* ------------------------------------------------------------------------------------------------
 * Branching
 * --------------------------------------------------------------------------------------------- */

assign branch_taken     = ff_in_valid && ff_in.branch_taken;
assign branch_target    = ff_in.branch_target;

/* ------------------------------------------------------------------------------------------------
 * Output Connections
 * --------------------------------------------------------------------------------------------- */

always_comb begin
    m1_to_m2_valid = out_valid;
    m1_to_m2 = '{
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
        rs2_idx:        ff_in.rs2_idx,
        alu_result:     ff_in.alu_result,
        mem_op:         ff_in.mem_op,
        mem_signed:     ff_in.mem_signed,
        mem_size:       ff_in.mem_size,
        amo_alu_op:     ff_in.amo_alu_op,
        rs2_val:        rs2_val
    };
end

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

assert property (@(posedge clk) disable iff (!rst_n) (m1_stall || m1_flush) |-> !e_to_m1_valid);

`endif // SIMULATION

endmodule : letc_core_stage_memory1
