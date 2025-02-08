/*
 * File:    letc_core_stage_execute.sv
 * Brief:   LETC Core Execute Stage
 *
 * Copyright:
 *  Copyright (C) 2024-2025 John Jekel
 *  Copytight (C) 2024 Eric Jessee
 *  Copytight (C) 2025 Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_stage_execute
    import riscv_pkg::*;
    import letc_pkg::*;
    import letc_core_pkg::*;
(
    //Clock and reset
    input logic clk,
    input logic rst_n,

    //Forwarding logic
    letc_core_forwardee_if.stage e_forwardee_rs1,
    letc_core_forwardee_if.stage e_forwardee_rs2,

    //Hazard/backpressure signals
    output logic e_ready,
    input  logic e_flush,
    input  logic e_stall,

    //From D
    input   logic       d_to_e_valid,
    input   d_to_e_s    d_to_e,

    //To M1
    output  logic       e_to_m1_valid,
    output  e_to_m1_s   e_to_m1
);

assign e_ready = 1'b1; // TODO: Will not be ready during multicycle multiply

/* ------------------------------------------------------------------------------------------------
 * Input Flop Stage
 * --------------------------------------------------------------------------------------------- */

logic    ff_in_valid;
d_to_e_s ff_in;

always_ff @(posedge clk) begin
    if (!rst_n) begin
        ff_in_valid <= 1'b0;
    end else begin
        if (!e_stall) begin
            ff_in_valid <= d_to_e_valid;
        end
    end
end

always_ff @(posedge clk) begin
    if (!e_stall) begin
        ff_in <= d_to_e;
    end
end

/* ------------------------------------------------------------------------------------------------
 * Forwarding
 * --------------------------------------------------------------------------------------------- */

assign e_forwardee_rs1.reg_idx_valid = ff_in_valid;//TODO should this be qualified with flush or stall as well?
assign e_forwardee_rs2.reg_idx_valid = ff_in_valid;//TODO should this be qualified with flush or stall as well?

assign e_forwardee_rs1.reg_idx = ff_in.rs1_idx;
assign e_forwardee_rs2.reg_idx = ff_in.rs2_idx;

word_t rs1_val;
word_t rs2_val;
always_comb begin
    rs1_val = e_forwardee_rs1.use_fwd ? e_forwardee_rs1.fwd_val : ff_in.rs1_val;
    rs2_val = e_forwardee_rs2.use_fwd ? e_forwardee_rs2.fwd_val : ff_in.rs2_val;
end

/* ------------------------------------------------------------------------------------------------
 * Arithmetic
 * --------------------------------------------------------------------------------------------- */

//ALU
word_t  [1:0]   alu_operands;
alu_op_e        alu_operation;
word_t          alu_result;

letc_core_alu alu (.*);

//ALU connections
//op1
always_comb begin
    unique case (ff_in.alu_op1_src)
        ALU_OP1_SRC_RS1:  alu_operands[0] = rs1_val;
        ALU_OP1_SRC_PC:   alu_operands[0] = ff_in.pc;
        ALU_OP1_SRC_CSR:  alu_operands[0] = ff_in.csr_old_val;
        ALU_OP1_SRC_ZERO: alu_operands[0] = 32'h0;
    endcase
end
//op2
always_comb begin
    unique case (ff_in.alu_op2_src)
        ALU_OP2_SRC_RS1:  alu_operands[1] = rs1_val;
        ALU_OP2_SRC_RS2:  alu_operands[1] = rs2_val;
        ALU_OP2_SRC_IMM:  alu_operands[1] = ff_in.immediate;
        ALU_OP2_SRC_FOUR: alu_operands[1] = 32'h4;
    endcase
end
//operation
always_comb begin
    alu_operation = ff_in.alu_op;
end

/* ------------------------------------------------------------------------------------------------
 * Branch Logic
 * --------------------------------------------------------------------------------------------- */

//Branch Comparator
logic cmp_result;

letc_core_branch_comparator branch_comparator (
    .cmp_operation(ff_in.cmp_op),
    .*
);

/* ------------------------------------------------------------------------------------------------
 * CSR Updating Logic
 * --------------------------------------------------------------------------------------------- */

//CSR Operand Mux
word_t csr_operand;
always_comb begin
    unique case (ff_in.csr_op_src)
        CSR_OP_SRC_RS1:     csr_operand = rs1_val;
        CSR_OP_SRC_ZIMM:    csr_operand = {27'h0, ff_in.csr_zimm};
        default:            csr_operand = 32'hDEADBEEF;
    endcase
end

//Modify the CSR value
word_t csr_new_val;
always_comb begin
    unique case (ff_in.csr_alu_op)
        CSR_ALU_OP_PASSTHRU:    csr_new_val = csr_operand;
        CSR_ALU_OP_BITSET:      csr_new_val = ff_in.csr_old_val |  csr_operand;
        CSR_ALU_OP_BITCLEAR:    csr_new_val = ff_in.csr_old_val & ~csr_operand;
        default:                csr_new_val = 32'hDEADBEEF;
    endcase
end

/* ------------------------------------------------------------------------------------------------
 * Output Connections
 * --------------------------------------------------------------------------------------------- */

always_comb begin
    e_to_m1_valid = ff_in_valid && !e_flush && !e_stall;

    e_to_m1 = '{
        pc:             ff_in.pc,
        rd_src:         ff_in.rd_src,
        rd_idx:         ff_in.rd_idx,
        rd_we:          ff_in.rd_we,
        csr_expl_wen:   ff_in.csr_expl_wen,
        csr_idx:        ff_in.csr_idx,
        csr_old_val:    ff_in.csr_old_val,
        csr_new_val:    csr_new_val,
        rs1_idx:        ff_in.rs1_idx,
        rs2_idx:        ff_in.rs2_idx,
        alu_result:     alu_result,
        mem_op:         ff_in.mem_op,
        mem_signed:     ff_in.mem_signed,
        mem_size:       ff_in.mem_size,
        amo_alu_op:     ff_in.amo_alu_op,
        rs2_val:        rs2_val,
`ifdef SIMULATION
        sim_exit_req:   ff_in.sim_exit_req,
`endif
        branch_taken:   cmp_result
    };
end

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

//Control signals should always be known out of reset
assert property (@(posedge clk) disable iff (!rst_n) !$isunknown(d_to_e_valid));
assert property (@(posedge clk) disable iff (!rst_n) !$isunknown(e_to_m1_valid));
assert property (@(posedge clk) disable iff (!rst_n) !$isunknown(e_ready));
assert property (@(posedge clk) disable iff (!rst_n) !$isunknown(e_flush));
assert property (@(posedge clk) disable iff (!rst_n) !$isunknown(e_stall));

//Valid qualified signals should be known
assert property (@(posedge clk) disable iff (!rst_n) d_to_e_valid  |-> !$isunknown(d_to_e));
assert property (@(posedge clk) disable iff (!rst_n) e_to_m1_valid |-> !$isunknown(e_to_m1));
assert property (@(posedge clk) disable iff (!rst_n) ff_in_valid   |-> !$isunknown(ff_in));

//If we're not ready, adhesive should stall us (loopback)
assert property (@(posedge clk) disable iff (!rst_n) !e_ready |-> e_stall);

//Outputs should stay stable when we're stalled
assert property (@(posedge clk) disable iff (!rst_n) e_stall |-> $stable(e_to_m1));

//Flushing and stalling a stage at the same time is likely a logic bug in adhesive
assert property (@(posedge clk) disable iff (!rst_n) !(e_flush & e_stall));

`endif //SIMULATION

endmodule : letc_core_stage_execute
