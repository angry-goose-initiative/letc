/*
 * File:    letc_core_stage_decode.sv
 * Brief:   LETC Core Decode Stage
 *
 * Copyright:
 *  Copyright (C) 2023-2024 John Jekel
 *  Copyright (C) 2025 Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_stage_decode
    import letc_pkg::*;
    import letc_core_pkg::*;
    import riscv_pkg::*;
(
    // Clock and reset
    input logic         clk,
    input logic         rst_n,

    // Hazard/backpressure signals
    output logic        d_ready,
    input  logic        d_flush,
    input  logic        d_stall,

    // Register file read ports
    output reg_idx_t    rf_rs1_idx,
    input  word_t       rf_rs1_val,
    output reg_idx_t    rf_rs2_idx,
    input  word_t       rf_rs2_val,

    // CSR port
    output csr_idx_t    csr_de_expl_idx,
    input  word_t       csr_de_expl_rdata,
    input  logic        csr_de_expl_rill,
    input  logic        csr_de_expl_will,

    // TODO signals for exceptions/cache flushing/etc
    // TODO any needed implicitly read CSRs

    // Datapath
    input   logic       f2_to_d_valid,
    input   f2_to_d_s   f2_to_d,

    output  logic       d_to_e_valid,
    output  d_to_e_s    d_to_e
);

/* ------------------------------------------------------------------------------------------------
 * Input Flops
 * --------------------------------------------------------------------------------------------- */

logic ff_in_valid;
always_ff @(posedge clk) begin
    if (!rst_n) begin
        ff_in_valid <= 1'b0;
    end else if (!d_stall) begin
        ff_in_valid <= f2_to_d_valid;
    end
end

f2_to_d_s ff_in;
always_ff @(posedge clk) begin
    if (!d_stall) begin
        ff_in <= f2_to_d;
    end
end

assign d_ready = 1'b1; // The decode stage always takes only a single cycle; no caches here!

logic out_valid;
assign out_valid = ff_in_valid && !d_flush && !d_stall;

/* ------------------------------------------------------------------------------------------------
 * Internal Types
 * --------------------------------------------------------------------------------------------- */

typedef logic [6:0] funct7_t;
typedef logic [2:0] funct3_t;

typedef enum logic [2:0] {
    INSTR_FORMAT_BAD = 3'b000,
    INSTR_FORMAT_R,
    INSTR_FORMAT_I,
    INSTR_FORMAT_S,
    INSTR_FORMAT_B,
    INSTR_FORMAT_U,
    INSTR_FORMAT_J,
    INSTR_FORMAT_SYS
} instr_format_e;

// Enum for non-CSR SYSTEM instructions
typedef enum logic [2:0] {
    SPECIAL_INSTR_NOP = 3'b000,
    SPECIAL_INSTR_ECALL,
    SPECIAL_INSTR_EBREAK,
    SPECIAL_INSTR_SRET,
    SPECIAL_INSTR_MRET,
    SPECIAL_INSTR_WFI,
    SPECIAL_INSTR_SFENCE_VMA
} special_instr_e;

typedef enum logic [1:0] {
    BRANCH_NOP = 2'b00,//Not a branch
    BRANCH_COND,
    BRANCH_JALR,
    BRANCH_JAL
} branch_e;

typedef struct packed {
    logic           illegal_instr;
    special_instr_e special_instr;
    rd_src_e        rd_src;
    logic           rd_we;
    csr_alu_op_e    csr_alu_op;
    logic           csr_expl_ren;
    logic           csr_expl_wen;
    csr_op_src_e    csr_op_src;
    alu_op1_src_e   alu_op1_src;
    alu_op2_src_e   alu_op2_src;
    alu_op_e        alu_op;
    mem_op_e        mem_op;
    logic           mem_signed;
    mem_size_e      mem_size;
    amo_alu_op_e    amo_alu_op;
    branch_e        branch;
    cmp_op_e        cond_branch_cmp_op;
    logic           fence;
} ctrl_s;

/* ------------------------------------------------------------------------------------------------
 * Opcode and Instruction Format Detection
 * --------------------------------------------------------------------------------------------- */

instr_t         instr;
opcode_e        opcode;
instr_format_e  instr_format;

always_comb begin
    instr = ff_in.instr; // For convenience

    opcode = opcode_e'(instr[6:2]);

    // OPCODE_SYSTEM is special: sometimes it acts like R, sometimes like I
    unique case (opcode)
        OPCODE_OP, OPCODE_AMO:          instr_format = INSTR_FORMAT_R;
        OPCODE_LOAD, OPCODE_OP_IMM,
        OPCODE_JALR, OPCODE_MISC_MEM:   instr_format = INSTR_FORMAT_I;
        OPCODE_STORE:                   instr_format = INSTR_FORMAT_S;
        OPCODE_BRANCH:                  instr_format = INSTR_FORMAT_B;
        OPCODE_AUIPC, OPCODE_LUI:       instr_format = INSTR_FORMAT_U;
        OPCODE_JAL:                     instr_format = INSTR_FORMAT_J;
        OPCODE_SYSTEM:                  instr_format = INSTR_FORMAT_SYS;
        default:                        instr_format = INSTR_FORMAT_BAD;
    endcase
end

/* ------------------------------------------------------------------------------------------------
 * Instruction Field Extraction
 * --------------------------------------------------------------------------------------------- */

// Funct fields
funct3_t funct3;
// verilator lint_save
// verilator lint_off UNUSEDSIGNAL
funct7_t funct7;
// verilator lint_restore
always_comb begin
    funct3 = funct3_from_instr(instr);
    funct7 = funct7_from_instr(instr);
end

// Register indexes
reg_idx_t rd_idx, rs1_idx, rs2_idx;
csr_idx_t csr_idx;
always_comb begin
    rd_idx  = rd_idx_from_instr(instr);
    rs1_idx = rs1_idx_from_instr(instr);
    rs2_idx = rs2_idx_from_instr(instr);
    csr_idx = instr[31:20];
end

// Immediates
word_t imm;
always_comb begin
    // Synthesis tool should detect the minimum muxes needed for each bit of
    // the immediate.
    unique case (instr_format)
        INSTR_FORMAT_I:     imm = imm_i_from_instr(instr);
        INSTR_FORMAT_S:     imm = imm_s_from_instr(instr);
        INSTR_FORMAT_B:     imm = imm_b_from_instr(instr);
        INSTR_FORMAT_U:     imm = imm_u_from_instr(instr);
        INSTR_FORMAT_J:     imm = imm_j_from_instr(instr);
        default:            imm = 32'hDEADBEEF;
    endcase
end

csr_zimm_t imm_z;
assign imm_z = 5'(imm_z_from_instr(instr));

/* ------------------------------------------------------------------------------------------------
 * Control Signal Generation
 * --------------------------------------------------------------------------------------------- */

// For instructions that have rd, only set rd_we if rd index is not x0. This
// simplifies forwarding logic and can prevent certain unneeded stalls.
logic rd_is_x0, rs1_is_x0;
assign rd_is_x0 = (rd_idx == 5'h0);
assign rs1_is_x0 = (rs1_idx == 5'h0);

// verilator lint_save
// verilator lint_off UNUSEDSIGNAL
ctrl_s ctrl;
// verilator lint_restore
always_comb begin
    ctrl = '0;
    unique case (opcode)
        OPCODE_OP: begin
            ctrl.rd_src         = RD_SRC_ALU;
            ctrl.rd_we          = !rd_is_x0;
            ctrl.alu_op1_src    = ALU_OP1_SRC_RS1;
            ctrl.alu_op2_src    = ALU_OP2_SRC_RS2;

            unique case (funct3)
                3'b000: ctrl.alu_op = funct7[5] ? ALU_OP_SUB : ALU_OP_ADD;
                3'b001: ctrl.alu_op = ALU_OP_SLL;
                3'b010: ctrl.alu_op = ALU_OP_SLT;
                3'b011: ctrl.alu_op = ALU_OP_SLTU;
                3'b100: ctrl.alu_op = ALU_OP_XOR;
                3'b101: ctrl.alu_op = funct7[5] ? ALU_OP_SRA : ALU_OP_SRL;
                3'b110: ctrl.alu_op = ALU_OP_OR;
                3'b111: ctrl.alu_op = ALU_OP_AND;
            endcase
        end
        OPCODE_AMO: begin
            ctrl.rd_src         = RD_SRC_MEM;
            ctrl.rd_we          = !rd_is_x0;
            ctrl.alu_op1_src    = ALU_OP1_SRC_ZERO;
            ctrl.alu_op2_src    = ALU_OP2_SRC_RS1;
            ctrl.alu_op         = ALU_OP_ADD;
            ctrl.mem_op         = MEM_OP_AMO;
            ctrl.mem_size       = MEM_SIZE_WORD;
            // ctrl.amo_alu_op     = TODO
        end
        OPCODE_LOAD: begin
            ctrl.rd_src         = RD_SRC_MEM;
            ctrl.rd_we          = !rd_is_x0;
            ctrl.alu_op1_src    = ALU_OP1_SRC_RS1;
            ctrl.alu_op2_src    = ALU_OP2_SRC_IMM;
            ctrl.alu_op         = ALU_OP_ADD;
            ctrl.mem_op         = MEM_OP_LOAD;
            ctrl.mem_signed     = !funct3[2];
            ctrl.mem_size       = mem_size_e'(funct3[1:0]);
        end
        OPCODE_OP_IMM: begin
            ctrl.rd_src         = RD_SRC_ALU;
            ctrl.rd_we          = !rd_is_x0;
            ctrl.alu_op1_src    = ALU_OP1_SRC_RS1;
            ctrl.alu_op2_src    = ALU_OP2_SRC_IMM;

            unique case (funct3)
                3'b000: ctrl.alu_op = ALU_OP_ADD;
                3'b001: ctrl.alu_op = ALU_OP_SLL;
                3'b010: ctrl.alu_op = ALU_OP_SLT;
                3'b011: ctrl.alu_op = ALU_OP_SLTU;
                3'b100: ctrl.alu_op = ALU_OP_XOR;
                3'b101: ctrl.alu_op = funct7[5] ? ALU_OP_SRA : ALU_OP_SRL;
                3'b110: ctrl.alu_op = ALU_OP_OR;
                3'b111: ctrl.alu_op = ALU_OP_AND;
            endcase
        end
        OPCODE_JALR: begin
            ctrl.rd_src         = RD_SRC_ALU;
            ctrl.rd_we          = !rd_is_x0;
            ctrl.alu_op1_src    = ALU_OP1_SRC_PC;
            ctrl.alu_op2_src    = ALU_OP2_SRC_FOUR;
            ctrl.alu_op         = ALU_OP_ADD;
            ctrl.branch         = BRANCH_JALR;
        end
        OPCODE_MISC_MEM:
            ctrl.fence = 1'b1; // Flush everything to be safe
        OPCODE_STORE: begin
            ctrl.alu_op1_src    = ALU_OP1_SRC_RS1;
            ctrl.alu_op2_src    = ALU_OP2_SRC_IMM;
            ctrl.alu_op         = ALU_OP_ADD;
            ctrl.mem_op         = MEM_OP_STORE;
            ctrl.mem_size       = mem_size_e'(funct3[1:0]);
        end
        OPCODE_BRANCH: begin
            ctrl.branch                 = BRANCH_COND;
            ctrl.cond_branch_cmp_op     = cmp_op_e'(funct3);
        end
        OPCODE_AUIPC: begin
            ctrl.rd_src         = RD_SRC_ALU;
            ctrl.rd_we          = !rd_is_x0;
            ctrl.alu_op1_src    = ALU_OP1_SRC_PC;
            ctrl.alu_op2_src    = ALU_OP2_SRC_IMM;
            ctrl.alu_op         = ALU_OP_ADD;
        end
        OPCODE_LUI: begin
            ctrl.rd_src         = RD_SRC_ALU;
            ctrl.rd_we          = !rd_is_x0;
            ctrl.alu_op1_src    = ALU_OP1_SRC_ZERO;
            ctrl.alu_op2_src    = ALU_OP2_SRC_IMM;
            ctrl.alu_op         = ALU_OP_ADD;
        end
        OPCODE_JAL: begin
            ctrl.rd_src         = RD_SRC_ALU;
            ctrl.rd_we          = !rd_is_x0;
            ctrl.alu_op1_src    = ALU_OP1_SRC_PC;
            ctrl.alu_op2_src    = ALU_OP2_SRC_FOUR;
            ctrl.alu_op         = ALU_OP_ADD;
            ctrl.branch         = BRANCH_JAL;
        end
        OPCODE_SYSTEM: begin
            unique case (funct3) inside
                3'b000: begin // ECALL, EBREAK, WFI, MRET, SRET, or SFENCE.VMA
                    // TODO also make sure rd is 0 and rs1 is (sometimes) 0
                    unique case(instr[31:20]) inside
                        12'b0000000_00000: ctrl.special_instr = SPECIAL_INSTR_ECALL;
                        12'b0000000_00001: ctrl.special_instr = SPECIAL_INSTR_EBREAK;
                        12'b0001000_00101: ctrl.special_instr = SPECIAL_INSTR_WFI;
                        12'b0011000_00010: ctrl.special_instr = SPECIAL_INSTR_MRET;
                        12'b0001000_00010: ctrl.special_instr = SPECIAL_INSTR_SRET;
                        12'b0001001_?????: ctrl.special_instr = SPECIAL_INSTR_SFENCE_VMA;
                        default: ctrl.illegal_instr = 1'b1;
                    endcase
                end
                3'b?01: begin // CSRRW(I)
                    ctrl.rd_src         = RD_SRC_CSR;
                    ctrl.rd_we          = !rd_is_x0;
                    ctrl.csr_alu_op     = CSR_ALU_OP_PASSTHRU;
                    ctrl.csr_expl_ren   = !rd_is_x0;
                    ctrl.csr_expl_wen   = 1'b1;
                    ctrl.csr_op_src     = funct3[2] ? CSR_OP_SRC_ZIMM : CSR_OP_SRC_RS1;
                end
                3'b?10: begin // CSRRS(I)
                    ctrl.rd_src         = RD_SRC_CSR;
                    ctrl.rd_we          = !rd_is_x0;
                    ctrl.csr_alu_op     = CSR_ALU_OP_BITSET;
                    ctrl.csr_expl_ren   = 1'b1;
                    ctrl.csr_expl_wen   = !rs1_is_x0;
                    ctrl.csr_op_src     = funct3[2] ? CSR_OP_SRC_ZIMM : CSR_OP_SRC_RS1;
                end
                3'b?11: begin // CSRRC(I)
                    ctrl.rd_src         = RD_SRC_CSR;
                    ctrl.rd_we          = !rd_is_x0;
                    ctrl.csr_alu_op     = CSR_ALU_OP_BITCLEAR;
                    ctrl.csr_expl_ren   = 1'b1;
                    ctrl.csr_expl_wen   = !rs1_is_x0;
                    ctrl.csr_op_src     = funct3[2] ? CSR_OP_SRC_ZIMM : CSR_OP_SRC_RS1;
                end
                default: ctrl.illegal_instr = 1'b1;
            endcase
        end
        default: ctrl.illegal_instr = 1'b1;
    endcase
end

/* ------------------------------------------------------------------------------------------------
 * RF/CSRF Port
 * --------------------------------------------------------------------------------------------- */

always_comb begin
    rf_rs1_idx = rs1_idx;
    rf_rs2_idx = rs2_idx;
end

word_t csr_old_val;
always_comb begin
    csr_de_expl_idx = csr_idx;
    csr_old_val     = csr_de_expl_rdata;
end

/* ------------------------------------------------------------------------------------------------
 * Handle Special SYSTEM Instructions
 * --------------------------------------------------------------------------------------------- */

// TODO

/* ------------------------------------------------------------------------------------------------
 * Exception Handling Logic
 * --------------------------------------------------------------------------------------------- */

// TODO: Actually trigger exceptions

// verilator lint_save
// verilator lint_off UNUSEDSIGNAL
logic illegal_instr_exception;
// verilator lint_restore

assign illegal_instr_exception =
    ctrl.illegal_instr
    || (csr_de_expl_rill && ctrl.csr_expl_ren)
    || (csr_de_expl_will && ctrl.csr_expl_wen)
    || instr[1:0] != 2'b11;

/* ------------------------------------------------------------------------------------------------
 * Output to next stage
 * --------------------------------------------------------------------------------------------- */

assign d_to_e = '{
    pc:             ff_in.pc,
    rd_src:         ctrl.rd_src,
    rd_idx:         rd_idx,
    rd_we:          ctrl.rd_we,
    csr_alu_op:     ctrl.csr_alu_op,
    csr_expl_wen:   ctrl.csr_expl_wen,
    csr_op_src:     ctrl.csr_op_src,
    csr_idx:        csr_idx,
    csr_zimm:       imm_z,
    csr_old_val:    csr_old_val,
    rs1_idx:        rs1_idx,
    rs2_idx:        rs2_idx,
    rs1_val:        rf_rs1_val,
    rs2_val:        rf_rs2_val,
    immediate:      imm,
    alu_op1_src:    ctrl.alu_op1_src,
    alu_op2_src:    ctrl.alu_op2_src,
    alu_op:         ctrl.alu_op,
    mem_op:         ctrl.mem_op,
    mem_signed:     ctrl.mem_signed,
    mem_size:       ctrl.mem_size,
    amo_alu_op:     ctrl.amo_alu_op,
    cmp_op:         ctrl.cond_branch_cmp_op
};

assign d_to_e_valid = out_valid;

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

// Note: We don't assume (most) data inputs will be known, but we do have
// assumptions about input control signals

// Assumptions of inputs to the stage
assert property (@(posedge clk) disable iff (!rst_n) !$isunknown(f2_to_d_valid));
assert property (@(posedge clk) disable iff (!rst_n) !$isunknown(d_flush));
assert property (@(posedge clk) disable iff (!rst_n) !$isunknown(d_stall));
assert property (@(posedge clk) disable iff (!rst_n) !(d_flush && d_stall));
assert property (@(posedge clk) disable iff (!rst_n) f2_to_d_valid |-> !$isunknown(f2_to_d.instr));

// Make sure output control signals unguarded by valids (or valids themselves)
// are never unknown
assert property (@(posedge clk) disable iff (!rst_n)
    !rst_n |=> !$isunknown(d_to_e_valid) // Extra |=> needed to deal with the reset
);
assert property (@(posedge clk) disable iff (!rst_n) !$isunknown(d_ready));

// Valid means not unknown and, well, valid for control signals
assert property (@(posedge clk) disable iff (!rst_n) d_to_e_valid |-> !$isunknown(d_to_e));
assert property (@(posedge clk) disable iff (!rst_n)
    d_to_e_valid |-> (d_to_e.mem_op != mem_op_e'(2'b11))
);

assert property (@(posedge clk) disable iff (!rst_n) d_to_e.rd_we |-> !rd_is_x0);

// If stalled then the input should be invalid
assert property (@(posedge clk) disable iff (!rst_n) d_stall |-> !f2_to_d_valid);

// If flushed then the input should be invalid
assert property (@(posedge clk) disable iff (!rst_n) d_flush |-> !f2_to_d_valid);

// Outputs should remain constant if the stage is stalled
assert property (@(posedge clk) disable iff (!rst_n) d_stall |-> $stable(d_ready));
assert property (@(posedge clk) disable iff (!rst_n) d_stall |-> $stable(rf_rs1_idx));
assert property (@(posedge clk) disable iff (!rst_n) d_stall |-> $stable(rf_rs2_idx));
assert property (@(posedge clk) disable iff (!rst_n) d_stall |-> $stable(csr_de_expl_idx));
assert property (@(posedge clk) disable iff (!rst_n) d_stall |-> $stable(d_to_e));

`endif // ifdef SIMULATION

endmodule : letc_core_stage_decode
