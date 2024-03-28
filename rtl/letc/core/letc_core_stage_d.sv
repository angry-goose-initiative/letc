/*
 * File:    letc_core_stage_d.sv
 * Brief:   LETC Core Decode Stage
 *
 * Copyright:
 *  Copyright (C) 2023-2024 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_stage_d
    import letc_pkg::*;
    import letc_core_pkg::*;
(
    //Clock and reset
    input logic i_clk,
    input logic i_rst_n,

    //Hazard/backpressure signals
    output logic o_stage_ready,
    input  logic i_stage_flush,
    input  logic i_stage_stall,

    //rs1 Read Port
    output reg_idx_t    o_rs1_idx,//Also goes to TGHM
    input  word_t       i_rs1_rdata,

    //rs2 Read Port
    output reg_idx_t    o_rs2_idx,//Also goes to TGHM
    input  word_t       i_rs2_rdata,

    //Bypass signals
    input logic     i_bypass_rs1,
    input logic     i_bypass_rs2,
    input word_t    i_bypass_rs1_rdata,
    input word_t    i_bypass_rs2_rdata,

    //CSR Read Port
    output logic        o_csr_explicit_ren,
    output csr_idx_t    o_csr_explicit_ridx,
    input  word_t       i_csr_explicit_rdata,
    input  logic        i_csr_explicit_rill,

    //Branch signals
    output logic        o_branch_taken,
    output pc_word_t    o_branch_target,

    //TODO signals for exceptions/cache flushing/etc
    //TODO any needed implicitly read CSRs

    //From F2
    input f2_to_d_s i_f2_to_d,

    //To E1
    output d_to_e1_s o_d_to_e1
);

//TODO in the future detect illegal instructions; not a priority to start with

/* ------------------------------------------------------------------------------------------------
 * Internal Types
 * --------------------------------------------------------------------------------------------- */

typedef logic [6:0] funct7_t;
typedef logic [2:0] funct3_t;

typedef enum logic [4:0] {
    OPCODE_LOAD   = 5'b00000, OPCODE_LOAD_FP    = 5'b00001, OPCODE_CUSTOM_0   = 5'b00010, OPCODE_MISC_MEM = 5'b00011,
    OPCODE_OP_IMM = 5'b00100, OPCODE_AUIPC      = 5'b00101, OPCODE_OP_IMM_32  = 5'b00110, OPCODE_B48_0    = 5'b00111,
    OPCODE_STORE  = 5'b01000, OPCODE_STORE_FP   = 5'b01001, OPCODE_CUSTOM_1   = 5'b01010, OPCODE_AMO      = 5'b01011,
    OPCODE_OP     = 5'b01100, OPCODE_LUI        = 5'b01101, OPCODE_OP_32      = 5'b01110, OPCODE_B64      = 5'b01111,
    OPCODE_MADD   = 5'b10000, OPCODE_MSUB       = 5'b10001, OPCODE_NMSUB      = 5'b10010, OPCODE_NMADD    = 5'b10011,
    OPCODE_OP_FP  = 5'b10100, OPCODE_RESERVED_0 = 5'b10101, OPCODE_CUSTOM_2   = 5'b10110, OPCODE_B48_1    = 5'b10111,
    OPCODE_BRANCH = 5'b11000, OPCODE_JALR       = 5'b11001, OPCODE_RESERVED_1 = 5'b11010, OPCODE_JAL      = 5'b11011,
    OPCODE_SYSTEM = 5'b11100, OPCODE_RESERVED_3 = 5'b11101, OPCODE_CUSTOM_3   = 5'b11110, OPCODE_BGE80    = 5'b11111
} opcode_e;

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

typedef enum logic [2:0] {
    SPECIAL_INSTR_NOP = 3'b000,
    SPECIAL_INSTR_ECALL,
    SPECIAL_INSTR_EBREAK,
    SPECIAL_INSTR_SRET,
    SPECIAL_INSTR_MRET,
    SPECIAL_INSTR_WFI,
    SPECIAL_INSTR_SFENCE_VMA
} special_instr_e;//AKA non CSR SYSTEM instructions

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
    csr_op_e        csr_op;
    alu_op1_src_e   alu_op1_src;
    alu_op2_src_e   alu_op2_src;
    alu_op_e        alu_op;
    mem_op_e        memory_op;
    logic           memory_signed;
    size_e          memory_size;
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
    instr = i_f2_to_d.instr;//For convenience

    opcode = opcode_e'(instr[6:2]);

    unique case (opcode)
        //OPCODE_SYSTEM is special: sometimes it acts like R, sometimes like I
        //TODO will we actually support AMOs in hardware?
        OPCODE_OP/*, OPCODE_AMO*/:                                  instr_format = INSTR_FORMAT_R;
        OPCODE_LOAD, OPCODE_OP_IMM, OPCODE_JALR, OPCODE_MISC_MEM:   instr_format = INSTR_FORMAT_I;
        OPCODE_STORE:                                               instr_format = INSTR_FORMAT_S;
        OPCODE_BRANCH:                                              instr_format = INSTR_FORMAT_B;
        OPCODE_AUIPC, OPCODE_LUI:                                   instr_format = INSTR_FORMAT_U;
        OPCODE_JAL:                                                 instr_format = INSTR_FORMAT_J;
        OPCODE_SYSTEM:                                              instr_format = INSTR_FORMAT_SYS;
        default:                                                    instr_format = INSTR_FORMAT_BAD;
    endcase
end

//TODO check for illegal 16-bit insts, '0, '1, etc (low priority)

/* ------------------------------------------------------------------------------------------------
 * Instruction Field Extraction
 * --------------------------------------------------------------------------------------------- */

//Register indexes
reg_idx_t rd_idx, rs1_idx, rs2_idx;
csr_idx_t csr_idx;
always_comb begin
    rd_idx  = instr[11:7];
    rs1_idx = instr[19:15];
    rs2_idx = instr[24:20];
    csr_idx = instr[31:20];
end

//Funct fields
funct3_t funct3;
funct7_t funct7;
always_comb begin
    funct3 = instr[14:12];
    funct7 = instr[31:25];
end

//Immediates
word_t imm_i, imm_s, imm_b, imm_u, imm_j;
word_t csr_uimm;
word_t muxed_imm_to_e1;
always_comb begin
    imm_i = {{20{instr[31]}}, instr[31:20]};
    imm_s = {{20{instr[31]}}, instr[31:25], instr[11:7]};
    imm_b = {{19{instr[31]}}, instr[31],    instr[7],  instr[30:25], instr[11:8], 1'b0};
    imm_u = {instr[31:12], 12'h000};
    imm_j = {{12{instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0};

    csr_uimm = {27'd0, instr[19:15]};//NOT sign extended

    //Immediate mux based on instruction format for E1
    //Synthesis tool should detect the minimum muxes needed for each bit of the immediate
    //Only the CSR SYSTEM instructions use an immediate, so simply provide it for all SYSTEM instructions
    unique case (instr_format)
        INSTR_FORMAT_I:     muxed_imm_to_e1 = imm_i;
        INSTR_FORMAT_S:     muxed_imm_to_e1 = imm_s;
        //INSTR_FORMAT_B:     muxed_imm_to_e1 = imm_b;//Branch logic in decode uses imm_b directly
        INSTR_FORMAT_U:     muxed_imm_to_e1 = imm_u;
        //INSTR_FORMAT_J:     muxed_imm_to_e1 = imm_j;//Branch logic in decode uses imm_j directly
        INSTR_FORMAT_SYS:   muxed_imm_to_e1 = csr_uimm;
        default:            muxed_imm_to_e1 = 32'hDEADBEEF;
    endcase
end

/* ------------------------------------------------------------------------------------------------
 * Control Signal Generation
 * --------------------------------------------------------------------------------------------- */

ctrl_s ctrl;
always_comb begin
    ctrl = '0;
    unique case (opcode)
        OPCODE_OP: begin
            ctrl.rd_src         = RD_SRC_ALU;
            ctrl.rd_we          = 1'b1;
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
        //OPCODE_AMO://TODO will we actually support this in hardware?
        OPCODE_LOAD: begin
            ctrl.rd_src         = RD_SRC_MEM;
            ctrl.rd_we          = 1'b1;
            ctrl.alu_op1_src    = ALU_OP1_SRC_RS1;
            ctrl.alu_op2_src    = ALU_OP2_SRC_IMM;
            ctrl.alu_op         = ALU_OP_ADD;
            ctrl.memory_op      = MEM_OP_LOAD;
            ctrl.memory_signed  = !funct3[2];
            ctrl.memory_size    = size_e'(funct3[1:0]);
        end
        OPCODE_OP_IMM: begin
            ctrl.rd_src         = RD_SRC_ALU;
            ctrl.rd_we          = 1'b1;
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
            ctrl.rd_we          = 1'b1;
            ctrl.alu_op1_src    = ALU_OP1_SRC_PC;
            ctrl.alu_op2_src    = ALU_OP2_SRC_FOUR;
            ctrl.alu_op         = ALU_OP_ADD;
            ctrl.branch         = BRANCH_JALR;
        end
        OPCODE_MISC_MEM: ctrl.fence = 1'b1;//Flush everything to be safe
        OPCODE_STORE: begin
            ctrl.alu_op1_src    = ALU_OP1_SRC_RS1;
            ctrl.alu_op2_src    = ALU_OP2_SRC_IMM;
            ctrl.alu_op         = ALU_OP_ADD;
            ctrl.memory_op      = MEM_OP_STORE;
            ctrl.memory_size    = size_e'(funct3[1:0]);
        end
        OPCODE_BRANCH: begin
            ctrl.branch                 = BRANCH_COND;
            ctrl.cond_branch_cmp_op     = cmp_op_e'(funct3);
        end
        OPCODE_AUIPC: begin
            ctrl.rd_src         = RD_SRC_ALU;
            ctrl.rd_we          = 1'b1;
            ctrl.alu_op1_src    = ALU_OP1_SRC_PC;
            ctrl.alu_op2_src    = ALU_OP2_SRC_IMM;
            ctrl.alu_op         = ALU_OP_ADD;
        end
        OPCODE_LUI: begin
            ctrl.rd_src         = RD_SRC_ALU;
            ctrl.rd_we          = 1'b1;
            ctrl.alu_op1_src    = ALU_OP1_SRC_ZERO;
            ctrl.alu_op2_src    = ALU_OP2_SRC_IMM;
            ctrl.alu_op         = ALU_OP_ADD;
        end
        OPCODE_JAL: begin
            ctrl.rd_src         = RD_SRC_ALU;
            ctrl.rd_we          = 1'b1;
            ctrl.alu_op1_src    = ALU_OP1_SRC_PC;
            ctrl.alu_op2_src    = ALU_OP2_SRC_FOUR;
            ctrl.alu_op         = ALU_OP_ADD;
            ctrl.branch         = BRANCH_JAL;
        end
        OPCODE_SYSTEM: begin
            unique case (funct3) inside
                3'b000: begin //ECALL, EBREAK, WFI, MRET, SRET, or SFENCE.VMA
                    //TODO also make sure rd is 0 and rs1 is (sometimes) 0
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
                3'b?01: begin//CSRRW(I)
                    ctrl.rd_src         = RD_SRC_CSR;//Old CSR value
                    ctrl.rd_we          = 1'b1;
                    ctrl.alu_op1_src    = ALU_OP1_SRC_ZERO;//So we just pass op2 through
                    ctrl.alu_op2_src    = funct3[2] ? ALU_OP2_SRC_IMM : ALU_OP2_SRC_RS1;
                    ctrl.alu_op         = ALU_OP_ADD;//Just pass op2 through
                    ctrl.csr_op         = CSR_OP_ACCESS;
                end
                3'b?10: begin//CSRRS(I)
                    ctrl.rd_src         = RD_SRC_CSR;//Old CSR value
                    ctrl.rd_we          = 1'b1;
                    ctrl.alu_op1_src    = ALU_OP1_SRC_CSR;
                    ctrl.alu_op2_src    = funct3[2] ? ALU_OP2_SRC_IMM : ALU_OP2_SRC_RS1;
                    ctrl.alu_op         = ALU_OP_OR;//Set bits
                    ctrl.csr_op         = CSR_OP_ACCESS;
                end
                3'b?11: begin//CSRRC(I)
                    ctrl.rd_src         = RD_SRC_CSR;//Old CSR value
                    ctrl.rd_we          = 1'b1;
                    ctrl.alu_op1_src    = ALU_OP1_SRC_CSR;
                    ctrl.alu_op2_src    = funct3[2] ? ALU_OP2_SRC_IMM : ALU_OP2_SRC_RS1;
                    ctrl.alu_op         = ALU_OP_MCLR;//Clear bits
                    ctrl.csr_op         = CSR_OP_ACCESS;
                end
                default: ctrl.illegal_instr = 1'b1;
            endcase
        end
        default: ctrl.illegal_instr = 1'b1;
    endcase
end

/* ------------------------------------------------------------------------------------------------
 * RF Access/CSR Reads
 * --------------------------------------------------------------------------------------------- */

word_t rs1_rdata, rs2_rdata;
always_comb begin
    o_rs1_idx = rs1_idx;
    o_rs2_idx = rs2_idx;

    rs1_rdata = i_bypass_rs1 ? i_bypass_rs1_rdata : i_rs1_rdata;
    rs2_rdata = i_bypass_rs2 ? i_bypass_rs2_rdata : i_rs2_rdata;
end

word_t csr_rdata;
always_comb begin
    //Assumes no read side effects since we don't handle flushing...
    o_csr_explicit_ren  = i_f2_to_d.valid & !i_stage_flush & (ctrl.csr_op == CSR_OP_ACCESS);
    o_csr_explicit_ridx = csr_idx;
    csr_rdata           = i_csr_explicit_rdata;
    //i_csr_explicit_rill//TODO actually cause exception on illegal CSR read (very low priority)
end

/* ------------------------------------------------------------------------------------------------
 * Branch Logic
 * --------------------------------------------------------------------------------------------- */

logic branch_cmp_result;
letc_core_branch_comparator branch_comparator (
    .i_rs1(rs1_rdata),
    .i_rs2(rs2_rdata),
    .i_cmp_operation(ctrl.cond_branch_cmp_op),
    .o_cmp_result(branch_cmp_result)
);

word_t jalr_branch_target;
always_comb begin
    //Per the spec we must do the add, then throw out the lsbs. This handles the case
    //where, for example, the lsbs in both rs1_rdata and imm_i are set, which would overflow
    //and affect the upper bits of the result!
    //Also we must use an intermediate for this since (rs1_rdata + imm_i)[31:2] isn't legal
    jalr_branch_target = rs1_rdata + imm_i;
end

always_comb begin
    //TODO catch misaligned branches
    o_branch_taken  = 1'b0;
    o_branch_target = 30'hDEADBEE;

    if (i_f2_to_d.valid & !i_stage_flush) begin
        unique0 case (ctrl.branch)
            BRANCH_COND: begin
                o_branch_taken  = i_f2_to_d.valid & branch_cmp_result;
                o_branch_target = i_f2_to_d.pc_word + imm_b[31:2];
            end
            BRANCH_JALR: begin
                o_branch_taken  = i_f2_to_d.valid;
                o_branch_target = jalr_branch_target[31:2];
            end
            BRANCH_JAL: begin
                o_branch_taken  = i_f2_to_d.valid;
                o_branch_target = i_f2_to_d.pc_word + imm_j[31:2];
            end
        endcase
    end
end

/* ------------------------------------------------------------------------------------------------
 * Handle Special SYSTEM Instructions
 * --------------------------------------------------------------------------------------------- */

//TODO

/* ------------------------------------------------------------------------------------------------
 * Exception Handling Logic
 * --------------------------------------------------------------------------------------------- */

//TODO

/* ------------------------------------------------------------------------------------------------
 * Output Flop Stage
 * --------------------------------------------------------------------------------------------- */

assign o_stage_ready = 1'b1;//The decode stage always takes only a single cycle; no caches here!

always_ff @(posedge i_clk) begin
    if (!i_rst_n) begin
        o_d_to_e1.valid <= 1'b0;
    end else begin
        if (i_stage_flush) begin
            o_d_to_e1.valid <= 1'b0;
        end else if (!i_stage_stall) begin
            o_d_to_e1.valid <= i_f2_to_d.valid;//Again, the decode stage always takes one cycle
        end
    end
end

always_ff @(posedge i_clk) begin
    //Save resources by not resetting the datapath; which is fine since `valid` above is reset
    //if (i_f2_to_d.valid & !i_stage_stall) begin//More power efficient but worse for timing and area
    if (!i_stage_stall) begin
        o_d_to_e1.pc_word <= i_f2_to_d.pc_word;

        o_d_to_e1.rd_src <= ctrl.rd_src;
        o_d_to_e1.rd_idx <= rd_idx;
        o_d_to_e1.rd_we  <= ctrl.rd_we;

        o_d_to_e1.csr_op    <= ctrl.csr_op;
        o_d_to_e1.csr_idx   <= csr_idx;
        o_d_to_e1.csr_rdata <= csr_rdata;

        o_d_to_e1.rs1_idx   <= rs1_idx;
        o_d_to_e1.rs2_idx   <= rs2_idx;
        o_d_to_e1.rs1_rdata <= rs1_rdata;
        o_d_to_e1.rs2_rdata <= rs2_rdata;

        o_d_to_e1.immediate <= muxed_imm_to_e1;

        o_d_to_e1.alu_op1_src <= ctrl.alu_op1_src;
        o_d_to_e1.alu_op2_src <= ctrl.alu_op2_src;
        o_d_to_e1.alu_op      <= ctrl.alu_op;

        o_d_to_e1.memory_op     <= ctrl.memory_op;
        o_d_to_e1.memory_signed <= ctrl.memory_signed;
        o_d_to_e1.memory_size   <= ctrl.memory_size;
    end
end

/* ------------------------------------------------------------------------------------------------
 * Assertions
 * --------------------------------------------------------------------------------------------- */

`ifdef SIMULATION

//Note: We don't assume (most) data inputs will be known, but we do have assumptions about input control signals

//Assumptions of inputs to the stage
assert property (@(posedge i_clk) disable iff (!i_rst_n) !$isunknown(i_f2_to_d.valid));
assert property (@(posedge i_clk) disable iff (!i_rst_n) !$isunknown(i_stage_flush));
assert property (@(posedge i_clk) disable iff (!i_rst_n) !$isunknown(i_stage_stall));
assert property (@(posedge i_clk) disable iff (!i_rst_n) !(i_stage_flush && i_stage_stall));
assert property (@(posedge i_clk) disable iff (!i_rst_n) i_f2_to_d.valid |-> !$isunknown(i_f2_to_d.instr));
assert property (@(posedge i_clk) disable iff (!i_rst_n) o_csr_explicit_ren |-> !$isunknown(i_csr_explicit_rill));

//Make sure output control signals unguarded by valids (or valids themselves) are never unknown
assert property (@(posedge i_clk) disable iff (!i_rst_n)
    !i_rst_n |=> !$isunknown(o_d_to_e1.valid)//Extra |=> needed to deal with the reset
);
`ifndef XSIM
//FIXME why is o_stage_ready unknown in XSIM, but 1'b1 in Verilator and VSIM (letc_core_tb only)?
assert property (@(posedge i_clk) disable iff (!i_rst_n) !$isunknown(o_stage_ready));
`endif //XSIM
assert property (@(posedge i_clk) disable iff (!i_rst_n) !$isunknown(o_csr_explicit_ren));
assert property (@(posedge i_clk) disable iff (!i_rst_n)
    (!$isunknown(rs1_rdata) && !$isunknown(rs2_rdata)) |-> !$isunknown(o_branch_taken)
);

//Valid means not unknown and, well, valid for control signals
assert property (@(posedge i_clk) disable iff (!i_rst_n) o_d_to_e1.valid |-> !$isunknown(o_d_to_e1.rd_we));
assert property (@(posedge i_clk) disable iff (!i_rst_n) o_d_to_e1.valid |-> !$isunknown(o_d_to_e1.csr_op));
assert property (@(posedge i_clk) disable iff (!i_rst_n) o_d_to_e1.valid |-> !$isunknown(o_d_to_e1.memory_op));
assert property (@(posedge i_clk) disable iff (!i_rst_n) o_d_to_e1.valid |-> (o_d_to_e1.memory_op != mem_op_e'(2'b11)));

//Outputs should remain constant if the stage is stalled (assumed stage before this also gets stalled)
assert property (@(posedge i_clk) disable iff (!i_rst_n) i_stage_stall |-> $stable(o_d_to_e1));
assert property (@(posedge i_clk) disable iff (!i_rst_n) i_stage_stall |-> $stable(o_stage_ready));
assert property (@(posedge i_clk) disable iff (!i_rst_n) i_stage_stall |-> $stable(o_csr_explicit_ren));
assert property (@(posedge i_clk) disable iff (!i_rst_n) i_stage_stall |-> $stable(o_csr_explicit_ridx));
assert property (@(posedge i_clk) disable iff (!i_rst_n) i_stage_stall |-> $stable(o_branch_taken));
assert property (@(posedge i_clk) disable iff (!i_rst_n) i_stage_stall |-> $stable(o_branch_target));
assert property (@(posedge i_clk) disable iff (!i_rst_n) i_stage_stall |-> $stable(o_rs1_idx));
assert property (@(posedge i_clk) disable iff (!i_rst_n) i_stage_stall |-> $stable(o_rs2_idx));

`endif //SIMULATION

endmodule : letc_core_stage_d
