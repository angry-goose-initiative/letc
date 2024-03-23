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

    //TODO

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

    //CSR Read Port
    output logic        o_csr_explicit_ren,
    output csr_idx_t    o_csr_explicit_ridx,
    input  word_t       i_csr_explicit_rdata,
    input  logic        i_csr_explicit_rill,

    //Branch signals
    output logic        o_branch_taken,
    output pc_word_t    o_branch_target,

    //From F2
    input f2_to_d_s i_f2_to_d,

    //To E1
    output d_to_e1_s o_d_to_e1
);

//TODO in the future detect illegal instructions; not a priority to start with

/* ------------------------------------------------------------------------------------------------
 * Internal Types
 * --------------------------------------------------------------------------------------------- */

typedef logic [6:0]     funct7_t;
typedef logic [2:0]     funct3_t;

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
    INSTR_FORMAT_R, INSTR_FORMAT_I, INSTR_FORMAT_S,   INSTR_FORMAT_B,
    INSTR_FORMAT_U, INSTR_FORMAT_J, INSTR_FORMAT_SYS, INSTR_FORMAT_BAD
} instr_format_e;

/* ------------------------------------------------------------------------------------------------
 * Opcode and Instruction Format Detection
 * --------------------------------------------------------------------------------------------- */

instr_t         instr;
opcode_e        opcode;
instr_format_e  instr_format;

always_comb begin
    instr = i_f2_to_d.instr;

    opcode = opcode_e'(instr[6:2]);

    unique case (opcode)
        //OPCODE_SYSTEM is special: sometimes it acts like R, sometimes like I
        OPCODE_OP, OPCODE_AMO:                                      instr_format = INSTR_FORMAT_R;
        OPCODE_LOAD, OPCODE_OP_IMM, OPCODE_JALR, OPCODE_MISC_MEM:   instr_format = INSTR_FORMAT_I;
        OPCODE_STORE:                                               instr_format = INSTR_FORMAT_S;
        OPCODE_BRANCH:                                              instr_format = INSTR_FORMAT_B;
        OPCODE_AUIPC, OPCODE_LUI:                                   instr_format = INSTR_FORMAT_U;
        OPCODE_JAL:                                                 instr_format = INSTR_FORMAT_J;
        OPCODE_SYSTEM:                                              instr_format = INSTR_FORMAT_SYS;
        default:                                                    instr_format = INSTR_FORMAT_BAD;
    endcase
end

/* ------------------------------------------------------------------------------------------------
 * Instruction Field Extraction
 * --------------------------------------------------------------------------------------------- */

//TODO possibly seperate out the B and J immediates if we end up doing the branch in decode?
//TODO possibly don't mux the B and J immediates if we end up doing the branch in decode?

//Register indexes and funct fields
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

//Regular immediates
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
        INSTR_FORMAT_B:     muxed_imm_to_e1 = imm_b;
        INSTR_FORMAT_U:     muxed_imm_to_e1 = imm_u;
        INSTR_FORMAT_J:     muxed_imm_to_e1 = imm_j;
        INSTR_FORMAT_SYS:   muxed_imm_to_e1 = csr_uimm;
        default:            muxed_imm_to_e1 = 32'hDEADBEEF;
    endcase
end

/* ------------------------------------------------------------------------------------------------
 * Control Signal Generation
 * --------------------------------------------------------------------------------------------- */

system_instr_e system_instr;

//TODO

/* ------------------------------------------------------------------------------------------------
 * RF Access/CSR Reads
 * --------------------------------------------------------------------------------------------- */

word_t rs1_rdata, rs2_rdata;
always_comb begin
    o_rs1_idx = rs1_idx;
    o_rs2_idx = rs2_idx;
    //TODO register read enables to allow TGHM bypassing

    //TODO also bypass mux if selected by TGHM
    rs1_rdata = i_rs1_rdata;
    rs2_rdata = i_rs2_rdata;
end

word_t csr_rdata;
always_comb begin
    //o_csr_explicit_ren  =//TODO
    o_csr_explicit_ridx = csr_idx;
    csr_rdata           = i_csr_explicit_rdata;
    //TODO actually cause exception on illegal CSR read
end

/* ------------------------------------------------------------------------------------------------
 * Branch Logic
 * --------------------------------------------------------------------------------------------- */

//TODO

/* ------------------------------------------------------------------------------------------------
 * Output Flop Stage
 * --------------------------------------------------------------------------------------------- */

always_ff @(posedge i_clk) begin
    if (~i_rst_n) begin
        o_d_to_e1.valid <= 1'b0;
    end else begin
        //The decode stage always takes only a single cycle; no caches here!

        //TODO stall logic
        o_d_to_e1.valid <= i_f2_to_d.valid;
    end
end

always_ff @(posedge i_clk) begin
    //TODO stall logic
    o_d_to_e1.pc_word   <= i_f2_to_d.pc_word;
    o_d_to_e1.rs1_rdata <= rs1_rdata;
    o_d_to_e1.rs2_rdata <= rs2_rdata;
    o_d_to_e1.immediate <= muxed_imm_to_e1;

    o_d_to_e1.csr_idx   <= csr_idx;
    o_d_to_e1.csr_rdata <= csr_rdata;

    //TODO opcode/other control signals
end

endmodule : letc_core_stage_d
