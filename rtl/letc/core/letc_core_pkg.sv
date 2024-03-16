/*
 * File:    letc_core_pkg.sv
 * Brief:   TODO
 *
 * Copyright:
 *  Copyright (C) 2023-2024 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Package Definition
 * --------------------------------------------------------------------------------------------- */

package letc_core_pkg;

/* ------------------------------------------------------------------------------------------------
 * Typedefs
 * --------------------------------------------------------------------------------------------- */

typedef logic [4:0]     reg_idx_t;

//We don't support misaligned instructions or the C extension so we can ignore the lower 2 bits of the PC
typedef logic [31:2]    pc_word_t;

//C extension is not supported so we can save some bits
typedef logic [31:2]    instr_t;

/* ------------------------------------------------------------------------------------------------
 * Parameters
 * --------------------------------------------------------------------------------------------- */

parameter pc_word_t RESET_PC_WORD= 30'h00000000;

/* ------------------------------------------------------------------------------------------------
 * Enums
 * --------------------------------------------------------------------------------------------- */

typedef enum logic [1:0] {
    U_MODE = 2'b00,
    S_MODE = 2'b01,
    M_MODE = 2'b11
} prv_mode_e;

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
    INSTR_FORMAT_R, INSTR_FORMAT_I, INSTR_FORMAT_S, INSTR_FORMAT_B,
    INSTR_FORMAT_U, INSTR_FORMAT_J, INSTR_FORMAT_UIMM, INSTR_FORMAT_OTHER
} instr_format_e;

typedef enum logic [1:0] {
    //Values correspond to RISC-V instruction encoding for potential efficiency gains
    SIZE_BYTE       = 2'b00,
    SIZE_HALFWORD   = 2'b01,
    SIZE_WORD       = 2'b10
} size_e;

typedef enum logic [2:0] {
    //Enum values based on funct3 of branch instructions
    CMP_OP_EQ   = 3'b000,
    CMP_OP_NE   = 3'b001,
    CMP_OP_LT   = 3'b100,
    CMP_OP_GE   = 3'b101,
    CMP_OP_LTU  = 3'b110,
    CMP_OP_GEU  = 3'b111
} cmp_op_e;

typedef enum logic [3:0] {
    ALU_OP_ADD,
    ALU_OP_SUB,
    ALU_OP_SLL,
    ALU_OP_SLT,
    ALU_OP_SLTU,
    ALU_OP_SRL,
    ALU_OP_SRA,
    ALU_OP_XOR,
    ALU_OP_OR,
    ALU_OP_AND
} alu_op_e;

/* ------------------------------------------------------------------------------------------------
 * Structs 
 * --------------------------------------------------------------------------------------------- */

typedef struct packed {
    logic               valid;
    pc_word_t           pc_word;
    letc_pkg::paddr_t   fetch_addr;
} f1_to_f2_s;

typedef struct packed {
    logic       valid;
    pc_word_t   pc_word;
    instr_t     instr;
} f2_to_d_s;

typedef struct packed {
    logic               valid;
    pc_word_t           pc_word;

    //reg_idx_t           rs1_idx;//Are these needed for bypassing?
    //reg_idx_t           rs2_idx;
    reg_idx_t           rd_idx;

    letc_pkg::word_t    rs1_rdata;
    letc_pkg::word_t    rs2_rdata;

    letc_pkg::word_t    immediate;

    opcode_e            opcode;
    //TODO control signals, rd write enable, etc
} d_to_e1_s;

typedef struct packed {
    logic valid;
    //TODO
} e1_to_e2_s;

typedef struct packed {
    logic valid;
    //TODO
} e2_to_w_s;

endpackage : letc_core_pkg
