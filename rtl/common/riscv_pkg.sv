/*
 * File:    riscv_pkg.sv
 * Brief:   Package for generic RISC-V things
 *
 * Copyright:
 *  Copytight (C) 2025 John Jekel
 *  Copyright (C) 2025 Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
*/

package riscv_pkg;

/* ------------------------------------------------------------------------------------------------
 * Common
 * --------------------------------------------------------------------------------------------- */

parameter WORD_WIDTH        = 32;
parameter HALFWORD_WIDTH    = 16;
parameter BYTE_WIDTH        = 8;

typedef logic [WORD_WIDTH-1:0]      word_t;
typedef logic [HALFWORD_WIDTH-1:0]  halfword_t;
typedef logic [BYTE_WIDTH-1:0]      byte_t;

/* ------------------------------------------------------------------------------------------------
 * Instruction Decoding
 * --------------------------------------------------------------------------------------------- */

typedef enum logic [4:0] {
    OPCODE_LOAD         = 5'b00000, OPCODE_LOAD_FP  = 5'b00001, OPCODE_CUSTOM_0     = 5'b00010,
    OPCODE_MISC_MEM     = 5'b00011, OPCODE_OP_IMM   = 5'b00100, OPCODE_AUIPC        = 5'b00101,
    OPCODE_OP_IMM_32    = 5'b00110, OPCODE_B48_0    = 5'b00111, OPCODE_STORE        = 5'b01000,
    OPCODE_STORE_FP     = 5'b01001, OPCODE_CUSTOM_1 = 5'b01010, OPCODE_AMO          = 5'b01011,
    OPCODE_OP           = 5'b01100, OPCODE_LUI      = 5'b01101, OPCODE_OP_32        = 5'b01110,
    OPCODE_B64          = 5'b01111, OPCODE_MADD     = 5'b10000, OPCODE_MSUB         = 5'b10001,
    OPCODE_NMSUB        = 5'b10010, OPCODE_NMADD    = 5'b10011, OPCODE_OP_FP        = 5'b10100,
    OPCODE_RESERVED_0   = 5'b10101, OPCODE_CUSTOM_2 = 5'b10110, OPCODE_B48_1        = 5'b10111,
    OPCODE_BRANCH       = 5'b11000, OPCODE_JALR     = 5'b11001, OPCODE_RESERVED_1   = 5'b11010,
    OPCODE_JAL          = 5'b11011, OPCODE_SYSTEM   = 5'b11100, OPCODE_RESERVED_3   = 5'b11101,
    OPCODE_CUSTOM_3     = 5'b11110, OPCODE_BGE80    = 5'b11111
} opcode_e;

/* ------------------------------------------------------------------------------------------------
 * CSR
 * --------------------------------------------------------------------------------------------- */

typedef enum logic [1:0] {
    U_MODE = 2'b00,
    S_MODE = 2'b01,
    M_MODE = 2'b11
} priv_mode_e;

endpackage : riscv_pkg
