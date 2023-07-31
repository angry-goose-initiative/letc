/*
 * File:    core_pkg.svh
 * Brief:   TODO
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

package core_pkg;

    typedef logic [4:0] reg_index_t;
    typedef enum logic [4:0] {//TODO prefix all of these with OPCODE_
        OPCODE_LOAD = 5'b00000,   OPCODE_LOAD_FP = 5'b00001,    CUSTOM_0 = 5'b00010,   MISC_MEM = 5'b00011,
        OPCODE_OP_IMM = 5'b00100, OPCODE_AUIPC = 5'b00101,      OP_IMM_32 = 5'b00110,  B48_0 = 5'b00111,
        OPCODE_STORE = 5'b01000,  OPCODE_STORE_FP = 5'b01001,   CUSTOM_1 = 5'b01010,   AMO = 5'b01011,
        OPCODE_OP = 5'b01100,     OPCODE_LUI = 5'b01101,        OP_32 = 5'b01110,      B64 = 5'b01111,
        OPCODE_MADD = 5'b10000,   OPCODE_MSUB = 5'b10001,       NMSUB = 5'b10010,      NMADD = 5'b10011,
        OPCODE_OP_FP = 5'b10100,  OPCODE_RESERVED_0 = 5'b10101, CUSTOM_2 = 5'b10110,   B48_1 = 5'b10111,
        OPCODE_BRANCH = 5'b11000, OPCODE_JALR = 5'b11001,       RESERVED_1 = 5'b11010, JAL = 5'b11011,
        OPCODE_SYSTEM = 5'b11100, OPCODE_RESERVED_3 = 5'b11101, CUSTOM_3 = 5'b11110,   BGE80 = 5'b11111
    } opcode_e;
    typedef logic [31:0] word_t;
    typedef logic [15:0] halfword_t;
    typedef logic [7:0]  byte_t;
    typedef enum logic [2:0] {
        ALUOPTODO//TODO
    } aluop_e;
    typedef enum logic [2:0] {
        INSTR_FORMAT_R, INSTR_FORMAT_I, INSTR_FORMAT_S, INSTR_FORMAT_B, INSTR_FORMAT_U, INSTR_FORMAT_J, INSTR_FORMAT_UIMM
    } instr_format_e;
    typedef enum logic [1:0] {
        RD_FROM_NEXT_SEQ_PC,
        RD_FROM_ALU_RESULT,
        RD_FROM_CSR,
        RD_FROM_MEM_LOAD
    } rd_src_e;
    typedef enum logic [1:0] {
        ALUOPSRC1TODO
        //TODO
    } alu_op1_src_e;
    typedef enum logic [2:0] {
        ALUOPSRC2TODO
        //TODO
    } alu_op2_src_e;

endpackage : core_pkg
