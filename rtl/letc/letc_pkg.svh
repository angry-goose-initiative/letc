/*
 * File:    letc_pkg.svh
 * Brief:   TODO
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

package letc_pkg;

    //FIXME these should really be moved to a Core-specific package
    typedef logic [4:0] reg_index_t;
    typedef enum logic [4:0] {
        LOAD = 5'b00000,   LOAD_FP = 5'b00001,    CUSTOM_0 = 5'b00010,   MISC_MEM = 5'b00011,
        OP_IMM = 5'b00100, AUIPC = 5'b00101,      OP_IMM_32 = 5'b00110,  B48_0 = 5'b00111,
        STORE = 5'b01000,  STORE_FP = 5'b01001,   CUSTOM_1 = 5'b01010,   AMO = 5'b01011,
        OP = 5'b01100,     LUI = 5'b01101,        OP_32 = 5'b01110,      B64 = 5'b01111,
        MADD = 5'b10000,   MSUB = 5'b10001,       NMSUB = 5'b10010,      NMADD = 5'b10011,
        OP_FP = 5'b10100,  RESERVED_0 = 5'b10101, CUSTOM_2 = 5'b10110,   B48_1 = 5'b10111,
        BRANCH = 5'b11000, JALR = 5'b11001,       RESERVED_1 = 5'b11010, JAL = 5'b11011,
        SYSTEM = 5'b11100, RESERVED_3 = 5'b11101, CUSTOM_3 = 5'b11110,   BGE80 = 5'b11111
    } opcode_e;

    typedef logic [31:0] word_t;
    typedef logic [15:0] halfword_t;
    typedef logic [7:0]  byte_t;

    /*package mem_pkg;
    //TODO perhaps move this to a different file?
    endpackage
    */


    //TODO

endpackage : letc_pkg
