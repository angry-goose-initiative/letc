/*
 * File:    letc_core_pkg.sv
 * Brief:   Common LETC Core stuffs
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

typedef logic [6:0]     funct7_t;
typedef logic [2:0]     funct3_t;

typedef logic [1:0]     priv_t;

/* ------------------------------------------------------------------------------------------------
 * Parameters
 * --------------------------------------------------------------------------------------------- */

parameter pc_word_t RESET_PC_WORD = 30'h00000000;

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

typedef enum logic [1:0] {
    MEM_OP_NOP,
    MEM_OP_LOAD,
    MEM_OP_STORE
} mem_op_e;

typedef enum logic {
    //Either nothing or read-modify-write
    CSR_OP_NOP,
    CSR_OP_ACCESS
} csr_op_e;

typedef enum logic [1:0] {
    RD_SRC_ALU,
    RD_SRC_MEM,
    RD_SRC_CSR
} rd_src_e;

typedef enum logic [1:0] {
    ALU_OP1_SRC_RS1
    //TODO others
} alu_op1_src_e;

typedef enum logic [1:0] {
    ALU_OP1_SRC_RS2
    //TODO others
} alu_op2_src_e;

/* ------------------------------------------------------------------------------------------------
 * Pipeline Datapath Structs
 * --------------------------------------------------------------------------------------------- */

typedef struct packed {
    logic               valid;
    pc_word_t           pc_word;
    letc_pkg::paddr_t   fetch_addr;//Virtual PC translated to physical address
} f1_to_f2_s;

typedef struct packed {
    logic       valid;
    pc_word_t   pc_word;
    instr_t     instr;
} f2_to_d_s;

typedef struct packed {
    logic               valid;
    pc_word_t           pc_word;

    rd_src_e            rd_src;//The final rd source, for writeback
    reg_idx_t           rd_idx;
    logic               rd_we;

    csr_op_e            csr_op;

    letc_pkg::word_t    rs1_rdata;
    letc_pkg::word_t    rs2_rdata;
    letc_pkg::word_t    immediate;//Sometimes contains CSR idx (bits 11:0)
    letc_pkg::word_t    csr_uimm;

    alu_op1_src_e       alu_op1_src;
    alu_op2_src_e       alu_op2_src;
    alu_op_e            alu_op;

    mem_op_e            memory_op;
    logic               memory_signed;
    size_e              memory_size;
} d_to_e1_s;

typedef struct packed {
    logic               valid;

    rd_src_e            rd_src;
    reg_idx_t           rd_idx;
    logic               rd_we;

    csr_op_e            csr_op;
    logic [11:0]        csr_idx;
    letc_pkg::word_t    old_csr_value;//To be written to rd

    letc_pkg::word_t    alu_result;//Can also pass through registers, new CSR value to writeback, mem address, etc

    mem_op_e            memory_op;
    logic               memory_signed;
    size_e              memory_size;
    letc_pkg::word_t    rs2_rdata;//rs2 is what is written to memory
} e1_to_e2_s;

typedef struct packed {
    logic               valid;

    rd_src_e            rd_src;
    reg_idx_t           rd_idx;
    logic               rd_we;

    letc_pkg::word_t    old_csr_value;
    letc_pkg::word_t    alu_result;
    letc_pkg::word_t    memory_rdata;
} e2_to_w_s;

/* ------------------------------------------------------------------------------------------------
 * CSR Structs
 * --------------------------------------------------------------------------------------------- */

//Note: Only provides CSRs that actually need to be implicitly read by LETC Core logic
typedef struct packed {
    //TODO structs for each CSR that holds the fields
    //TODO add more CSRs here if they need to be implicitly read

    letc_pkg::word_t mstatus;
    letc_pkg::word_t mcause;
    letc_pkg::word_t mip;
    letc_pkg::word_t mie;
    letc_pkg::word_t mideleg;
    letc_pkg::word_t medeleg;
    letc_pkg::word_t mtvec;

    letc_pkg::word_t scause;
    letc_pkg::word_t stvec;
    letc_pkg::word_t satp;

    priv_t current_priv;//Not really a standard RISC-V CSR but useful to many things
} csr_implicit_rdata_s;

endpackage : letc_core_pkg
