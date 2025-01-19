//TODO add structs for between the various stages
/*
 * File:    letc_core_pkg.sv
 * Brief:   Common LETC Core stuffs
 *
 * Copyright:
 *  Copyright (C) 2023-2025 John Jekel
 *  Copyright (C) 2025 Nick Chan
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
typedef logic [11:0]    csr_idx_t;

//We don't support misaligned instructions or the C extension so we can ignore the lower 2 bits of the PC
typedef logic [31:2]    pc_word_t;

//C extension is not supported so we can save some bits
typedef logic [31:2]    instr_t;

/* ------------------------------------------------------------------------------------------------
 * Parameters
 * --------------------------------------------------------------------------------------------- */

//verilator lint_save
//verilator lint_off UNUSEDPARAM

parameter pc_word_t RESET_PC_WORD = 30'h00000000;

//verilator lint_restore

/* ------------------------------------------------------------------------------------------------
 * Enums
 * --------------------------------------------------------------------------------------------- */

typedef enum logic [1:0] {
    U_MODE = 2'b00,
    S_MODE = 2'b01,
    M_MODE = 2'b11
} priv_mode_e;

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
    ALU_OP_AND,
    //May be needed for atomics in the future if we do them in HW
    /*
    ALU_OP_MIN,
    ALU_OP_MAX,
    ALU_OP_MINU,
    ALU_OP_MAXU,
    */
    ALU_OP_MCLR//Mask clear (for CSR instructions); use OR for "MSET"
    //ALU_OP_PASS1//No instructions really need this
    //ALU_OP_PASS2//Using ADD and making the first operand 0 instead
    //FIXME we need a special ALU op that clears the lsb after the addition for JALR
} alu_op_e;

typedef enum logic [1:0] {
    MEM_OP_NOP = 2'b00,
    MEM_OP_LOAD,
    MEM_OP_STORE
    //TODO perhaps something for atomics in the future?
} mem_op_e;

typedef enum logic {
    //Either nothing or read-modify-write
    CSR_OP_NOP = 1'b0,
    CSR_OP_ACCESS
} csr_op_e;

typedef enum logic [1:0] {
    RD_SRC_ALU,
    RD_SRC_MEM,
    RD_SRC_CSR
} rd_src_e;

typedef enum logic [1:0] {
    ALU_OP1_SRC_RS1,
    ALU_OP1_SRC_PC,
    ALU_OP1_SRC_CSR,
    ALU_OP1_SRC_ZERO//Useful to pass through op2 for lui, etc
} alu_op1_src_e;

typedef enum logic [1:0] {
    ALU_OP2_SRC_RS1,
    ALU_OP2_SRC_RS2,
    ALU_OP2_SRC_IMM,
    ALU_OP2_SRC_FOUR
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
    csr_idx_t           csr_idx;
    letc_pkg::word_t    csr_rdata;

    reg_idx_t           rs1_idx;//Not used by e1 directly, rather used by TGHM to detect hazards
    reg_idx_t           rs2_idx;//Same here
    letc_pkg::word_t    rs1_rdata;
    letc_pkg::word_t    rs2_rdata;

    letc_pkg::word_t    immediate;

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
    csr_idx_t           csr_idx;
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

    csr_op_e            csr_op;
    csr_idx_t           csr_idx;

    letc_pkg::word_t    old_csr_value;//Written to rd, sometimes
    letc_pkg::word_t    alu_result;//Sometimes written to rd, or to a CSR
    letc_pkg::word_t    memory_rdata;//Written to rd, sometimes
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

    priv_mode_e current_priv;//Not really a standard RISC-V CSR but useful to many things
} csr_implicit_rdata_s;

endpackage : letc_core_pkg
