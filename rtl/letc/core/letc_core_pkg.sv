/*
 * File:    letc_core_pkg.sv
 * Brief:   Common LETC Core stuffs
 *
 * Copyright:
 *  Copyright (C) 2023-2025 John Jekel
 *  Copyright (C) 2025 Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Package Definition
 * --------------------------------------------------------------------------------------------- */

package letc_core_pkg;

/* ------------------------------------------------------------------------------------------------
 * Typedefs
 * --------------------------------------------------------------------------------------------- */

typedef logic [11:0]    csr_idx_t;
typedef logic [4:0]     csr_zimm_t;

//TODO decide if we should save hardware by leaving off the two lsbs off instr_t and pc_t
//We were originally doing that but switched to this to make our lives easier
//Might help timing though by easing routing pressure?
typedef logic [31:0]    pc_t;
typedef logic [31:0]    instr_t;

typedef logic [31:0]    vaddr_t;

/* ------------------------------------------------------------------------------------------------
 * Parameters
 * --------------------------------------------------------------------------------------------- */

//verilator lint_save
//verilator lint_off UNUSEDPARAM

parameter pc_t RESET_PC = 32'h00000000;

parameter NUM_STAGES            = 7;
parameter FETCH1_STAGE_IDX      = 0;
parameter FETCH2_STAGE_IDX      = 1;
parameter DECODE_STAGE_IDX      = 2;
parameter EXECUTE_STAGE_IDX     = 3;
parameter MEMORY1_STAGE_IDX     = 4;
parameter MEMORY2_STAGE_IDX     = 5;
parameter WRITEBACK_STAGE_IDX   = 6;

//verilator lint_restore

/* ------------------------------------------------------------------------------------------------
 * Enums
 * --------------------------------------------------------------------------------------------- */

typedef enum logic [1:0] {
    //Values correspond to RISC-V instruction encoding for potential efficiency gains
    MEM_SIZE_BYTE       = 2'b00,
    MEM_SIZE_HALFWORD   = 2'b01,
    MEM_SIZE_WORD       = 2'b10
} mem_size_e;

typedef enum logic [1:0] {
    BRANCH_NOP = 2'b00,//Not a branch
    BRANCH_COND,
    BRANCH_JALR,
    BRANCH_JAL
} branch_e;

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
    //ALU_OP_PASS1//No instructions really need this
    //ALU_OP_PASS2//Using ADD and making the first operand 0 instead
    //FIXME we need a special ALU op that clears the lsb after the addition for JALR
} alu_op_e;

typedef enum logic [1:0] {
    MEM_OP_NOP = 2'b00,
    MEM_OP_LOAD,
    MEM_OP_STORE,
    MEM_OP_AMO
} mem_op_e;

typedef enum logic [3:0] {
    AMO_OP_SWAP,
    AMO_OP_ADD,
    AMO_OP_AND,
    AMO_OP_OR,
    AMO_OP_XOR,
    AMO_OP_MIN,
    AMO_OP_MAX,
    AMO_OP_MINU,
    AMO_OP_MAXU
} amo_alu_op_e;

typedef enum logic [1:0] {
    CSR_ALU_OP_PASSTHRU = 2'b00,
    CSR_ALU_OP_BITSET,
    CSR_ALU_OP_BITCLEAR
} csr_alu_op_e;

typedef enum logic {
    CSR_OP_SRC_RS1,
    CSR_OP_SRC_ZIMM
} csr_op_src_e;

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
    pc_t pc;

    //TODO add exception status signal
} f1_to_f2_s;

typedef struct packed {
    pc_t    pc;
    instr_t instr;

    //TODO add exception status signal
} f2_to_d_s;

typedef struct packed {
    pc_t                    pc;

    rd_src_e                rd_src;
    riscv_pkg::reg_idx_t    rd_idx;
    logic                   rd_we;

    csr_alu_op_e            csr_alu_op;
    logic                   csr_expl_wen;
    csr_op_src_e            csr_op_src;
    csr_idx_t               csr_idx;
    csr_zimm_t              csr_zimm;
    riscv_pkg::word_t       csr_old_val;

    riscv_pkg::reg_idx_t    rs1_idx;
    riscv_pkg::reg_idx_t    rs2_idx;
    riscv_pkg::word_t       rs1_val;
    riscv_pkg::word_t       rs2_val;

    riscv_pkg::word_t       immediate;

    alu_op1_src_e           alu_op1_src;
    alu_op2_src_e           alu_op2_src;
    alu_op_e                alu_op;

    mem_op_e                mem_op;
    logic                   mem_signed;
    mem_size_e              mem_size;
    amo_alu_op_e            amo_alu_op;

    branch_e                branch_type;
    cmp_op_e                cmp_op;

`ifdef SIMULATION
    logic                   sim_exit_req;
`endif

    //TODO add exception status signal
} d_to_e_s;

typedef struct packed {
    pc_t                    pc;
    rd_src_e                rd_src;
    riscv_pkg::reg_idx_t    rd_idx;
    logic                   rd_we;

    logic                   csr_expl_wen;
    csr_idx_t               csr_idx;
    riscv_pkg::word_t       csr_old_val;//To be written to rd
    riscv_pkg::word_t       csr_new_val;//To be written back to the CSR

    riscv_pkg::reg_idx_t    rs1_idx;
    riscv_pkg::reg_idx_t    rs2_idx;

    riscv_pkg::word_t       alu_result;

    mem_op_e                mem_op;
    logic                   mem_signed;
    mem_size_e              mem_size;
    amo_alu_op_e            amo_alu_op;
    riscv_pkg::word_t       rs2_val;//rs2 is what is written to memory

    logic                   branch_taken;
    pc_t                    branch_target;

`ifdef SIMULATION
    logic                   sim_exit_req;
`endif

    //TODO add exception status signal
} e_to_m1_s;

typedef struct packed {
    pc_t                    pc;
    rd_src_e                rd_src;
    riscv_pkg::reg_idx_t    rd_idx;
    logic                   rd_we;
    logic                   csr_expl_wen;
    csr_idx_t               csr_idx;
    riscv_pkg::word_t       csr_old_val;
    riscv_pkg::word_t       csr_new_val;
    riscv_pkg::word_t       alu_result;
    mem_op_e                mem_op;
    logic                   mem_signed;
    mem_size_e              mem_size;
    amo_alu_op_e            amo_alu_op;
    riscv_pkg::word_t       rs2_val;

`ifdef SIMULATION
    logic                   sim_exit_req;
`endif

    //TODO add exception status signal
} m1_to_m2_s;

typedef struct packed {
    pc_t                    pc;
    rd_src_e                rd_src;
    riscv_pkg::reg_idx_t    rd_idx;
    logic                   rd_we;

    logic                   csr_expl_wen;
    csr_idx_t               csr_idx;

    riscv_pkg::word_t       csr_old_val;//Written to rd, sometimes
    riscv_pkg::word_t       alu_result;//Written to rd, sometimes
    riscv_pkg::word_t       mem_rdata;//Written to rd, sometimes
    riscv_pkg::word_t       csr_new_val;//Written to a CSR

    mem_op_e                mem_op;
    mem_size_e              mem_size;
    riscv_pkg::word_t       mem_wdata;

`ifdef SIMULATION
    logic                   sim_exit_req;
`endif

    //TODO add exception status signal
} m2_to_w_s;

/* ------------------------------------------------------------------------------------------------
 * CSR Structs
 * --------------------------------------------------------------------------------------------- */

// TODO: Create structs for each CSR that holds the fields

// TODO: Should this be an interface?
//Note: Only provides CSRs that actually need to be implicitly read by LETC Core logic
typedef struct packed {
    //TODO add more CSRs here if they need to be implicitly read

    riscv_pkg::word_t mstatus;
    riscv_pkg::word_t mcause;
    riscv_pkg::word_t mip;
    riscv_pkg::word_t mie;
    riscv_pkg::word_t mideleg;
    riscv_pkg::word_t medeleg;
    riscv_pkg::word_t mtvec;

    riscv_pkg::word_t scause;
    riscv_pkg::word_t stvec;
    riscv_pkg::word_t satp;

    riscv_pkg::priv_mode_e current_priv;//Not really a standard RISC-V CSR but useful to many things
} csr_implicit_rdata_s;

endpackage : letc_core_pkg
