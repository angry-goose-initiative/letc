/*
 * File:    core_s2.sv
 * Brief:   TODO
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

`ifdef IMPORTS_IN_MODULE_SCOPE_UNSUPPORTED
import letc_pkg::*;
import core_pkg::*;
`endif

module core_s2
`ifndef IMPORTS_IN_MODULE_SCOPE_UNSUPPORTED
    import letc_pkg::*;
    import core_pkg::*;
`endif
(
    input   logic           clk,
    input   logic           rst_n,

    //From s1
    input   word_t          s1_to_s2_instr,
    input   word_t          s1_to_s2_pc,

    //To s1
    output  word_t          s2_to_s1_branch_target_addr,
    output  logic           s2_to_s1_branch_en,
    output  logic           s2_busy,//Means s2 is NOT ready to accept a new instruction from s1 this cycle//TODO or does this go to master control?
    output  logic           halt_req,//LETC.EXIT instruction encountered in M-mode

    //CSR
    input   word_t          csr_data_out,
    output  word_t          csr_wd,
    output  logic           csr_we,
    output  logic [11:0]    csr_sel

    //TODO other ports

);

/* ------------------------------------------------------------------------------------------------
 * Connections
 * --------------------------------------------------------------------------------------------- */

//?
logic   from_s1_we;
word_t  instr_ff;
word_t  pc_ff;//PC?
word_t  next_seq_pc;//PC?

//Memory
word_t dcache_data_out;

//Register file
reg_idx_t   rd_idx;
word_t      rd_wd;
logic       rd_we;
reg_idx_t   rs1_idx;
word_t      rs1_ff;
reg_idx_t   rs2_idx;
word_t      rs2_ff;

//Register file source mux
rd_src_e rd_src;

//Internal control signals
word_t          imm;
word_t          csr_uimm;
logic           illegal_instr;//TODO this will go to the trap priority controller via core_top
instr_format_e  instr_format;

//Branching
cmp_op_e        cmp_operation;
logic           cmp_result;
logic           cond_branch_en;
logic           uncond_branch_en;

//TODO others

//ALU
word_t      alu_operand_1;
word_t      alu_operand_2;
alu_op_e    alu_operation;
word_t      alu_result;

//ALU source mux
alu_op1_src_e alu_op1_src;
alu_op2_src_e alu_op2_src;

assign s2_to_s1_branch_en = uncond_branch_en || (cond_branch_en && cmp_result);

assign next_seq_pc = pc_ff + 4;

//FIXME possible design consideration here. Introduce an instruction_ff stage may introduce an additional stage of latency. This may need to be removed, even though it would help with
always_ff @(posedge clk, negedge rst_n) begin : from_s1
    if (!rst_n) begin
        pc_ff       <= 32'hDEADBEEF;
        instr_ff    <= 32'hDEADBEEF;
    end else if (from_s1_we) begin
        pc_ff       <= s1_to_s2_pc;
        instr_ff    <= s1_to_s2_instr;
    end
end : from_s1

/* ------------------------------------------------------------------------------------------------
 * Module Instantiations
 * --------------------------------------------------------------------------------------------- */

core_s2_control             core_s2_control_inst            (.*);
core_s2_alu_src_mux         core_s2_alu_src_mux_inst        (.*);
core_s2_alu                 core_s2_alu_inst                (.*);
core_s2_reg_file_src_mux    core_s2_reg_file_src_mux_inst   (.*);
core_s2_reg_file            core_s2_reg_file_inst           (.*);
core_s2_gen_imm             core_s2_gen_imm_inst            (.*);
core_s2_comparator          core_s2_comparator_inst         (.*);

endmodule : core_s2
