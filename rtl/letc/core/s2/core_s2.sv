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

    input   s1_to_s2_s      s1_to_s2,
    output  s2_to_s1_s      s2_to_s1,
    //TODO move these signals to the s1_to_s2 and s2_to_s1 structs
    //From s1

    //To s1

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
//word_t  instr_ff;
//word_t  pc_ff;//PC?
word_t  instr;
word_t  pc;
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

assign s2_to_s1.branch_en = uncond_branch_en || (cond_branch_en && cmp_result);

assign pc = s1_to_s2.pc;
assign instr = s1_to_s2.instr;

//assign next_seq_pc = pc_ff + 4;
assign next_seq_pc = pc + 32'd4;

//FIXME possible design consideration here. Introduce an instruction_ff stage may introduce an additional stage of latency. This may need to be removed, even though it would help with
//TODO actually we will include this, but we'll move it into s1
/*
always_ff @(posedge clk, negedge rst_n) begin : from_s1
    if (!rst_n) begin
        pc_ff       <= 32'hDEADBEEF;
        instr_ff    <= 32'hDEADBEEF;
    end else if (from_s1_we) begin
        pc_ff       <= s1_to_s2.pc;
        instr_ff    <= s1_to_s2.instr;
    end
end : from_s1
*/

/* ------------------------------------------------------------------------------------------------
 * Module Instantiations
 * --------------------------------------------------------------------------------------------- */

core_s2_control             core_s2_control_inst            (.halt_req(s2_to_s1.halt_req), .*);
core_s2_alu_src_mux         core_s2_alu_src_mux_inst        (.*);
core_s2_alu                 core_s2_alu_inst                (.*);
core_s2_reg_file_src_mux    core_s2_reg_file_src_mux_inst   (.*);
core_s2_reg_file            core_s2_reg_file_inst           (.*);
core_s2_gen_imm             core_s2_gen_imm_inst            (.*);
core_s2_comparator          core_s2_comparator_inst         (.*);

endmodule : core_s2
