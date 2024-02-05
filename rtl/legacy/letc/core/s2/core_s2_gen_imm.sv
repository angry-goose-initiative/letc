/*
 * File:    core_s2_gen_imm.sv
 * Brief:   Generates immediate values
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

module core_s2_gen_imm
`ifndef IMPORTS_IN_MODULE_SCOPE_UNSUPPORTED
    import letc_pkg::*;
    import core_pkg::*;
`endif
(
    input   word_t          instr,
    input   instr_format_e  instr_format,
    output  word_t          imm,
    output  word_t          csr_uimm
    // TODO other ports
);

//For the CSR uimm, we always provide it, treating CSR instructions as I-type so we get _that_ immediate too since both are needed
assign csr_uimm  = {27'd0, instr[19:15]};//NOT sign extended

//Regular immediates
word_t imm_i;
word_t imm_s;
word_t imm_b;
word_t imm_u;
word_t imm_j;
assign imm_i = {{20{instr[31]}}, instr[31:20]};
assign imm_s = {{20{instr[31]}}, instr[31:25], instr[11:7]};
assign imm_b = {{19{instr[31]}}, instr[31],    instr[7],  instr[30:25], instr[11:8], 1'b0};
assign imm_u = {instr[31:12], 12'h000};
assign imm_j = {{12{instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0};

//Regular immediate mux based on instruction format
always_comb begin : immediate_mux
    unique case (instr_format)
        INSTR_FORMAT_I: imm = imm_i;
        INSTR_FORMAT_S: imm = imm_s;
        INSTR_FORMAT_B: imm = imm_b;
        INSTR_FORMAT_U: imm = imm_u;
        INSTR_FORMAT_J: imm = imm_j;
        default: imm = 32'hDEADBEEF;
    endcase
end : immediate_mux

endmodule : core_s2_gen_imm