/*
 * File:    letc_core_gen_imm.sv
 * Brief:   Generates immediates from RISC-V instructions
 *
 * Copyright:
 *  Copyright (C) 2023-2024 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_gen_imm
    import letc_pkg::*;
    import letc_core_pkg::*;
(
    input   instr_t         i_instr,
    input   instr_format_e  i_instr_format,
    output  word_t          o_imm,
    output  word_t          o_csr_uimm
);

/* ------------------------------------------------------------------------------------------------
 * Immediate Generation
 * --------------------------------------------------------------------------------------------- */

//For the CSR uimm, we always provide it, treating CSR instructions as I-type so we get _that_ immediate too since both are needed
assign o_csr_uimm = {27'd0, i_instr[19:15]};//NOT sign extended

//Regular immediates
word_t imm_i, imm_s, imm_b, imm_u, imm_j;
always_comb begin
    imm_i = {{20{i_instr[31]}}, i_instr[31:20]};
    imm_s = {{20{i_instr[31]}}, i_instr[31:25], i_instr[11:7]};
    imm_b = {{19{i_instr[31]}}, i_instr[31],    i_instr[7],  i_instr[30:25], i_instr[11:8], 1'b0};
    imm_u = {i_instr[31:12], 12'h000};
    imm_j = {{12{i_instr[31]}}, i_instr[19:12], i_instr[20], i_instr[30:21], 1'b0};
end

/* ------------------------------------------------------------------------------------------------
 * Muxing
 * --------------------------------------------------------------------------------------------- */

//Regular immediate mux based on instruction format
//Synthesis tool should detect the minimum muxes needed for each bit of the immediate
always_comb begin
    unique case (i_instr_format)
        INSTR_FORMAT_I: o_imm = imm_i;
        INSTR_FORMAT_S: o_imm = imm_s;
        INSTR_FORMAT_B: o_imm = imm_b;
        INSTR_FORMAT_U: o_imm = imm_u;
        INSTR_FORMAT_J: o_imm = imm_j;
        default:        o_imm = 32'hDEADBEEF;
    endcase
end

endmodule : letc_core_gen_imm
