/*
 * File:    core_s2_alu_src_mux.sv
 * Brief:   The ALU source mux
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

module core_s2_alu_src_mux
`ifndef IMPORTS_IN_MODULE_SCOPE_UNSUPPORTED
    import letc_pkg::*;
    import core_pkg::*;
`endif
(
    //ALU operand 1 mux IO
    input   alu_op1_src_e   alu_op1_src,
    input   word_t          rs1_ff,
    input   word_t          pc,
    input   word_t          csr_uimm,
    input   word_t          dcache_data_out,
    output  word_t          alu_operand_1,

    //ALU operand 2 mux IO
    input   alu_op2_src_e   alu_op2_src,
    input   word_t          rs2_ff,
    input   word_t          imm,
    input   word_t          csr_data_out,
    output  word_t          alu_operand_2
);

//ALU operand 1 mux
always_comb begin : op1_mux
    unique case (alu_op1_src)
        ALU_OP1_SRC_RS1:                alu_operand_1 = rs1_ff;
        ALU_OP1_SRC_PC:                 alu_operand_1 = pc;
        ALU_OP1_SRC_CSR_UIMM:           alu_operand_1 = csr_uimm;
        ALU_OP1_SRC_DCACHE_DATA_OUT:    alu_operand_1 = dcache_data_out;
    endcase
end : op1_mux

//ALU operand 2 mux
always_comb begin : op2_mux
    unique case (alu_op2_src)
        ALU_OP2_SRC_RS2:            alu_operand_2 = rs2_ff;
        ALU_OP2_SRC_IMM:            alu_operand_2 = imm;
        ALU_OP2_SRC_CSR_DATA_OUT:   alu_operand_2 = csr_data_out;
    endcase
end : op2_mux

endmodule : core_s2_alu_src_mux
