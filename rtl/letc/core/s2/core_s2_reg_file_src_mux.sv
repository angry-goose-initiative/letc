/*
 * File:    core_s2_reg_file_src_mux.sv
 * Brief:   The register file source mux
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

module core_s2_reg_file_src_mux
    import letc_pkg::*;
    import core_pkg::*;
(
    input   rd_src_e    rd_src,
    input   word_t      dcache_data_out,
    input   word_t      next_seq_pc,
    input   word_t      alu_result,
    input   word_t      csr_data_out,
    output  word_t      rd
);

always_comb begin : rd_mux
    unique case(rd_src)
        RD_FROM_NEXT_SEQ_PC:    rd = next_seq_pc;
        RD_FROM_ALU_RESULT:     rd = alu_result;
        RD_FROM_CSR:            rd = csr_data_out;
        RD_FROM_MEM_LOAD:       rd = dcache_data_out;
    endcase
end : rd_mux

endmodule : core_s2_reg_file_src_mux
