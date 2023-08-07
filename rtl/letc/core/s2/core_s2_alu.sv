/*
 * File:    core_s2_alu.sv
 * Brief:   The ALU
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

module core_s2_alu
`ifndef IMPORTS_IN_MODULE_SCOPE_UNSUPPORTED
    import letc_pkg::*;
    import core_pkg::*;
`endif
(
    input   word_t      alu_operand_1,
    input   word_t      alu_operand_2,
    input   alu_op_e    alu_operation,
    output  word_t      alu_result
);

//TODO

endmodule : core_s2_alu
