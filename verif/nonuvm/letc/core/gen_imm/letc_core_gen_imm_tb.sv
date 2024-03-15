/**
 * File    letc_core_gen_imm_tb.sv
 * Brief   TODO
 * 
 * Copyright:
 *  Copyright (C) 2024 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 * 
 * TODO longer description
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_gen_imm_tb;

import letc_pkg::*;
import letc_core_pkg::*;

/* ------------------------------------------------------------------------------------------------
 * DUT Connections
 * --------------------------------------------------------------------------------------------- */

instr_t         i_instr;
instr_format_e  i_instr_format;
word_t          o_imm;
word_t          o_csr_uimm;

/* ------------------------------------------------------------------------------------------------
 * DUT
 * --------------------------------------------------------------------------------------------- */

letc_core_gen_imm dut (.*);

/* ------------------------------------------------------------------------------------------------
 * Clocking
 * --------------------------------------------------------------------------------------------- */

//Purely combinational so no clocking needed

/* ------------------------------------------------------------------------------------------------
 * Stimulus
 * --------------------------------------------------------------------------------------------- */

logic [31:0] nice_instr;
assign i_instr = nice_instr[31:2];

initial begin
    //lw a5, 360(s1)
    nice_instr      = 32'h1684a783;
    i_instr_format  = INSTR_FORMAT_I;
    #1;
    assert(o_imm == 32'd360);

    //sw ra, 12(sp)
    nice_instr      = 32'h00112623;
    i_instr_format  = INSTR_FORMAT_S;
    #1;
    assert(o_imm == 32'd12);

    //beqz a5, offset 0x14
    nice_instr      = 32'h00078a63;
    i_instr_format  = INSTR_FORMAT_B;
    #1;
    assert(o_imm == 32'h00000014);

    //lui a5, 0x6
    nice_instr      = 32'h000067b7;
    i_instr_format  = INSTR_FORMAT_U;
    #1;
    assert(o_imm == 32'h00006000);

    //jal offset -0x3028
    //fd9fc0ef                jal     1844
    nice_instr      = 32'hfd9fc0ef;
    i_instr_format  = INSTR_FORMAT_J;
    #1;
    assert(o_imm == 32'hffffcfd8);

    //csrci mip, 2
    nice_instr      = 32'h34417073;
    i_instr_format  = INSTR_FORMAT_I;
    #1;
    assert(o_imm      == 32'h00000344);//mip
    assert(o_csr_uimm == 32'h00000002);

    //TODO more

    $finish;
end

endmodule : letc_core_gen_imm_tb
