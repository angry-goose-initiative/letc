/*
 * File:    letc_core_top.sv
 * Brief:   Top of LETC Core
 *  _     _____ _____ ____    ____
 * | |   | ____|_   _/ ___|  / ___|___  _ __ ___
 * | |   |  _|   | || |     | |   / _ \| '__/ _ \
 * | |___| |___  | || |___  | |__| (_) | | |  __/
 * |_____|_____| |_| \____|  \____\___/|_|  \___|
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
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module letc_core_top
    import riscv_pkg::*;
    import letc_pkg::*;
    import letc_core_pkg::*;
(
    //Clock and reset
    input logic clk,
    input logic rst_n,

    //IO
    axi_if.manager          axi_instr,
    axi_if.manager          axi_data,
    //FIXME remove these waivers eventually
    //verilator lint_save
    //verilator lint_off UNUSEDSIGNAL
    //verilator lint_off UNDRIVEN
    input logic             timer_irq_pending,
    input logic             external_irq_pending,

    //Debug (Logic Analyzer)
    output logic [7:0]      o_debug

    //verilator lint_restore
);

/* ------------------------------------------------------------------------------------------------
 * Connections
 * --------------------------------------------------------------------------------------------- */

//TODO signal to globally flush caches?

//rd Write Port
reg_idx_t   rf_rd_idx;
word_t      rf_rd_val;
logic       rf_rd_we;

//rs1 Read Port
reg_idx_t   rf_rs1_idx;
word_t      rf_rs1_val;

//rs2 Read Port
reg_idx_t   rf_rs2_idx;
word_t      rf_rs2_val;

//Explicit CSR access
csr_idx_t    csr_de_expl_idx;
word_t       csr_de_expl_rdata;
logic        csr_de_expl_rill;
logic        csr_de_expl_will;

//Inter-stage connections
logic f1_to_f2_valid;
logic f2_to_d_valid;
logic d_to_e_valid;
logic e_to_m1_valid;
logic m1_to_m2_valid;
logic m2_to_w_valid;
f1_to_f2_s  f1_to_f2;
f2_to_d_s   f2_to_d;
d_to_e_s    d_to_e;
e_to_m1_s   e_to_m1;
m1_to_m2_s  m1_to_m2;
m2_to_w_s   m2_to_w;

//Implicitly read CSRs by LETC Core logic, always valid
csr_implicit_rdata_s csr_implicit_rdata;

//Hazard/backpressure signals
logic [NUM_STAGES-1:0] stage_ready;
logic [NUM_STAGES-1:0] stage_flush;
logic [NUM_STAGES-1:0] stage_stall;

// Decided branches
logic   branch_taken;
pc_t    branch_target;

// Forwarding interfaces
letc_core_forwardee_if  e_forwardee_rs1();
letc_core_forwardee_if  e_forwardee_rs2();
letc_core_forwardee_if m1_forwardee_rs2();
letc_core_forwardee_if m2_forwardee_rs2();

letc_core_forwarder_if m1_forwarder();
letc_core_forwarder_if m2_forwarder();
letc_core_forwarder_if  w_forwarder();

//MSS Interfaces
letc_core_imss_if imss_if (.*);
letc_core_dmss_if dmss_if (.*);

//Change the PC (useful for branches, exceptions, etc)
logic   pc_load_en;
pc_t    pc_load_val;

//assign o_debug = d_to_e1[7:0];//TESTING

/* ------------------------------------------------------------------------------------------------
 * Module Instantiations
 * --------------------------------------------------------------------------------------------- */

letc_core_adhesive glue (.*);

letc_core_rf rf (.*);

letc_core_imss imss (.*);

letc_core_dmss dmss (.*);

letc_core_stage_fetch1 stage_fetch1 (
    .*,

    //Hazard/backpressure signals
    .f1_ready(stage_ready[FETCH1_STAGE_IDX]),
    .f1_flush(stage_flush[FETCH1_STAGE_IDX]),
    .f1_stall(stage_stall[FETCH1_STAGE_IDX])
);

letc_core_stage_fetch2 stage_fetch2 (
    .*,

    //Hazard/backpressure signals
    .f2_ready(stage_ready[FETCH2_STAGE_IDX]),
    .f2_flush(stage_flush[FETCH2_STAGE_IDX]),
    .f2_stall(stage_stall[FETCH2_STAGE_IDX])
);

//FIXME why does XSIM act like stage_ready has multiple drivers
//unless we do this indirect assignment instead?
//logic xsim_workaround_stage_d_ready;
//assign stage_ready[2] = xsim_workaround_stage_d_ready;

letc_core_stage_decode stage_decode (
    .*,

    //Hazard/backpressure signals
    .d_ready(stage_ready[DECODE_STAGE_IDX]),
    .d_flush(stage_flush[DECODE_STAGE_IDX]),
    .d_stall(stage_stall[DECODE_STAGE_IDX])
);

letc_core_stage_execute stage_execute (
    .*,

    //Hazard/backpressure signals
    .e_ready(stage_ready[EXECUTE_STAGE_IDX]),
    .e_flush(stage_flush[EXECUTE_STAGE_IDX]),
    .e_stall(stage_stall[EXECUTE_STAGE_IDX])
);

letc_core_stage_memory1 stage_memory1 (
    .*,

    //Hazard/backpressure signals
    .m1_ready(stage_ready[MEMORY1_STAGE_IDX]),
    .m1_flush(stage_flush[MEMORY1_STAGE_IDX]),
    .m1_stall(stage_stall[MEMORY1_STAGE_IDX])
);

letc_core_stage_memory2 stage_memory2 (
    .*,

    //Hazard/backpressure signals
    .m2_ready(stage_ready[MEMORY2_STAGE_IDX]),
    .m2_flush(stage_flush[MEMORY2_STAGE_IDX]),
    .m2_stall(stage_stall[MEMORY2_STAGE_IDX])
);

letc_core_stage_writeback stage_writeback (
    .*,

    //Hazard/backpressure signals
    .w_ready(stage_ready[WRITEBACK_STAGE_IDX]),
    .w_flush(stage_flush[WRITEBACK_STAGE_IDX]),
    .w_stall(stage_stall[WRITEBACK_STAGE_IDX])
);

endmodule : letc_core_top
