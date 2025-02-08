/*
 * File:    letc_core_forwarder_if.sv
 * Brief:   Interface to adhesive from stages that provide forwarded data
 *
 * Copyright:
 *  Copyright (C) 2025 Nick Chan
 *  Copyright (C) 2025 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * One of these stage that produces forwarded data
 *
*/

interface letc_core_forwarder_if;

import riscv_pkg::*;
import letc_core_pkg::*;

logic       instr_produces_rd;
logic       rd_val_avail;
word_t      rd_val;
reg_idx_t   rd_idx;

modport fwd_factory (
    input   instr_produces_rd,
    input   rd_val_avail,
    input   rd_val,
    input   rd_idx
);

modport stage (
    output  instr_produces_rd,
    output  rd_val_avail,
    output  rd_val,
    output  rd_idx
);

endinterface : letc_core_forwarder_if
