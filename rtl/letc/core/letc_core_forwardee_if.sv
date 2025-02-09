/*
 * File:    letc_core_forwardee_if.sv
 * Brief:   Interface from adhesive to stages that need forwarded data
 *
 * Copyright:
 *  Copyright (C) 2025 Nick Chan
 *  Copyright (C) 2025 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
*/

interface letc_core_forwardee_if;

import riscv_pkg::*;
import letc_core_pkg::*;

// - This interface is for a single register. If a stage holds/uses both rs1
//   and rs2, then it will have two instances of this interface.
// - "reg" is the register that the stage holds/uses.
// - `stage_uses_reg` indicates if the stage uses reg, not if the instruction
//   that the stage contains will use the reg at any point in the pipeline.
// - A stage must account for its flopped valid signal when producing
//   `stage_uses_reg`.

//FIXME remove these once testbenches actually use and test them
//verilator lint_save
//verilator lint_off UNUSEDSIGNAL

logic       stage_uses_reg;
reg_idx_t   reg_idx;
logic       use_fwd;
word_t      fwd_val;

//verilator lint_restore

modport fwd_factory (
    input   stage_uses_reg,
    input   reg_idx,
    output  use_fwd,
    output  fwd_val
);

modport stage (
    output  stage_uses_reg,
    output  reg_idx,
    input   use_fwd,
    input   fwd_val
);

endinterface : letc_core_forwardee_if
