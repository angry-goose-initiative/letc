/**
 * File    letc_core_forwardee_if.sv
 * Brief   Interface from adhesive to stages that need forwarded data
 *
 * Copyright:
 *  Copyright (C) 2025 Nick Chan
 *  Copyright (C) 2025 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * One of these per register operand a stage may need
 *
*/

// verilator lint_save
// verilator lint_off UNUSEDSIGNAL

interface letc_core_forwardee_if;

import riscv_pkg::*;
import letc_core_pkg::*;

logic       reg_idx_valid;//Useful for avoiding unnecessary stalls
reg_idx_t   reg_idx;
logic       use_fwd;
word_t      fwd_val;

modport adhesive (
    input   reg_idx_valid,
    input   reg_idx,
    output  use_fwd,
    output  fwd_val
);

modport stage (
    output  reg_idx_valid,
    output  reg_idx,
    input   use_fwd,
    input   fwd_val
);

endinterface : letc_core_forwardee_if
