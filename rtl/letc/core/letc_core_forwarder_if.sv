/**
 * File    letc_core_forwarder_if.sv
 * Brief   Interface to adhesive from stages that provide forwarded data
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

//Decide if there is a hazard, and, depending on the stage, if we should forward or stall:
// rd_we | fwd_val_avali | Action
// 0     | x             | No hazard
// 1     | 0             | Stall as appropriate
// 1     | 1             | Forward fwd_val (which is valid)
logic       rd_we;//Depending on the stage, adhesive
reg_idx_t   rd_idx;
logic       fwd_val_avail;

//The actual data to forward if that's what we decide to do
word_t      fwd_val;//The stage will have to have a mux to feed this

modport adhesive (
    input   rd_we,
    input   rd_idx,
    input   fwd_val_avail,
    input   fwd_val
);

modport stage (
    output  rd_we,
    output  rd_idx,
    output  fwd_val_avail,
    output  fwd_val
);

endinterface : letc_core_forwarder_if
