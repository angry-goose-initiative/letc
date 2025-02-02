/**
 * File    letc_core_dmss_if.sv
 * Brief   Interface between pipeline stages and the DMSS
 *
 * Copyright:
 *  Copyright (C) 2025 Nick Chan
 *  Copyright (C) 2025 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
*/

// verilator lint_save
// verilator lint_off UNUSEDSIGNAL

interface letc_core_dmss_if;

import riscv_pkg::*;
import letc_core_pkg::*;

// logic   dmss1_flop_en;
// logic   dmss1_ready;
// logic   load_req;
// logic   store_req;
vaddr_t load_addr;

// logic   dmss2_flop_en;
// logic   dmss2_ready;
word_t  load_data;

word_t  store_data;
vaddr_t store_addr;//TODO or should this be physical, with virtual translation having happened earlier?
logic   store_en;

modport memory1 (
    output  load_addr
);

modport memory2 (
    input   load_data
);

modport writeback (
    output  store_data,
    output  store_addr,
    output  store_en
);

modport subsystem (
    input   load_addr,
    output  load_data,
    input   store_data,
    input   store_addr,
    input   store_en
);

endinterface : letc_core_dmss_if
