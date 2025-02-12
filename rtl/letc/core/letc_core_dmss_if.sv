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

//M1 <-> DMSS (technically combinationally from E but I digress)
logic   dmss0_req_load;
logic   dmss0_req_store;
vaddr_t dmss0_req_addr;
logic   dmss0_req_stall;//This one is ACTUALLY from m1 not E

//M2 <-> DMSS (actually in M2)
//Unlike the IMSS, no need for a stall signal TO the DMSS because nothing after M2 could possibly stall M2
logic   dmss1_rsp_ready;
word_t  dmss1_rsp_load_data;
logic   dmss1_rsp_illegal;//TODO contain bad address info?

//WB <-> DMSS (actually in M2)
logic   dmss2_req_commit;
word_t  dmss2_req_store_data;

modport memory1 (
    output dmss0_req_load,
    output dmss0_req_store,
    output dmss0_req_addr,
    output dmss0_req_stall
);

modport memory2 (
    input dmss1_rsp_ready,
    input dmss1_rsp_load_data,
    input dmss1_rsp_illegal
);

modport writeback (
    output dmss2_req_commit,
    output dmss2_req_store_data
);

modport subsystem (
    input  dmss0_req_load,
    input  dmss0_req_store,
    input  dmss0_req_addr,
    input  dmss0_req_stall,
    output dmss1_rsp_ready,
    output dmss1_rsp_load_data,
    output dmss1_rsp_illegal,
    input  dmss2_req_commit,
    input  dmss2_req_store_data
);

endinterface : letc_core_dmss_if
