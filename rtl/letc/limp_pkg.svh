/*
 * File:    limp_pkg.svh
 * Brief:   LETC Internal Memory Protocol definitions and helper functions
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

package limp_pkg;

/* ------------------------------------------------------------------------------------------------
 * Enums
 * --------------------------------------------------------------------------------------------- */

//TODO if this is going to be sort-of standardized, should we assign values to the enums?

typedef enum logic [1:0] {
    LIMP_NOP, LIMP_READ, LIMP_WRITE, LIMP_AMO_READ
} cmd_e;
typedef enum logic [1:0] {
    LIMP_NOT_READY, LIMP_READY, LIMP_READY_ILLEGAL
} status_e;
typedef enum logic [1:0] {
    LIMP_BYTE, LIMP_HALFWORD, LIMP_WORD
} size_e;

/* ------------------------------------------------------------------------------------------------
 * Structs
 * --------------------------------------------------------------------------------------------- */

typedef struct packed {
    cmd_e               cmd;
    letc_pkg::paddr_t   addr;
    letc_pkg::word_t    wdata;
    size_e              size;
} req_s;
typedef struct packed {
    status_e            status;
    letc_pkg::word_t    rdata;
} rsp_s;

/* ------------------------------------------------------------------------------------------------
 * Helper functions
 * --------------------------------------------------------------------------------------------- */

function logic req_valid(req_s req);
    return req.cmd != LIMP_NOP;
endfunction

function logic rsp_ready(rsp_s rsp);
    return rsp.status != LIMP_NOT_READY;
endfunction

function logic transfer_complete_at_posedge(req_s req, rsp_s rsp);
    return req_valid(req) && rsp_ready(rsp);
endfunction

endpackage : limp_pkg
