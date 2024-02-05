/*
 * File:    limp_pkg.svh
 * Brief:   LETC Internal Memory Protocol definitions and helper functions
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * DEPRECATED: We're transitioning to AXI3 from this custom memory protocol
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
    LIMP_NOT_READY, LIMP_READY_READ, LIMP_READY_WRITE, LIMP_READY_ILLEGAL
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

function logic req_active(req_s req);
    return (req.cmd == LIMP_READ) || (req.cmd == LIMP_WRITE) || (req.cmd == LIMP_AMO_READ);
endfunction

function logic req_addr_valid(req_s req);
    return req_active(req);//Every access needs an address
endfunction

function logic req_wdata_valid(req_s req);
    return req.cmd == LIMP_WRITE;
endfunction

function logic req_size_valid(req_s req);
    unique case(req.cmd)
        LIMP_READ, LIMP_WRITE:  return (req.size == LIMP_BYTE) || (req.size == LIMP_HALFWORD) || (req.size == LIMP_WORD);
        LIMP_AMO_READ:          return req.size == LIMP_WORD;
        default:                return 1'd0;
    endcase
endfunction

function logic rsp_ready(rsp_s rsp);
    return (rsp.status == LIMP_READY_READ) || (rsp.status == LIMP_READY_WRITE) || (rsp.status == LIMP_READY_ILLEGAL);
endfunction

function logic rsp_rdata_valid(rsp_s rsp);
    return rsp.status == LIMP_READY_READ;
endfunction

function letc_pkg::word_t rsp_rdata_word(rsp_s rsp);
    return rsp.rdata;
endfunction

function letc_pkg::halfword_t rsp_rdata_halfword(rsp_s rsp);
    return rsp.rdata[15:0];
endfunction

function letc_pkg::byte_t rsp_rdata_byte(rsp_s rsp);
    return rsp.rdata[7:0];
endfunction

function logic transfer_complete_at_posedge(req_s req, rsp_s rsp);
    return req_active(req) && rsp_ready(rsp);
endfunction

endpackage : limp_pkg
