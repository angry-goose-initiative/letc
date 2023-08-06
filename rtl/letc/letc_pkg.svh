/*
 * File:    letc_pkg.svh
 * Brief:   TODO
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

package letc_pkg;

    typedef logic [33:0] paddr_t;
    typedef logic [31:0] word_t;
    typedef logic [15:0] halfword_t;
    typedef logic [7:0]  byte_t;

    //TODO perhaps move limp stuff to a different file?
    typedef enum logic [1:0] {
        /*LIMP_NOP,*/ LIMP_READ, LIMP_WRITE, LIMP_AMO_READ
    } limp_cmd_e;
    typedef enum logic [1:0] {
        LIMP_BYTE, LIMP_HALF, LIMP_WORD
    } limp_size_e;

    typedef struct packed {
        logic       valid;//TODO Not needed since we can just check if cmd is not LIMP_NOP?
        limp_cmd_e  cmd;
        paddr_t     addr;
        word_t      wdata;
        limp_size_e size;
    } limp_req_s;
    typedef struct packed {
        logic  ready;
        logic  illegal;
        word_t rdata;
    } limp_rsp_s;

endpackage : letc_pkg
