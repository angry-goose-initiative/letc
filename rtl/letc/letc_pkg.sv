/*
 * File:    letc_pkg.sv
 * Brief:   TODO
 *
 * Copyright:
 *  Copyright (C) 2023-2025 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Package Definition
 * --------------------------------------------------------------------------------------------- */

package letc_pkg;

/* ------------------------------------------------------------------------------------------------
 * Parameters
 * --------------------------------------------------------------------------------------------- */

parameter PADDR_WIDTH       = 32;//Instead of 34 bit physical address to reduce resource usage
parameter WORD_WIDTH        = 32;
parameter HALFWORD_WIDTH    = 16;
parameter BYTE_WIDTH        = 8;

/* ------------------------------------------------------------------------------------------------
 * Typedefs
 * --------------------------------------------------------------------------------------------- */

typedef logic [PADDR_WIDTH-1:0]     paddr_t;
typedef logic [WORD_WIDTH-1:0]      word_t;
typedef logic [HALFWORD_WIDTH-1:0]  halfword_t;
typedef logic [BYTE_WIDTH-1:0]      byte_t;

endpackage : letc_pkg
