/*
 * File:    axi_pkg.sv
 * Brief:   AXI definitions and helper functions
 *
 * Copyright:
 *  Copyright (C) 2023-2024 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * Based on the old axi_pkg.svh
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Package Definition
 * --------------------------------------------------------------------------------------------- */

package axi_pkg;

/* ------------------------------------------------------------------------------------------------
 * Parameters
 * --------------------------------------------------------------------------------------------- */

//Adjust these as needed depending on the project
//For LETC this is 32 bits for both address and data in the Matrix, though we
//may need to upconvert to 64 bit data for the ACP connection
parameter int AWIDTH    = 32;
parameter int DWIDTH    = 32;
parameter int IDWIDTH   = 8;
parameter int LENWIDTH  = 4;//4 bits are used for AXI3, 8 for AXI4

//Derived constants
parameter int WSTRBWIDTH = DWIDTH / 8;

/* ------------------------------------------------------------------------------------------------
 * Typedefs
 * --------------------------------------------------------------------------------------------- */

typedef logic [AWIDTH-1:0]      addr_t;
typedef logic [DWIDTH-1:0]      data_t;
typedef logic [IDWIDTH-1:0]     id_t;
typedef logic [LENWIDTH-1:0]    len_t;
typedef logic [2:0]             size_t;

typedef logic [WSTRBWIDTH-1:0]  wstrb_t;

/* ------------------------------------------------------------------------------------------------
 * Enums
 * --------------------------------------------------------------------------------------------- */

typedef enum logic [1:0] {
    AXI_BURST_FIXED     = 2'b00,
    AXI_BURST_INCR      = 2'b01,
    AXI_BURST_WRAP      = 2'b10,
    AXI_BURST_RESERVED  = 2'b11
} burst_e;

typedef enum logic [1:0] {
    AXI_RESP_OKAY   = 2'b00,
    AXI_RESP_EXOKAY = 2'b01,
    AXI_RESP_SLVERR = 2'b10,
    AXI_RESP_DECERR = 2'b11
} resp_e;

/* ------------------------------------------------------------------------------------------------
 * Structs
 * --------------------------------------------------------------------------------------------- */

//Actually interfaces feel like a better fit for this

endpackage : axi_pkg
