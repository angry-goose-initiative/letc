/*
 * File:    example_pkg.sv
 * Brief:   An example SystemVerilog package file
 *
 * Copyright:
 *  Copyright (C) 2024 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * This file is part of a set of example files used to demonstrate
 * hardware/RTL/SystemVerilog concepts to those new to digital logic design.
 *
 * A SystemVerilog package is a collection of constants (called parameters), types,
 * functions, and other items that can be used in multiple files.
 *
 * You can use this in a module for example by prefixing one of these items with the package name.
 * For example, you can do `example_pkg::EXAMPLE_PARAMETER` to use the `EXAMPLE_PARAMETER` parameter.
 *
 * If that's painful to do each time, you can also `import example_pkg::EXAMPLE_PARAMETER;`
 * in a module's definition to use the parameter without the package name. Or you can import the
 * whole thing with `import example_pkg::*;`!
 *
 * Importing packages, as opposed to `including files containing definitions, is considered best
 * practice.
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Package Definition
 * --------------------------------------------------------------------------------------------- */

package example_pkg;//Convention is to make the package name the same as the file name

/* ------------------------------------------------------------------------------------------------
 * Parameters
 * --------------------------------------------------------------------------------------------- */

//verilator lint_save
//verilator lint_off UNUSEDPARAM
parameter EXAMPLE_PARAMETER = 32'hDEADBEEF;
parameter EXAMPLE_TYPE_LEN  = 5;

//verilator lint_restore

/* ------------------------------------------------------------------------------------------------
 * Typedefs
 * --------------------------------------------------------------------------------------------- */

//This is a vector of bits, with a length of EXAMPLE_TYPE_LEN
//You can refer to this as `example_type_t` in your code which can be useful for readability!
typedef logic [EXAMPLE_TYPE_LEN-1:0] example_type_t;

/* ------------------------------------------------------------------------------------------------
 * Structs
 * --------------------------------------------------------------------------------------------- */

//ALWAYS ALWAYS ALWAYS use the `packed` keyword when defining structs in SystemVerilog!
//Otherwise the struct may not be synthesizable!
typedef struct packed {
    logic valid;
    example_type_t data;
} example_struct_s;

//You can access struct members like this:
//`example_struct_s.valid` or `example_struct_s.data`
//You can also access the struct as a giant array of bits because it is a packed struct!
//Example: `example_struct_s[1:0]` gets the lowest bit of `data`, and the `valid` line in one stroke!

/* ------------------------------------------------------------------------------------------------
 * Functions
 * --------------------------------------------------------------------------------------------- */

function logic example_function(input logic a, input logic b);
    return a ~^ b;//This is xnor!
endfunction

endpackage : example_pkg
