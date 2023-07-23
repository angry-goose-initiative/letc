/*
 * File:    core_top.sv
 * Brief:   TODO
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

import letc_pkg::*;

module core_top (
    input clk,
    input rst_n

    //TODO other ports

);

core_control core_control_instance (.*);

//TODO all of the inner goodness

typedef enum {
    TEST_ENUM_0,
    TEST_ENUM_1,
    TEST_ENUM_2
} test_enum_t;

typedef struct packed {
    logic [7:0] a;
    logic [7:0] b;
} test_struct_t;

test_enum_t test_enum;

test_struct_t test_struct;

assign test_enum = TEST_ENUM_1;
assign test_struct.a = 8'hFF;
assign test_struct.b = 8'ha5;

endmodule
