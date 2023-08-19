/*
 * File:    jzj_cycloneiv_wrapper_top.sv
 * Brief:   TODO
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

module jzj_cycloneiv_wrapper_top
    //import letc_pkg::*;
(
    input   logic       clk,//Pin 25
    input   logic       rst_n,//Pin 23

    input   logic[3:0]  key,//Pins 91:88//TODO or is this backwards?

    output  logic       buzzer,//Pin 110

    output  logic[3:0]  led,//Pins 87:84//TODO or is this backwards?

    output  logic[1:0]  i2c_scl,//Pins 112, 99
    inout   logic[1:0]  i2c_sda,//Pins 113, 98

    output  logic       vga_hsync,//Pin 101
    output  logic       vga_vsync,//Pin 103
    output  logic       vga_r,//Pin 106
    output  logic       vga_g,//Pin 105
    output  logic       vga_b,//Pin 104

    output  logic[3:0]  seven_seg_digit_sel,//TODO
    output  logic[7:0]  seven_seg_segment,//TODO

    output  logic       ps2_clk,//Pin 119
    output  logic       ps2_data,//Pin 120

    input   logic       ir,//Pin 100

    output  logic       uart_tx,//Pin 114
    input   logic       uart_rx//Pin 115

    //TODO LCD lines

    //TODO SDRAM lines
);

letc_top letc_top_inst (.*);

//TODO other things

/*
true_dual_port_ram_single_clock (
    .data_a({i2c_sda, key}),
    .data_b({i2c_sda, key}),
    .addr_a({i2c_sda, key}),
    .addr_b({key, i2c_sda}),
    .we_a(ir),
    .we_b(uart_rx),
    .clk_a(clk),
    .clk_b(rst_n),
    .q_a(seven_seg_digit_sel),
    .q_b(seven_seg_segment)
);
*/
//TESTING
intel_fpga_sram #(
    .DEPTH(1024),
    .DATA_WIDTH(32)
) sram_inst (
    .clk({clk, clk}),
    .we({ir, ir}),
    .addr({i2c_sda, key}),
    .wdata({i2c_sda, key}),
    .rdata({seven_seg_digit_sel, seven_seg_segment}),
    .wmask('0)
);

endmodule : jzj_cycloneiv_wrapper_top
