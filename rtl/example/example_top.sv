/*
 * File:    example_top.sv
 * Brief:   An example SystemVerilog module file!
 *
 * Copyright:
 *  Copyright (C) 2024 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * This file is part of a set of example files used to demonstrate
 * hardware/RTL/SystemVerilog concepts to those new to digital logic design.
 *
 * A SystemVerilog module is a logical grouping of combinational and sequential logic.
 *
 * A module's definition begins with a list of parameters, and input and output ports.
 * Logic is then defined in the body of the module.
 *
 * Modules can also instanciaite other modules, and can be instantiated in other modules.
 * This is great for reusing logic for organizing a design!
 *
 * Note that this only touches on a basics, there's much more you'll need to
 * learn on your own! :)
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module example_top (
    //Clock and reset lines
    input logic i_clk,
    input logic i_rst_n,//_n means active low

    //Inputs and outputs
    input  logic    a1,
    input  logic    b1,
    output logic    c1,

    input  logic    a2,
    input  logic    b2,
    input  logic    c2,
    output logic    d2,

    input  logic    a3,
    input  logic    b3,
    output logic    c3,

    //This type is defined in the example_pkg and is 5 bits wide
    output example_pkg::example_type_t counter_out,

    input  logic a4,
    output logic b4
);

/* ------------------------------------------------------------------------------------------------
 * Module Body
 * --------------------------------------------------------------------------------------------- */

//You can model combinational logic with `assign` statements. Changing the
//inputs will change the outputs "immediately" (rather than waiting for a clock edge).
assign c1 = a1 & b1;

//If your logic is more complicated, it could make sense to use a `always_comb` block
logic intermediate;
always_comb begin
    intermediate    = a2 | b2;
    d2              = intermediate & c2;
end

//You can use functions in combinational logic too!
always_comb begin
    c3 = example_pkg::example_function(a3, b3);
end

//Note the use of the "blocking assignment operator", `=`, in these cases!
//THIS IS IMPORTANT, as in SystemVerilog, there are two types of assignment operators!
//You'll see the other shortly!

//Seqential logic is where things get more interesting! You model flip-flops with `always_ff` blocks.
//Here we use the "non-blocking assignment operator", `<=`.
always_ff @(posedge i_clk) begin
    if (!i_rst_n) begin//If the reset line goes low...
        //Clear the counter
        counter_out <= '0;
    end else begin//Otherwise a positive clock edge occurred!
        //Increment the counter by 1
        //5'd1 is a 5-bit wide decimal literal 1
        counter_out <= counter_out + 5'd1;
    end
end

//Why is it important to use non-blocking assignments in sequential logic?
//Well, what if you want to do a shift register, like this:
logic [2:0] shift_reg_stage;//Three shift register stages
always_ff @(posedge i_clk) begin
    if (!i_rst_n) begin
        //Clear all shift register stages
        //'0 is shorthand for an all-zero bit vector (matches the size based on context)
        shift_reg_stage     <= '0;
        //Also clear the b4 output
        b4                  <= 1'b0;
    end else begin
        //On each clock cycle, data moves to the next stage. So it will take
        //4 clock cycles from the time a4 is set to a value for it to appear at b4.

        shift_reg_stage[0]  <= a4;
        shift_reg_stage[1]  <= shift_reg_stage[0];
        shift_reg_stage[2]  <= shift_reg_stage[1];
        b4                  <= shift_reg_stage[2];

        //Note that if we had used the blocking assignment operator `=` here, this logic
        //would have behaved entirely differently! Instead after a single clock cycle,
        //all stages and b4 would take on a4's value at once! This is not what we want!
        /*
        shift_reg_stage[0] = a4;
        shift_reg_stage[1] = shift_reg_stage[0];
        shift_reg_stage[2] = shift_reg_stage[1];
        b4                 = shift_reg_stage[2];
        */
    end
end

//SIMPLE RULE TO REMEMBER: Use non-blocking assignments in sequential logic, and blocking assignments in combinational logic!

endmodule : example_top
