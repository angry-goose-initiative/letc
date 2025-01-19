/*
 * File:    cdc_synchronizer.sv
 * Brief:   Simple synchronizer for crossing clock domains
 *
 * Copyright (C) 2024 John Jekel
 * See the LICENSE file at the root of the project for licensing info.
 *
 * DO NOT JUST USE THIS BLINDLY WHEN CROSSING CLOCK DOMAINS
 * You may need to make use of ex. grey codes or other techniques depending on your requirements
 *
*/

/* ------------------------------------------------------------------------------------------------
 * Module Definition
 * --------------------------------------------------------------------------------------------- */

module cdc_synchronizer #(
    parameter int WIDTH = 1,
    parameter int STAGES = 3//AT MINIMUM THIS SHOULD BE 2; more than 4 is likely overkill
) (
    //Clock to synchronize to
    input  logic                i_clk,
    input  logic [WIDTH-1:0]    i_async_data,
    output logic [WIDTH-1:0]    o_sync_data
);

logic [STAGES-1:0] [WIDTH-1:0] sync_data;

always_ff @(posedge i_clk) begin
    sync_data[0] <= i_async_data;
    for (int ii = 0; ii < (STAGES - 1); ++ii) begin
        sync_data[ii + 1] <= sync_data[ii];
    end
end

assign o_sync_data = sync_data[STAGES - 1];

endmodule : cdc_synchronizer
