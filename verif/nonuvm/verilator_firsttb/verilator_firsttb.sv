/*
 * File:    verilator_firsttb.sv
 * Brief:   TODO
 *
 * Copyright (C) 2023 John Jekel and Nick Chan
 * See the LICENSE file at the root of the project for licensing info.
 *
 * TODO longer description
 *
*/

module verilator_firsttb();

logic clk;
logic rst_n;

letc_top letc_top_instance (.*);

initial begin
    $display("Starting verilator_firsttb!");
    $dumpfile(`VERILATOR_FIRSTTB_DUMPFILE_PATH);
    $dumpvars(0, firsttb);

    clk = 1'b0;
    rst_n = 1'b0;
    #1 rst_n = 1'b1;

    repeat(1000) begin
        #1 clk = ~clk;
    end

    $display("Bye bye!");
    $finish;
end

endmodule
