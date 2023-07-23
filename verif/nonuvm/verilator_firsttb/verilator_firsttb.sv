//Intended for use with verilator
//Based on tb from vgacpu

module verilator_firsttb(
    //input logic clk,
    //input logic rst_n
);

logic clk;
logic rst_n;

letc_top letc_top_instance (.*);

initial begin
    $display("Starting firsttb!");
    $dumpfile(`FIRSTTB_DUMPFILE_PATH);
    $dumpvars(0, firsttb);

    clk = 1'b0;
    rst_n = 1'b1;
    #1 rst_n = 1'b0;

    repeat(1000) begin
        #1 clk = ~clk;
    end

    $display("Bye bye!");
    $finish;
end

/*
initial begin
    $dumpfile("/tmp/vgacpu_verilator.vcd");
    $dumpvars(0, vgacpu_verilator);
end

//Clock cycle counter to end simulation
logic [63:0] counter = 0;

always_ff @(posedge clk) begin
    counter <= counter + 1;

    if (counter == 1000000)
        $finish();
end
*/

endmodule
