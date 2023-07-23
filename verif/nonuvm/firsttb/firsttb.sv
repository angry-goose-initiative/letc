
module firsttb();

logic clk;
logic rst_n;

initial begin
    $display("Starting firsttb!");
    $dumpfile(`FIRSTTB_DUMPFILE_PATH);
    $dumpvars(0, firsttb);

    clk = 1'b0;
    #1 rst_n = 1'b1;
    rst_n = 1'b0;

    repeat(1000) begin
        #1 clk = ~clk;
    end

    $display("Bye bye!");
    $finish;
end

endmodule

