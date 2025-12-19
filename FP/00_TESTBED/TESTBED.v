`timescale 1ns/10ps
//`include "PATTERN.v"
//`include "../01_RTL/detector.v"

module TESTBED;

wire clk, rst_n;

wire [89:0] InData;
wire in_valid, flagChannelorData;


wire [11:0] OutData;
wire out_valid;

initial begin
    /* iverilog format */

    // $dumpfile("waveform.vcd");
	// $dumpvars(0, TESTBED);

    /* ADFP format */

    `ifdef GATE
        $sdf_annotate("../02_SYN/Netlist/detector_syn.sdf", my_detector);
    `endif

    $fsdbDumpfile("chip.fsdb");
    $fsdbDumpvars(0, "+mda");

end

detector my_detector(
    .clk(clk),
    .rst_n(rst_n),

    .InData(InData),
    .flagChannelorData(flagChannelorData),
    .in_valid(in_valid),

    .out_valid(out_valid),
    .OutData(OutData)
);

PATTERN My_PATTERN(
    .clk(clk),
    .rst_n(rst_n),

    .InData(InData),
    .flagChannelorData(flagChannelorData),
    .in_valid(in_valid),

    .out_valid(out_valid),
    .OutData(OutData)
);
 
endmodule