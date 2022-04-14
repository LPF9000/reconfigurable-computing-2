// Ryan Laur and Benjamin Wheeler
// University of Florida

`include "test.svh"

module fib_tb;

  localparam int NUM_RANDOM_TESTS = 10;
  localparam int NUM_CONSECUTIVE_TESTS = 10;
  localparam int NUM_REPEATS = 1;
  localparam int INPUT_WIDTH = 6;
  localparam int OUTPUT_WIDTH = 32;
  logic clk;

  fib_bfm_if #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) bfm (.clk(clk));
  fib #(
      .INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)
  ) DUT (
      .clk(clk),
      .rst(bfm.rst),
      .go(bfm.go),
      .n(bfm.n),
      .result(bfm.result),
      .overflow(bfm.overflow),
      .done(bfm.done)
  );

  random_test #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) test_random = new(bfm, "Random Test");
  consecutive_test #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) test_consecutive = new(bfm, "Consecutive Test");

  initial begin : generate_clock
    clk = 1'b0;
    while (1) #5 clk = ~clk;
  end

  initial begin
    $timeformat(-9, 0, " ns");
    test_random.run(NUM_RANDOM_TESTS, NUM_REPEATS);
    test_consecutive.run(NUM_CONSECUTIVE_TESTS, NUM_REPEATS);
    test_random.report_status();
    test_consecutive.report_status();
    disable generate_clock;
  end

  assert property (@(posedge bfm.clk) disable iff (bfm.rst) bfm.go && bfm.done |=> !bfm.done);
  assert property (@(posedge bfm.clk) disable iff (bfm.rst) $fell(bfm.done) |-> $past(bfm.go, 1));

endmodule
