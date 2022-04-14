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

  fib_bfm_if #(
      .INPUT_WIDTH (INPUT_WIDTH),
      .OUTPUT_WIDTH(OUTPUT_WIDTH)
  ) bfm (
      .clk(clk)
  );

  bind fib fib_bfm_if bfm(.*);
  /*
  fib #(
      .INPUT_WIDTH (INPUT_WIDTH),
      .OUTPUT_WIDTH(OUTPUT_WIDTH)
  ) DUT (
      .clk(clk),
      .rst(bfm.rst),
      .go(bfm.go),
      .n(bfm.n),
      .result(bfm.result),
      .overflow(bfm.overflow),
      .done(bfm.done),
  );
*/
  random_test #(
      .INPUT_WIDTH (INPUT_WIDTH),
      .OUTPUT_WIDTH(OUTPUT_WIDTH)
  ) test_random = new(
      bfm, "Random Test"
  );
  consecutive_test #(
      .INPUT_WIDTH (INPUT_WIDTH),
      .OUTPUT_WIDTH(OUTPUT_WIDTH)
  ) test_consecutive = new(
      bfm, "Consecutive Test"
  );

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

  /*The implication construct (|->) allows a user to monitor sequences based on satisfying some
  criteria, e.g. attach a precondition to a sequence and evaluate the sequence only if the condition
  is successful. The left-hand side operand of the implication is called the antecedent sequence expression,
  while the right-hand side is called the consequent sequence expression.

  If there is no match of the antecedent sequence expression, implication succeeds
  vacuously by returning true. If there is a match, for each successful match of the antecedent
  sequence expression, the consequent sequence expression is separately evaluated, beginning at
  the end point of the match.

  There are two forms of implication: overlapped using operator |->, and non-overlapped using operator |=>.

  For overlapped implication, if there is a match for the antecedent sequence expression, then the
  first element of the consequent sequence expression is evaluated on the same clock tick.

  For non-overlapped implication, the first element of the consequent sequence expression
  is evaluated on the next clock tick.*/

  // if go and done are both asserted, done should be cleared on the next cycle
  assert property (@(posedge bfm.clk) disable iff (bfm.rst) bfm.go && bfm.done |=> !bfm.done)
  else $error("Time %0t [Assert Property]: Done=1, go=1, done not cleared next cycle.", $time);

  // if done is asserted, but go is not asserted, done should remain true.
  assert property (@(posedge bfm.clk) disable iff (bfm.rst) bfm.done && $stable(
      bfm.done
  ) && !bfm.go |=> $stable(
      bfm.done
  ))
  else $error("Time %0t [Assert Property]: Done=1, go=0, done not stable.", $time);

  // if done is cleared, then go should have been asserted on the previous clock cycle
  assert property (@(posedge bfm.clk) disable iff (bfm.rst) $fell(bfm.done) |-> $past(bfm.go, 1))
  else $error("Time %0t [Assert Property]: done not cleared after go asserted.", $time);

  // go must be cleared for done to be asserted
  assert property (@(posedge bfm.clk) disable iff (bfm.rst) $rose(bfm.done) |-> $past(!bfm.go, 1))
  else $error("Time %0t [Assert Property]: Go did not return to 0", $time);

  // upon completion, (ie done = 1), result and overflow retain their values until circuit is restarted
  assert property (@(posedge bfm.clk) disable iff (bfm.rst) bfm.done && $stable(
      bfm.done
  ) |-> $stable(
      bfm.result
  ))
  else $error("Time %0t [Assert Property]: Done=1, result not stable.", $time);
  // upon completion, (ie done = 1), result and overflow retain their values until circuit is restarted
  assert property (@(posedge bfm.clk) disable iff (bfm.rst) bfm.done && $stable(
      bfm.done
  ) |-> $stable(
      bfm.overflow
  ))
  else $error("Time %0t [Assert Property]: Done=1, overflow not stable.", $time);

endmodule

/*
Design specifican bullet points:

Done: 1 2 3 4 8
Not done: 5 6 9
Skipping: 7

To do:

7. Fixing the design

*/
