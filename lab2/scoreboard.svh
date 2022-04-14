// Ryan Laur and Benjamin Wheeler
// University of Florida

`ifndef _SCOREBOARD_SVH_
`define _SCOREBOARD_SVH_

`include "fib_item.svh"

class scoreboard #(
    int INPUT_WIDTH,
    int OUTPUT_WIDTH
);
  mailbox scoreboard_result_mailbox;
  mailbox scoreboard_n_mailbox;
  int     passed,                      failed, reference;

  function new(mailbox scoreboard_n_mailbox, mailbox scoreboard_result_mailbox);
    this.scoreboard_n_mailbox = scoreboard_n_mailbox;
    this.scoreboard_result_mailbox = scoreboard_result_mailbox;
    //this.scoreboard_overflow_mailbox = scoreboard_overflow_mailbox;

    passed = 0;
    failed = 0;
  endfunction  // new

  // Reference model for the correct result.
  function longint result_model(int n);
    longint x, y, i, temp;
    x = 0;
    y = 1;
    i = 3;
    if (n < 2) return 0;

    while (i <= n) begin
      temp = x + y;
      x = y;
      y = temp;
      i++;
    end
    return y;
  endfunction

  // Reference overflow_model for the correct overflow.
  function logic overflow_model(longint result);
    logic [OUTPUT_WIDTH-1:0] result_truncated;
    result_truncated = result;

    // If the truncated version is the same as the full version, there
    // was no overflow.
    return result_truncated != result;
  endfunction

  task run(int num_tests);
    fib_item #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) in_item;
    fib_item #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) out_item;
    //fib_item #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) out_item2;

    for (int i = 0; i < num_tests; i++) begin

      // First wait until the driver informs us of a new test.
      scoreboard_n_mailbox.get(in_item);
      $display("Time %0t [Scoreboard]: Received start of test for n=h%h.", $time, in_item.n);

      // Then, wait until the monitor tells us that test is complete.
      scoreboard_result_mailbox.get(out_item);
      $display("Time %0t [Scoreboard]: Received result=%0d for n=h%h.", $time, out_item.result,
               in_item.n);

      //scoreboard_overflow_mailbox.get(out_item2);
      //$display("Time %0t [Scoreboard]: Received overflow=%0d for n=h%h.", $time,
      //         out_item2.overflow, in_item.n);

      // Get the correct result based on the input at the start of the test.
      reference = result_model(in_item.n);
      if (out_item.result == reference) begin
        $display("Time %0t [Scoreboard] Test passed for n=h%h", $time, in_item.n);
        passed++;
      end else begin
        $display("Time %0t [Scoredboard] Test failed: result = %0d instead of %0d for n = h%h.",
                 $time, out_item.result, reference, in_item.n);
        failed++;
      end

      // Get the correct overflow based on the input at the start of the test.
      /*reference2 = overflow_model(in_item.n);
      if (out_item2.result == reference2) begin
        $display("Time %0t [Scoreboard] Test passed for n=h%h", $time, in_item.n);
        passed++;
      end else begin
        $display("Time %0t [Scoredboard] Test failed: overflow = %0d instead of %0d for n = h%h.",
                 $time, out_item2.overflow, reference2, in_item.n);
        failed++;
      end
      */
    end  // for (int i=0; i < num_tests; i++)

    // Remove any leftover messages that might be in the mailbox upon
    // completion. This is needed for the repeat functionality to work.
    // If n is left in the mailbox when repeating a test, that n
    // will be detected as part of the current test.
    while (scoreboard_n_mailbox.try_get(in_item));
    while (scoreboard_result_mailbox.try_get(out_item));
    //while (scoreboard_overflow_mailbox.try_get(out_item2));
  endtask

  function void report_status();
    $display("Test status: %0d passed, %0d failed", passed, failed);
  endfunction

endclass

`endif