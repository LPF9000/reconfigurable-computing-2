// Ryan Laur and Benjamin Wheeler
// University of Florida

`ifndef _MONITOR_SVH_
`define _MONITOR_SVH_

`include "fib_item.svh"

virtual class base_monitor #(
    int INPUT_WIDTH,
    int OUTPUT_WIDTH
);
  virtual fib_bfm_if #(
      .INPUT_WIDTH (INPUT_WIDTH),
      .OUTPUT_WIDTH(OUTPUT_WIDTH)
  ) bfm;

  function new(
  virtual fib_bfm_if #(
  .INPUT_WIDTH (INPUT_WIDTH),
  .OUTPUT_WIDTH(OUTPUT_WIDTH)
  ) bfm);
    this.bfm = bfm;
  endfunction  // new

  pure virtual task run();
endclass


class done_monitor #(
    int INPUT_WIDTH,
    int OUTPUT_WIDTH
) extends base_monitor #(
    .INPUT_WIDTH (INPUT_WIDTH),
    .OUTPUT_WIDTH(OUTPUT_WIDTH)
);
  mailbox scoreboard_result_mailbox;

  function new(
  virtual fib_bfm_if #(
      .INPUT_WIDTH (INPUT_WIDTH),
      .OUTPUT_WIDTH(OUTPUT_WIDTH)
  ) bfm,
               mailbox _scoreboard_result_mailbox);
    super.new(bfm);
    scoreboard_result_mailbox = _scoreboard_result_mailbox;
  endfunction  // new

  virtual task run();
    $display("Time %0t [Monitor]: Monitor starting.", $time);

    forever begin
      fib_item #(
          .INPUT_WIDTH (INPUT_WIDTH),
          .OUTPUT_WIDTH(OUTPUT_WIDTH)
      ) item = new;
      bfm.wait_for_done();
      item.result   = bfm.result;
      item.overflow = bfm.overflow;
      $display("Time %0t [Monitor]: Monitor detected result=%0d and overflow=%0d.", $time,
               bfm.result, bfm.overflow);
      scoreboard_result_mailbox.put(item);
    end
  endtask
endclass


class start_monitor #(
    int INPUT_WIDTH,
    int OUTPUT_WIDTH
) extends base_monitor #(
    .INPUT_WIDTH (INPUT_WIDTH),
    .OUTPUT_WIDTH(OUTPUT_WIDTH)
);
  mailbox scoreboard_n_mailbox;

  function new(
  virtual fib_bfm_if #(
      .INPUT_WIDTH (INPUT_WIDTH),
      .OUTPUT_WIDTH(OUTPUT_WIDTH)
  ) bfm,
               mailbox _scoreboard_n_mailbox);
    super.new(bfm);
    scoreboard_n_mailbox = _scoreboard_n_mailbox;
  endfunction  // new

  virtual task run();
    fork
      // Start the BFM monitor to track the active status.
      bfm.monitor();
      detect_start();
    join_any
  endtask

  task detect_start();
    forever begin
      fib_item #(
          .INPUT_WIDTH (INPUT_WIDTH),
          .OUTPUT_WIDTH(OUTPUT_WIDTH)
      ) item = new;

      // Wait until the DUT becomes active.
      @(bfm.active_event);
      item.n = bfm.n;
      $display("Time %0t [start_monitor]: Sending start of test for n=h%h.", $time, item.n);
      scoreboard_n_mailbox.put(item);
    end
  endtask
endclass

`endif
