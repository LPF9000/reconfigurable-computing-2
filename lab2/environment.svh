// Ryan Laur and Benjamin Wheeler
// University of Florida

`ifndef _ENVIRONMENT_SVH_
`define _ENVIRONMENT_SVH_

`include "driver.svh"
`include "generator.svh"
`include "monitor.svh"
`include "scoreboard.svh"

class environment #(
    int INPUT_WIDTH,
    int OUTPUT_WIDTH
);

  // The environment doesn't know what type of generator and driver it will
  // use, so it contains a handle to the base class for each. Use of virtual
  // methods then allows us to use any class derived from the base version
  // without requiring knowledge of the specific class here.
  base_generator #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) genarator_h;
  base_driver #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) driver_h;
  done_monitor #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) done_monitor_h;
  start_monitor #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) start_monitor_h;
  scoreboard #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) scoreboard_h;

  mailbox scoreboard_n_mailbox;
  mailbox scoreboard_result_mailbox;
  mailbox scoreboard_overflow_mailbox;
  mailbox driver_mailbox;

  event driver_done_event;

  function new(virtual fib_bfm_if #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) bfm, base_generator#(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) gen_h,
               base_driver#(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) drv_h);
    scoreboard_n_mailbox = new;
    scoreboard_result_mailbox = new;
    scoreboard_overflow_mailbox = new;
    driver_mailbox = new;

    // We no longer instantiate these here because they are created in the
    // test class and passed in to this constructor.
    genarator_h = gen_h;
    driver_h = drv_h;
    done_monitor_h = new(bfm, scoreboard_result_mailbox);
    start_monitor_h = new(bfm, scoreboard_n_mailbox);
    scoreboard_h = new(scoreboard_n_mailbox, scoreboard_result_mailbox, scoreboard_overflow_mailbox);
  endfunction  // new

  function void report_status();
    scoreboard_h.report_status();
  endfunction

  virtual task run(int num_tests);
    fork
      genarator_h.run();
      driver_h.run();
      done_monitor_h.run();
      start_monitor_h.run();
      scoreboard_h.run(num_tests);
    join_any

    disable fork;
  endtask
endclass

`endif
