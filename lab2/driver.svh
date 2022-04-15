// Ryan Laur and Benjamin Wheeler
// University of Florida

`ifndef _DRIVER_SVH_
`define _DRIVER_SVH_

`include "fib_item.svh"

virtual class base_driver #(
    int INPUT_WIDTH,
    int OUTPUT_WIDTH
);
  virtual fib_bfm_if #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) bfm;
  mailbox driver_mailbox;
  event driver_done_event;

  function new(virtual fib_bfm_if #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) bfm);
    this.bfm = bfm;
    driver_mailbox = new;
  endfunction  // new

  pure virtual task run();
endclass  // base_driver


class nonblocking_driver #(
  int INPUT_WIDTH,
  int OUTPUT_WIDTH
) extends base_driver #(
    .INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)
);

  function new(virtual fib_bfm_if #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) bfm);
    super.new(bfm);
  endfunction  // new

  virtual task run();
    fib_item #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) item;
    $display("Time %0t [Driver]: Driver starting.", $time);

    forever begin
      driver_mailbox.get(item);
      //$display("Time %0t [Driver]: Driving n=h%h, go=%0b.", $time, item.n, item.go);
      bfm.n = item.n;
      bfm.go   = item.go;
      @(posedge bfm.clk); // Shouldn't this be bfm.wait_for_done() ?
      ->driver_done_event;
    end
  endtask
endclass


class blocking_driver #(
    int INPUT_WIDTH,
    int OUTPUT_WIDTH
) extends base_driver #(
    .INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)
);

  function new(virtual fib_bfm_if #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) bfm);
    super.new(bfm);
  endfunction  // new

  task run();
    fib_item #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) item;
    $display("Time %0t [Driver]: Driver starting.", $time);

    forever begin
      driver_mailbox.get(item);
      bfm.start(item.n);
      bfm.wait_for_done();
      $display("Time %0t [Driver]: Detected done.", $time);
      ->driver_done_event;
    end
  endtask
endclass

`endif
