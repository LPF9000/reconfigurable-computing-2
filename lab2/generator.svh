// Ryan Laur and Benjamin Wheeler
// University of Florida

`ifndef _GENERATOR_SVH_
`define _GENERATOR_SVH_

`include "driver.svh"

virtual class base_generator #(
    int INPUT_WIDTH,
    int OUTPUT_WIDTH
);

  mailbox driver_mailbox;
  event   driver_done_event;

  function new(base_driver#(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) driver_h);
    this.driver_mailbox = driver_h.driver_mailbox;
    this.driver_done_event = driver_h.driver_done_event;
  endfunction  // new

  pure virtual task run();
endclass


class random_generator #(
    int INPUT_WIDTH,
    int OUTPUT_WIDTH
) extends base_generator #(
    .INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)
);

  function new(base_driver#(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) driver_h);
    super.new(driver_h);
  endfunction  // new

  virtual task run();
    fib_item #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) item;

    // Start the consecutive sequence at 0. This could also be modified with
    // another configuration parameter.
    bit [INPUT_WIDTH-1:0] n = '0;

    forever begin
      item = new;
      if (!item.randomize()) $display("Randomize failed");
      driver_mailbox.put(item);
      @(driver_done_event);
    end
  endtask
endclass


class consecutive_generator #(
    int INPUT_WIDTH,
    int OUTPUT_WIDTH
) extends base_generator #(
    .INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)
);

  function new(base_driver#(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) driver_h);
    super.new(driver_h);
  endfunction  // new

  task run();
    fib_item #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH)) item;
    bit [INPUT_WIDTH-1:0] n = '0;

    forever begin
      item = new;
      item.n = n;
      n++;
      driver_mailbox.put(item);
      @(driver_done_event);
    end
  endtask
endclass

`endif
