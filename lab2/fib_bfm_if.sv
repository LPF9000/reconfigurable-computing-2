// Ryan Laur and Benjamin Wheeler
// University of Florida

interface fib_bfm_if #(
    parameter int INPUT_WIDTH,
    parameter int OUTPUT_WIDTH
) (
    input logic clk,
    input [INPUT_WIDTH-1:0] i_r,
    input [OUTPUT_WIDTH-1:0] x_r, y_r, full_add_r
);
  logic rst, go, done, overflow;
  logic [ INPUT_WIDTH-1:0] n;
  logic [OUTPUT_WIDTH-1:0] result;

  task automatic wait_for_done();
    //@(posedge clk iff (done == 1'b0));
    //@(posedge clk iff (done == 1'b1));
    @(posedge done);
  endtask

  task automatic reset(int cycles);
    rst <= 1'b1;
    go  <= 1'b0;
    for (int i = 0; i < cycles; i++) @(posedge clk);
    @(negedge clk);
    rst <= 1'b0;
    @(posedge clk);
  endtask

  task automatic start(input logic [INPUT_WIDTH-1:0] n_);
    n  <= n_;
    go <= 1'b1;
    @(posedge clk);
    go <= 1'b0;
  endtask  // start

  // Helper code to detect when the DUT starts executing. This task internally
  // tracks the active status of the DUT and sends an event every time it
  // becomes active. With this strategy, the implementation specific details
  // are limited to the BFM and are hidden from the testbench.
  event active_event;
  event inactive_event;
  task automatic monitor();
    logic is_active;
    is_active = 1'b0;

    forever begin
      @(posedge clk);
      if (rst) begin
        is_active = 1'b0;
      end else begin
        if (done) is_active = 1'b0;
        if (!is_active && go) begin

          is_active = 1'b1;
          // The event is needed because there will be times in the
          // simulation where go and done are asserted at the same time.
          // If the code simply used @(posedge is_active) to detect the
          // start of a test, it would miss these instances because
          // there wouldn't be a rising edge on is_active. It would simply
          // remain active between two consecutive tests.
          ->active_event;
        end
      end
    end
  endtask  // monitor
endinterface
