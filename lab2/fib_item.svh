// Ryan Laur and Benjamin Wheeler
// University of Florida

`ifndef _fib_ITEM_SVH_
`define _fib_ITEM_SVH_

class fib_item #(
    int WIDTH
);
  rand bit [WIDTH-1:0] data;
  rand bit go;
  bit signed [$clog2(WIDTH*2+1)-1:0] result;

  // A uniform distribution of go values probably isn't what we want, so
  // we'll make sure go is 1'b0 90% of the time.
  constraint go_dist_c {
    go dist {
      0 :/ 90,
      1 :/ 10
    };
  }
endclass

`endif
