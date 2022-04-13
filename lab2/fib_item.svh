// Ryan Laur and Benjamin Wheeler
// University of Florida

`ifndef _FIB_ITEM_SVH_
`define _FIB_ITEM_SVH_

class fib_item #(
    int INPUT_WIDTH,
    int OUTPUT_WIDTH
);
  rand bit [INPUT_WIDTH-1:0] n;
  rand bit go;
  bit [OUTPUT_WIDTH-1:0] result;
  bit overflow;

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
