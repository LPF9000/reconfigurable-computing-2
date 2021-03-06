// Ryan Laur
// University of Florida

// Datapath to count the number of bits asserted in a number
module register #(
    parameter int WIDTH
) (
    input logic clk,
    input logic rst,
    input logic en,
    input logic [WIDTH-1:0] in,
    output logic [WIDTH-1:0] out
);

  always_ff @(posedge clk or posedge rst) begin
    if (rst) out <= '0;
    else if (en) out <= in;
  end
endmodule

module mux2x1 #(
    parameter int WIDTH
) (
    input  logic [WIDTH-1:0] in0,
    input  logic [WIDTH-1:0] in1,
    input  logic             sel,
    output logic [WIDTH-1:0] out
);

  assign out = sel == 1'b1 ? in1 : in0;

endmodule

module add #(
    parameter int WIDTH
) (
    input  logic [WIDTH-1:0] in0,
    in1,
    output logic [WIDTH-1:0] sum
);

  assign sum = in0 + in1;

endmodule

module and_gate #(
    parameter int WIDTH
) (
    input  logic [WIDTH-1:0] in0,
    in1,
    output logic [WIDTH-1:0] sum
);

  assign sum = in0 & in1;

endmodule

module eq #(
    parameter int WIDTH
) (
    input  logic [WIDTH-1:0] in0,
    in1,
    output logic             out
);

  assign out = in0 == in1 ? 1'b1 : 1'b0;

endmodule

module datapath_str #(
    parameter int WIDTH
) (
    input  logic                       clk,
    input  logic                       rst,
    input  logic [          WIDTH-1:0] in,
    input  logic                       n_sel,
    input  logic                       n_en,
    input  logic                       count_sel,
    input  logic                       count_en,
    input  logic                       out_en,
    output logic                       count_done,
    output logic [$clog2(WIDTH+1)-1:0] out
);

  localparam int COUNT_WIDTH = $clog2(WIDTH + 1);
  localparam int OUT_WIDTH = $clog2(WIDTH + 1);

  logic [$bits(in)-1:0] n_r, n_sub, n_and_sub, n_mux;
  logic [$clog2(WIDTH):0] count_r, count_add, count_mux;

  // Mux that defines provides input to the data register.
  mux2x1 #(
      .WIDTH(WIDTH)
  ) MUX_N (
      .in0(in),
      .in1(n_and_sub),
      .sel(n_sel),
      .out(n_mux)
  );

  // The data register.
  register #(
      .WIDTH(WIDTH)
  ) N_REG (
      .en (n_en),
      .in (n_mux),
      .out(n_r),
      .*
  );
  // Adds the current difference with the output of the add_in1_mux (1 or -1).
  add #(
      .WIDTH(WIDTH)
  ) SUB_ONE (
      .in0(n_r),
      .in1(WIDTH'(-1)),
      .sum(n_sub)
  );

  // Adds the current difference with the output of the add_in1_mux (1 or -1).
  and_gate #(
      .WIDTH(WIDTH)
  ) N_AND (
      .in0(n_r),
      .in1(n_sub),
      .sum(n_and_sub)
  );

  // Comparator to check when the count is complete. Equivalent to
  // count_r == WIDTH-1 from the FSMD.
  eq #(
      .WIDTH(WIDTH)
  ) EQ (
      .in0(WIDTH'(0)),
      .in1(n_r),
      .out(count_done)
  );

  // Selects between a 1 or -1 input to the adder.
  mux2x1 #(
      .WIDTH(COUNT_WIDTH)
  ) CNT_MUX (
      .in0(COUNT_WIDTH'(0)),
      .in1(count_add),
      .sel(count_sel),
      .out(count_mux)
  );

  // The count register.
  register #(
      .WIDTH(COUNT_WIDTH)
  ) CNT_REG (
      .en (count_en),
      .in (count_mux),
      .out(count_r),
      .*
  );

  // Adds the current difference with the output of the add_in1_mux (1 or -1).
  add #(
      .WIDTH(COUNT_WIDTH)
  ) CNT_ADD (
      .in0(COUNT_WIDTH'(1)),
      .in1(count_r),
      .sum(count_add)
  );

  // The diff register.
  register #(
      .WIDTH(OUT_WIDTH)
  ) DIFF_REG (
      .en (out_en),
      .in (count_r),
      .out(out),
      .*
  );

endmodule

module datapath_bhv #(
    parameter int WIDTH
) (
    input  logic                       clk,
    input  logic                       rst,
    input  logic [          WIDTH-1:0] in,
    input  logic                       n_sel,
    input  logic                       n_en,        // TODO this is always 1'b1. Not needed ?
    input  logic                       count_sel,
    input  logic                       count_en,
    input  logic                       out_en,
    output logic                       count_done,
    output logic [$clog2(WIDTH+1)-1:0] out
);

  logic [$bits(in)-1:0] n_r, count_r;
  logic [$bits(in)-1:0] sub_and_n_r;

  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      n_r <= '0;
      count_r <= '0;
      out <= '0;
    end else begin
      n_r <= n_sel ? sub_and_n_r : in;
      if (count_en) count_r <= count_sel ? count_r + 1 : '0;
      if (out_en) out <= count_r;
    end
  end  // always_ff

  always_comb begin
    sub_and_n_r = (n_r - 1'b1) & n_r;
    count_done  = n_r == '0;
  end

endmodule


module datapath #(
    parameter int WIDTH
) (
    input  logic                       clk,
    input  logic                       rst,
    input  logic [          WIDTH-1:0] in,
    input  logic                       n_sel,
    input  logic                       n_en,
    input  logic                       count_sel,
    input  logic                       count_en,
    input  logic                       out_en,
    output logic                       count_done,
    output logic [$clog2(WIDTH+1)-1:0] out
);

  datapath_bhv #(WIDTH) top (.*);
  //datapath_str #(WIDTH) top (.*);

endmodule
