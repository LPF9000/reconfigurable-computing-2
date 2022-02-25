// Ryan Laur
// University of Florida

// 2-Process FSM Module
module fsm_bhv (
    input  logic clk,
    input  logic rst,
    input  logic go,
    input  logic count_done,
    output logic done,
    output logic n_sel,
    output logic n_en,
    output logic count_sel,
    output logic count_en,
    output logic out_en
);

  typedef enum logic [1:0] {
    START,
    COMPUTE,
    RESTART
  } state_t;
  state_t state_r, next_state;

  always_ff @(posedge clk or posedge rst) begin
    if (rst) state_r <= START;
    else state_r <= next_state;
  end

  always_comb begin

    done       = 1'b0;
    out_en     = 1'b0;
    count_en   = 1'b0;
    count_sel  = 1'b0;
    n_sel      = 1'b0;

    next_state = state_r;

    case (state_r)
      START: begin

        // Replaces count_r <= '0;
        count_en = 1'b1;
        //count_sel = 1'b1;

        // Replaces data_r <= data;
        n_en = 1'b1;
        //n_sel = 1'b1;

        if (go) next_state = COMPUTE;
      end

      COMPUTE: begin

        count_sel = 1'b1;
        count_en = 1'b1;

        // Replaces data_r <= data_r >> 1;
        n_en = 1'b1;
        n_sel = 1'b1;

        // Replaces count_r == WIDTH-1
        if (count_done) begin
          // Enable the result register one cycle early to make sure it
          // aligns with the assertion of done.
          out_en = 1'b1;
          next_state = RESTART;
        end
      end

      RESTART: begin
        // Assert done in this state.
        done      = 1'b1;

        // Replaces count_r <= '0;
        count_en  = 1'b1;
        count_sel = 1'b0;

        // Replaces data_r <= data
        n_en      = 1'b1;
        n_sel     = 1'b0;

        if (go) next_state = COMPUTE;

      end
      default: ;

    endcase
  end
endmodule

module fsm (
    input  logic clk,
    input  logic rst,
    input  logic go,
    input  logic count_done,
    output logic done,
    output logic n_sel,
    output logic n_en,
    output logic count_sel,
    output logic count_en,
    output logic out_en
);

  fsm_bhv top (.*);

endmodule
