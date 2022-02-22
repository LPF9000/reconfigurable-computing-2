// Ryan Laur
// University of Florida

// 1-process FSMD here.
module asserted_bit_count_fsmd_1p
  #(parameter int WIDTH)
  (
  input   logic 		                  clk,
  input   logic 		                  rst,
  input   logic 		                  go,
  input   logic [WIDTH-1:0] 	        in,
  output  logic [$clog2(WIDTH+1)-1:0] out,
  output  logic 		                  done 
  );

  typedef enum 				{S_START, S_INIT, S_COND, S_COMPUTE, S_RESULT, S_DONE} state_t;
  // We only have one process, so we'll only have a state_r variable.
  state_t state_r;

  // Create variables for the internal registers.
  logic [$bits(in)-1:0] 	  n_r;
  logic [$bits(out)-1:0] 	  out_r;
  logic [$clog2(WIDTH)-1:0] count_r;
  logic 					          done_r;

  assign out  = out_r;
  assign done = done_r;

  // In the 1-process FSMD, everything is captured in a single always block.
  // It doesn't have to be an always_ff block in case there is combinational
  // logic mixed into the assignments, but use the always_ff when possible.
  always_ff @(posedge clk or posedge rst) begin
    if (rst == 1'b1) begin	 	 
      out_r   <= '0;
      done_r  <= 1'b0;	 	 
      count_r <= '0;
      n_r     <= '0;	 
      state_r <= S_START;	 
    end
    else begin
	    done_r <= 1'b0;	 
      case (state_r)
        S_START : begin
          if (go == 1'b1) state_r <= S_INIT;	
        end
        S_INIT : begin
          // Assign outputs.
          done_r  <= 1'b0;
          out_r   <= '0;
              
          // Initialize internal state.
          count_r <= '0;
          n_r     <= in;

          state_r <= S_COND;       
        end
        S_COND : begin
          // Go to result state if n_r reaches 0, else go to compute state
          done_r  <= 1'b0;
          state_r <= n_r == '0 ? S_RESULT : S_COMPUTE;  
        end

        S_COMPUTE : begin
          // Move to next asserted bit
          n_r     <= n_r & (n_r - 1'b1);
          // if count reaches the maximum number, add 1 and go to done state
          // this was used to avoid increasing the count width
          if (count_r == WIDTH-1) begin
            out_r   <= count_r + 1'b1;
            state_r <= S_DONE;
          end
          else begin
            // increment the count
            count_r <= count_r + 1'b1;
            state_r <= S_COND;
          end
        end

        S_RESULT : begin
          out_r   <= count_r;
          state_r <= S_DONE;
        end

        S_DONE : begin

          // Assign outputs.          
          done_r  <= 1'b1;

          // Reset internal state.
          n_r <= in;
              
          if (go == 1'b1) begin

            count_r <= '0;
          
            done_r <= 1'b0;		 
            state_r <= S_COND;
          end
        end
      endcase	  
    end      
  end   
endmodule

// 2-process FSMD here.
module asserted_bit_count_fsmd_2p
  #(parameter int WIDTH)
  (
  input logic 		                    clk,
  input logic 		                    rst,
  input logic 		                    go,
  input logic [WIDTH-1:0] 	          in,
  output logic [$clog2(WIDTH+1)-1:0]  out,
  output logic 		                    done 
  );

  typedef enum 				{S_START, S_COND, S_COMPUTE, S_RESULT, S_DONE} state_t;

  // For a 2-process FSMD, every register needs a variable for the output of
  // the register, which is the current value represented by the _r suffix,
  // and a variable for the input to the register (i.e., the value for the
  // next cycle), which is determined by combinational logic.
  state_t                   state_r, next_state;
  logic 					          done_r, next_done;   
  logic [$bits(in)-1:0] 		n_r, next_n;
  logic [$bits(out)-1:0] 		out_r, next_out;
  logic [$clog2(WIDTH)-1:0] count_r, next_count;

  assign out  = out_r;
  assign done = done_r;
      
  // The first process simply implements all the registers.
  always_ff @(posedge clk or posedge rst) begin
    if (rst == 1'b1) begin
      out_r   <= '0;
      done_r  <= 1'b0;	 
      count_r <= '0;
      n_r     <= '0;	 
      state_r <= S_START;	 
    end
    else begin
      out_r   <= next_out;
      done_r  <= next_done;	 
      count_r <= next_count;
      n_r     <= next_n;
      state_r <= next_state;
    end 
  end 

  // The second process implements any combinational logic, which includes
  // the inputs to all the registers, and any other combinational logic.
  always_comb begin
      
    logic [$bits(count_r)-1:0] count_temp;
        
    // Here we assign default values to all the register inputs to make sure
    // we don't have latches. 
    next_out    = out_r;
    next_done   = done_r;      
    next_n      = n_r;
    next_count  = count_r;
    next_state  = state_r;
      
    case (state_r)	
	    S_START : begin	   
	      next_done   = 1'b0;
	      next_out    = '0;	   
	      next_n      = in;
	      next_count  = '0;

	      // Without the default assignment at the beginning of the block,
	      // this would result in a latch in the 2-process FSMD.
	      if (go == 1'b1) begin
	        next_state = S_COND;
	      end
	    end
	
	    S_COND : begin	
        next_state = n_r == '0 ? S_RESULT : S_COMPUTE;  
      end

      S_COMPUTE : begin
        next_n      = n_r & (n_r - 1'b1);
        count_temp  = count_r + 1'b1;
        next_count  = count_temp;

        if (count_r == WIDTH-1) begin
          next_out    = count_r + 1'b1;
          next_done   = 1'b1;
          next_state  = S_DONE;
        end
        else begin          
          next_state  = S_COND;
        end
      end

      S_RESULT : begin
	      next_state  = S_DONE;
	      next_out    = count_r;
	      next_done   = 1'b1;	      
	    end

      S_DONE : begin	  
        next_count  = '0;
        next_n      = in;

	      if (go == 1'b1) begin
          // We have to clear done here to ensure the register updates
          // one cycle after go is asserted.
          next_done   = 1'b0;	      
          next_state  = S_COND;
	      end
	    end
    endcase	  
  end    
endmodule


// FSM+D - Datapath and FSM modules are in external files. 
module asserted_bit_count_fsm_plus_d
  #(parameter int WIDTH)
  (
  input   logic 		                    clk,
  input   logic 		                    rst,
  input   logic 		                    go,
  input   logic [WIDTH-1:0] 	          in,
  output  logic [$clog2(WIDTH+1)-1:0]   out,
  output  logic 		                    done 
  );

  logic 					count_done;   
  logic 					n_sel;
  logic 					n_en;
  logic 					count_sel;
  logic 					count_en;
  logic 					out_en;

  fsm CONTROLLER (.*);
  datapath #(.WIDTH(WIDTH)) DATAPATH (.*);  
endmodule

// Top-level for synthesis. Change the comments to synthesize each module.
module asserted_bit_count
  #(parameter int WIDTH=32)
  (
  input   logic 		                  clk,
  input   logic 		                  rst,
  input   logic 		                  go,
  input   logic [WIDTH-1:0] 	        in,
  output  logic [$clog2(WIDTH+1)-1:0] out,
  output  logic 		                  done 
  );

  //asserted_bit_count_fsmd_1p #(.WIDTH(WIDTH)) top (.*);
  //asserted_bit_count_fsmd_2p #(.WIDTH(WIDTH)) top (.*);
  asserted_bit_count_fsm_plus_d #(.WIDTH(WIDTH)) top (.*);   
   
endmodule
