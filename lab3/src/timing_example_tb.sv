// University of Florida
// EEL 6935
// Use this testbench to verify the functionality of your timing_example module
// as you make changes for timing optimization.

module timing_example_tb;

   localparam NUM_TESTS = 10000;
   int passed = 0, failed = 0, total = 0;
   
   localparam INPUT_WIDTH = 32;
   localparam OUTPUT_WIDTH = 8;
   localparam COUNTER_WIDTH = 64;
   localparam NUM_PIPELINES = 16;
   
   logic clk, rst, data_in_valid, ready, data_out_valid;
   logic [INPUT_WIDTH-1:0] data_in;
   logic [OUTPUT_WIDTH-1:0] data_out;
   logic [OUTPUT_WIDTH-1:0] pipe_in[NUM_PIPELINES];
   logic [COUNTER_WIDTH-1:0] count;

   time                      finish;   
   
   timing_example #(.INPUT_WIDTH(INPUT_WIDTH), 
                    .OUTPUT_WIDTH(OUTPUT_WIDTH),
                    .COUNTER_WIDTH(COUNTER_WIDTH),
                    .NUM_PIPELINES(NUM_PIPELINES)) DUT (.*);
      
   initial begin : generate_clock
      clk = 1'b0;
      while(1) #5 clk = ~clk;
   end

   initial begin : drive_inputs
      $timeformat(-9, 0, " ns");

      // These won't change during the execution.
      for (int i=0; i < NUM_PIPELINES; i++) pipe_in[i] <= i+2;
      
      rst <= 1'b1;
      data_in <= '0;
      data_in_valid <= 1'b0;
      for (int i=0; i < 5; i++) @(posedge clk);
      @(negedge clk);
      rst <= 1'b0;
      @(posedge clk);
      
      while(total != NUM_TESTS) begin
         // Wait for ready to be asserted before passing in an input.
         while(!ready) @(posedge clk);                 
         data_in = $urandom;
         data_in_valid = 1'b1;
         @(posedge clk);
         data_in_valid = 1'b0;
         @(posedge clk);
      end
   
      finish = $realtime;
      if (finish > 3500095.0 * 1.05) $error("ERROR: Simulation took too long");
      disable generate_clock;
      $display("Tests Completed: %0d passed, %0d failed", passed, failed);
   end
      

   int tag=0, serving=0;   
   function void inc_tag();
      tag = tag + 1'b1;
   endfunction
   
   function void inc_serving();
      serving = serving + 1'b1; 
   endfunction

   function int bit_diff_model(int data, int width);
      automatic int                  diff = 0;
      
      for (int i=0; i < width; i++) begin
         diff = data[0] ? diff+1  : diff-1;
         data = data >> 1;       
      end
      
      return diff;      
   endfunction
   
   function logic isOutputCorrect(logic [INPUT_WIDTH-1:0] in, logic [OUTPUT_WIDTH-1:0] pipe_in[NUM_PIPELINES], logic [OUTPUT_WIDTH-1:0] out);

      automatic logic signed [$clog2(INPUT_WIDTH*2+1)-1:0] bit_diff_result;
      automatic logic signed [OUTPUT_WIDTH-1:0] pipe_out;
      automatic logic signed [OUTPUT_WIDTH-1:0] mult_out[NUM_PIPELINES];
            
      bit_diff_result = bit_diff_model(in, INPUT_WIDTH);
      //$display("Time %0t: bit_diff should be %0d", $time, bit_diff_result);
      
      for (int i=0; i < NUM_PIPELINES; i++) begin
         mult_out[i] = bit_diff_result * signed'(pipe_in[i]);
      end

      pipe_out = mult_out.sum();
      if (out !== pipe_out) begin
         $error("Time %0t: out = %0d instead of %0d", $time, out, pipe_out);
         return 1'b0;
      end
      return 1'b1;                  
   endfunction
   
   property check_output;
      int wr_tag;
      logic [INPUT_WIDTH-1:0] in;

      @(posedge clk) (data_in_valid && ready, wr_tag=tag, inc_tag(), in=data_in) |-> first_match(##[1:$] (data_out_valid && serving==wr_tag, inc_serving())) ##0 isOutputCorrect(in, pipe_in, data_out);
   endproperty
            
   ap_check_output : assert property (check_output) begin
      passed ++;
      total ++;
   end
   else begin
      failed ++;
      total ++;
   end
         
endmodule
