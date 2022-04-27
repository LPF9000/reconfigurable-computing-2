// University of Florida
// Lab 3 EEL6935
// This file contains a top-level module timing example that you are required
// to optimize to as fast a frequency as possible. Make sure to use the
// provided timing_example_tb.sv to ensure that any changes are still
// functionally correct.
//
// Unless the comments say otherwise, you are allowed to make any change you
// want with the exception of removing modules.
//
// You are allowed to sacrifice performance to improve the clock frequency, up
// to a limit of 5% performance overhead, which is measured by the testbench.


module bit_diff
  #(
    parameter WIDTH
    )
   (
    input logic                                 clk,
    input logic                                 rst,
    input logic                                 go,
    input logic [WIDTH-1:0]                     data, 
    output logic signed [$clog2(2*WIDTH+1)-1:0] result,
    output logic                                done    
    );
   
   typedef enum                                 {START, COMPUTE, RESTART} state_t;
   state_t state_r;

   logic [$bits(data)-1:0]                      data_r;
   logic [$bits(result)-1:0]                    result_r;
   logic [$clog2(WIDTH)-1:0]                    count_r;
   logic signed [$clog2(2*WIDTH+1)-1:0]         diff_r;
   logic                                        done_r;
   
   assign result = result_r;
   assign done = done_r;

   always @(posedge clk or posedge rst) begin
      if (rst == 1'b1) begin     
         
         result_r <= '0;
         done_r <= 1'b0;                 
         diff_r <= '0;   
         count_r <= '0;
         data_r <= '0;   
         state_r <= START;       
      end
      else begin         
         case (state_r)
           START : begin   
              if (go == 1'b1) begin 
                 done_r <= 1'b0;
                 result_r <= '0;                 
                 diff_r <= '0;
                 count_r <= '0;
                 data_r <= data;
                 state_r <= COMPUTE;
              end
           end

           COMPUTE : begin
              logic [$bits(diff_r)-1:0] next_diff;
              next_diff = data_r[0] == 1'b1 ? diff_r + 1'b1 : diff_r - 1'b1;
              diff_r <= next_diff;            
              data_r <= data_r >> 1;
              count_r <= count_r + 1'b1;

              if (count_r == WIDTH-1) begin
                 result_r <= next_diff;
                 done_r <= 1'b1;
                 state_r <= RESTART;
              end
           end
        
           RESTART : begin
              if (go == 1'b1) begin              
                 count_r <= '0;
                 data_r <= data;
                 diff_r <= '0;
                 done_r <= 1'b0;                 
                 state_r <= COMPUTE;
              end
           end
         endcase          
      end      
   end   
endmodule


module fifo
  #(
    parameter WIDTH,
    parameter DEPTH,
    parameter int ALMOST_FULL_THRESHOLD=DEPTH-1
    )
   (
    input logic              clk,
    input logic              rst,
    output logic             full,
    output logic             almost_full,
    input logic              wr_en,
    input logic [WIDTH-1:0]  wr_data,
    output logic             empty, 
    input logic              rd_en,
    output logic [WIDTH-1:0] rd_data  
    );
  
   logic [WIDTH-1:0]         ram[DEPTH];
   logic [$clog2(DEPTH)-1:0] wr_addr_r, rd_addr_r, rd_addr;
   logic [$bits(rd_data)-1:0] rd_data_delay_r;

   localparam int            COUNT_WIDTH = $clog2(DEPTH)+1;   
   logic [COUNT_WIDTH-1:0]   count_r, next_count, count_update;
   logic                     valid_wr, valid_rd;
   
   assign rd_addr = !valid_rd ? rd_addr_r : rd_addr_r + 1'b1;
   
   always @(posedge clk) begin
      if (valid_wr) ram[wr_addr_r] = wr_data;
      rd_data_delay_r <= ram[rd_addr]; // Delay it by 1 cycle
      rd_data <= rd_data_delay_r;
   end
   
   always_ff @(posedge clk or posedge rst) begin
      if (rst) begin
         rd_addr_r <= '0;
         wr_addr_r <= '0;
         count_r <= '0;  
      end
      else begin
         // Handle rd/wr
         if (valid_wr) wr_addr_r <= wr_addr_r + 1'b1;
         if (valid_rd) rd_addr_r <= rd_addr_r + 1'b1;

         // Update count_r
         count_r <= next_count;

      end
   end
   
   always_comb begin
      case ({valid_rd, valid_wr})
         2'b10: count_update = '1; // -1
         2'b01: count_update = COUNT_WIDTH'(1); // TODO do we need to width-cast here?
         default: count_update = 0;
      endcase

      next_count = count_r + count_update;
   end
   
   assign valid_wr = wr_en && !full;
   assign valid_rd = rd_en && !empty;
   assign almost_full = count_r == ALMOST_FULL_THRESHOLD;   
   assign full = count_r == DEPTH;
   assign empty = count_r == 0;
    
endmodule


module timing_example
  #(
    // DO NOT CHANGE ANY OF THESE DEFAULTS
    parameter int INPUT_WIDTH=32,
    parameter int OUTPUT_WIDTH=8,
    parameter int COUNTER_WIDTH=64,
    parameter int NUM_PIPELINES=16
    )
   (
    input logic                      clk,
    input logic                      rst,
    input logic [INPUT_WIDTH-1:0]    data_in,
    input logic                      data_in_valid,
    input logic [OUTPUT_WIDTH-1:0]   pipe_in[NUM_PIPELINES],
    output logic                     ready,
    output logic [OUTPUT_WIDTH-1:0]  data_out,
    output logic                     data_out_valid, 
    output logic [COUNTER_WIDTH-1:0] count
    );

   logic [$clog2(2*INPUT_WIDTH+1)-1:0] bit_diff_out;
   logic                               bit_diff_done, bit_diff_done_r;
   logic                               first_execution_r;   
   
   localparam int                      FIFO_DEPTH = 512;
   logic [$bits(bit_diff_out)-1:0]     fifo_rd_data, fifo_rd_data_r; // _r solves crit path 1
   logic                               fifo_wr_en, fifo_rd_en;
   logic                               fifo_full, fifo_almost_full, fifo_empty;   

   // DO NOT CHANGE THE WIDTH ANY THIS SIGNAL
   logic [63:0]                      total_count_r;
      
   // Perform a bit_diff on data_in.
   bit_diff #(.WIDTH(INPUT_WIDTH)) bit_diff_ (.go(data_in_valid), 
                                              .data(data_in),
                                              .result(bit_diff_out),
                                              .done(bit_diff_done), .*);
    
   // Count the total number of bit_diff executions since reset
   always_ff @(posedge clk or posedge rst) begin
      if (rst) begin
         total_count_r <= '0;
         bit_diff_done_r <= 1'b0;
         fifo_wr_en <= 1'b0;         
         first_execution_r <= 1'b1;      
      end
      else begin
         fifo_wr_en <= 1'b0;        
         
         if (data_in_valid) first_execution_r <= 1'b0;   
         
         bit_diff_done_r <= bit_diff_done;
         
         // If the current bit_diff_done is asserted and the previous cycle
         // wasn't, we just had a new completion, so increment the count.
         if (bit_diff_done && !bit_diff_done_r) begin
            total_count_r <= total_count_r + 1'b1;

            // Write the output to the FIFO upon completion.
            fifo_wr_en <= 1'b1;     
         end
      end
   end
   
   assign count = total_count_r;   
   assign ready = first_execution_r || (bit_diff_done_r && !fifo_almost_full);
         
   fifo #(.WIDTH($bits(bit_diff_out)), .DEPTH(FIFO_DEPTH)) fifo_ 
     (.wr_en(fifo_wr_en), .full(fifo_full), .almost_full(fifo_almost_full), 
      .wr_data(bit_diff_out), .rd_en(fifo_rd_en), .rd_data(fifo_rd_data), 
      .empty(fifo_empty), .*);

   assign fifo_rd_en = !fifo_empty;
      
   ////////////////////////////////////////////////////////
   // Instantiate a multiply-add tree.
   
   logic [OUTPUT_WIDTH-1:0] pipe_in_r[NUM_PIPELINES], pipe_in_r_delay[NUM_PIPELINES], mult_out[NUM_PIPELINES], add_l0[8], add_l1[4], add_l2[2];  
   
   always_ff @(posedge clk or posedge rst) begin
      if (rst) begin
         for (int i=0; i < NUM_PIPELINES; i++) begin
            pipe_in_r[i] <= '0;
            mult_out[i] <= '0;
         end
      end
      else begin             
         fifo_rd_data_r <= fifo_rd_data;
         for (int i=0; i < NUM_PIPELINES; i++) begin
            // Register all the pipeline inputs. You can assume these inputs 
            // never change in the middle of execution.
            pipe_in_r[i] <= pipe_in[i];
            pipe_in_r_delay[i] <= pipe_in_r[i];
            mult_out[i] <= fifo_rd_data_r * pipe_in_r_delay[i];
         end         
      end
   end

   // Adder tree that sums all the multiplier outputs
   always_comb begin
      for (int i=0; i < 8; i++) add_l0[i] = mult_out[2*i] + mult_out[2*i+1];
      for (int i=0; i < 4; i++) add_l1[i] = add_l0[2*i] + add_l0[2*i+1];
      for (int i=0; i < 2; i++) add_l2[i] = add_l1[2*i] + add_l1[2*i+1];
      data_out = add_l2[0] + add_l2[1];
   end
   
   ////////////////////////////////////////////////////
   // Logic for valid_out

   // IF YOU MAKE CHANGES THAT INCREASE LATENCY OF THE MULTIPLY-ADD TREE, YOU
   // WILL NEED TO CHANGE THIS LOCALPARAM.
   localparam int                        PIPE_LATENCY = 3;
   logic [0:PIPE_LATENCY-1]              valid_delay_r;
   
   always_ff @(posedge clk or posedge rst) begin
      if (rst) begin
         for (int i=0; i < PIPE_LATENCY; i++) valid_delay_r[i] = '0;
      end
      else begin
         valid_delay_r[0] <= fifo_rd_en;       
         for (int i=1; i < PIPE_LATENCY; i++) valid_delay_r[i] <= valid_delay_r[i-1];    
      end      
   end

   assign data_out_valid = valid_delay_r[PIPE_LATENCY-1];
   
endmodule

