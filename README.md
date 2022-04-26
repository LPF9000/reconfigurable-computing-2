# Reconfigurable Computing 2
Link to Dr. Stitt's SystemVerilog tutorial: https://github.com/ARC-Lab-UF/sv-tutorial

## Race Conditions
### What is a race condition? 

Race conditions are when two expressions are scheduledbto execute at the same time, and if the order of the execution is not determined, then a race condition occurs. In other words, a race condition is non-deterministic behavior created by a variable written to and/or read from by multiple threads simultaneously. 

### Common Race Conditions
#### Race #1 Blocking and non-blocking assignments

Race #1 is the most commone race. When there is multiple threads running in parallel synchronized to the same clock edge, there is a race between reading hte old value, or the updated value from a blocking assignment. 

GUIDELINE FOR TESTBENCHES: when one process reads a value that another process writes, the write should use a non-blocking assignment to avoid the race conditions. 

``` 
x = i
```
changed to:
```
x <= i
```

#### Race #2 Continuous Assignemnts

There is no deterministic order when using continuous assignemnts. Whenever the right-hand side of the operand of a continuous assignment changes, it assigns it to the left side. But if there is another process also making changes, there is no guarantee when the left-hand side wiill update. 

#### Race #3 Reset Race

Changing the reset should be done with a non-blocking assignment, reset gets updatated at the end of a time step, so when a block reads reset, it will always be the previous value. This also has the effect of not setting/clearing the reset until the next clock cycle.

One way to think of non-blocking assignments that are synchronized to a rising clock edge is that they will always get updated just after the clock, so that anything read fromt he modified variables will always get the old value. 

## Testbench Techniques
### Simple testbenches and basics
#### Generating a clock
Instead of this:
```
   initial begin : generate_clock
      clk = 1'b0;
      while(1)
        #5 clk = !clk;
   end
```
Use this:
```
   initial begin : generate_clock
      clk = 1'b0;
      while(1)
        #5 clk = !clk;
   end
```
Here we change the always block to an initial block with an infinite loop. We do this because we will later use a disable statement, which is similar to a break statement. The disable will move execution to the end of the initial block, which breaks the loop.
```
      // Disable the other initial blocks so that the simulation terminates.
      disable generate_clock;
```
#### Assertions

#### Immediate Assertions
Immediate assertions are procedural statements mainly used in simulation. 
```  
if (A == B) ...  // Simply checks if A equals B
  assert (A == B); // Asserts that A equals B; if not, an error is generated 
 ```
 You can include a message with the statement. 
 
 Pass Statement:
 ``` 
 assert (A == B) $display ("OK. A equals B");
 ```
 Fail Statement:
 ``` 
 assert (A == B) $display ("OK. A equals B");
    else $error("It's gone wrong");
 ```
 #### Concurrent Assertions
 Let's say we want the behavior of our design to behave as such:
 "The done signal should be cleared at least 2 cycles after the go signal is asserted"
 
 Properties are built using sequences. For example,
 ```
 assert property (@(posedge clk) go |-> ##[1:2] !done);
 ```
 where `go` is a simple sequence (boolean) and `##[1:2] !done` means that `done` is false on the next clock, the following clock, or both. `|->` is the implification operator, so this assertion checks that whenever go asserted, done must be cleared on the next clock, or the following clock. 
 
This assertion is only checked when a rising clock edge have occured, so go and done are sampled on the rising edge of clock. 

#### Implication
The implication construct (`|->`) allows a user to monitor sequences based on satisfying somecriteria, e.g. attach a precondition to a sequence and evaluate the sequence only if the condition is successful. The left-hand side operand of the implication is called the antecedent sequence expression, while the right-hand side is called the consequent sequence expression.

If there is no match of the antecedent sequence expression, implication succeeds vacuously by returning true. If there is a match, for each successful match of the antecedent sequence expression, the consequent sequence expression is separately evaluated, beginning at the end point of the match.

There are two forms of implication: overlapped using operator `|->`, and non-overlapped using operator `|=>`.

For overlapped implication, if there is a match for the antecedent sequence expression, then the first element of the consequent sequence expression is evaluated on the same clock tick.

For non-overlapped implication, the first element of the consequent sequence expression
is evaluated on the next clock tick.

#### Properties and Sequences
Complex properties can be built using sequences, and both properties and sequences can be declared separately. 
```
  sequence request
    Req;
  endsequence

  sequence acknowledge
    ##[1:2] Ack;
  endsequence

  property handshake;
    @(posedge Clock) request |-> acknowledge;
  endproperty

  assert property (handshake);
```

#### disable iff

`disable iff` disables the property if the expression it is checking is active. This is normally used for reset checking and if reset is active, then property is disabled. 
``` 
assert property (@(posedge clk) disable iff (rst) in |=> out);
```
This property checks (on a rising `clk`) that if in is asserted, then `out` should be asserted on the next cycle - the property is disabled if `rst` is asserted. 

#### Assertion Techniques

##### Testing a Flip Flop
```
   // checks that out is asserted one cycle after enable is asserted, and also one cycle after in is asserted
   assert property(@(posedge clk) disable iff (rst) en |=> out == $past(in,1));

   // Here we check to make sure that the output doesn't change when the enable
   // isn't asserted. We can either do this by using the $past function to check
   // the output on the previous cycle, or by using the $stable function, which
   // is semantically equivalent.
   assert property(@(posedge clk) disable iff (rst) !en |=> out == $past(out,1));
   assert property(@(posedge clk) disable iff (rst) !en |=> $stable(out));

   // The always block from the previous testbench can be simplified to this:
   always @(rst) #1 assert(out == 1'b0);  
```
##### Testing a synchronous Reset on a flip flop
```
assert property (@(posedge clk) rst |=> !out);
```
##### Testing an asynchronous reset
```
always @(rst) #1 assert(!out);
```
#### Coverage
In order to monitor sequences and other behavioral aspects, cover property statements can be used. 
##### Cover Properties
For example, let's say we hae an adder. We would like to check that there was at least one test where there was a carry in, and at least one test that generated a carry out:
```
   cp_carry_in : cover property (@(posedge clk) carry_in);
   cp_carry_out : cover property (@(posedge clk) carry_out);
   ```
Here we check to make sure that both inputs were 0 at some point:
```
   cp_in0_eq_0 : cover property (@(posedge clk) in0 == 0);
   cp_in1_eq_0 : cover property (@(posedge clk) in1 == 0);
```
Here we check to make sure both inputs are tested with their maximum amounts. To get the maximum amount, we use the replication operator:
```
   cp_in0_max : cover property (@(posedge clk) in0 == {WIDTH{1'b1}});
   cp_in1_max : cover property (@(posedge clk) in1 == {WIDTH{1'b1}});
```
### Advanced Testbench Techniques
#### Reference Queue
This example uses a localparam in the module declaration:
```
   localparam logic [WIDTH-1:0] RESET_VALUE = '0; 
```
Example code:
```
   // A queue is similar to an unpacked array, but is declared with a $ for
   // the range.
   logic [WIDTH-1:0] reference_queue[$];
   
   always_ff @(posedge clk or posedge rst)
     if (rst) begin
        reference_queue = {};
        for (int i=0; i < CYCLES; i++) reference_queue = {reference_queue, RESET_VALUE};
     end
     else if (en) begin
        // Update the queue by popping the front and pushing the new input.
        reference_queue = {reference_queue[1:$], in};
     end
     
   // The output should simply always be the front of the reference queue.
   // IMPORTANT: In previous examples, we saw race conditions being caused by
   // one process writing with blocking assignments, and another process reading
   // those values. There is no race condition here because an assert property
   // always samples the "preponed" values of the referenced signals. In other
   // words, you can think of the sampled values as the ones before the
   // simulator updates anything on a clock edge. Alternatively, you can think
   // of the values as the ones just before the posedge of the clock.
   // Interestingly, this means that any reference to the clock here will always
   // be 0, because the clock is always 0 right before a rising clock edge.
   assert property(@(posedge clk) out == reference_queue[0]);
```
The above replicates a delay module, which imitates a shift register inside of a delay. 

#### Tagging and Serving
The following example is using Tagging and Serving so we can track the writes, so when a read occurs, we can find out which write corresponds to a read. This example corresponds to the write and reads that occur within a fifo:
```
  assert property (@(posedge clk) DUT.valid_wr |-> !full);
   assert property (@(posedge clk) DUT.valid_rd |-> !empty);

   int tag=0, serving=0;   
   function void inc_tag();
      tag = tag + 1'b1;
   endfunction
   
   function void inc_serving();
      serving = serving + 1'b1; 
   endfunction
```    
The following example says, when there is a valid write, we are going to store the current tag value (local wr_tag), increments the tag, saves the write data into the local data variable, it then checks for the first_match within a sequence of indefinite amount of time, that there is a valid read that corresponds to the write tag. It then increments the serving, waits one cycle, and then it verifies the read data. 

```
   property check_output;
      int wr_tag;
      logic [WIDTH-1:0] data;
     
    
      @(posedge clk) (wr_en && !full, wr_tag=tag, inc_tag(), data=wr_data) |-> first_match(##[1:$] (rd_en && !empty && serving==wr_tag, inc_serving())) ##1 rd_data==data;
   endproperty
            
   ap_check_output : assert property (check_output);
   
```
#### Reference Queue on a FIFO
This is the same example as the previous queue, but with a FIFO. 
```
   assert property (@(posedge clk) DUT.valid_wr |-> !full);
   assert property (@(posedge clk) DUT.valid_rd |-> !empty);

   logic [WIDTH-1:0] correct_rd_data;   
   logic [WIDTH-1:0] reference[$];

   // Imitate the functionality of the FIFO with a queue
   always_ff @(posedge clk or posedge rst)
     if (rst) begin
        reference = {};
     end
     else begin
     
         // save to a variable so we can see what is happening within the queue
        correct_rd_data = reference[0];       
        
        // Pop the front element on a valid read
        if (rd_en && !empty) begin
           reference = reference[1:$];
        end

        // Push the write data on a valid write.
        if (wr_en && !full) begin
           reference = {reference, wr_data};
        end    
      end
   
   assert property(@(posedge clk) rd_en && !empty |=> rd_data == correct_rd_data); 
   ```
   
   
## Resources

1. https://github.com/intel/FPGA-Devcloud/tree/master/main/QuickStartGuides/RTL_AFU_Program_PAC_Quickstart/Arria10

2. https://github.com/ARC-Lab-UF/docs/wiki/VSCode-Remote-Development

3. https://github.com/intel/FPGA-Devcloud/tree/master/main/Devcloud_Access_Instructions#30-access-from-your-pc-via-mobaxterm-or-from-linux-terminal

4. https://github.com/ARC-Lab-UF/intel-training-modules

# MobaXterm + Intel DevCloud Instructions
This tutorial goes through the process of setting up Intel DevCloud using MobaXterm, a free Xserver and SSH client for Windows. 

## Getting a DevCloud Account

**Use this cloud website landing page to submit a request to access the FPGA Cloud:**

**https://intelsoftwaresites.secure.force.com/fpgadevcloud**

## Connecting to the DevCloud

Once you have created and activated your DevCloud account, it is time to set up the account within the cloud. Intel's recommended software is MobXterm, which will be purpose of this guide. The software can be found here: 

[Windows with Mobaxterm (SSH client)](https://mobaxterm.mobatek.net/download-home-edition.html) (recommended, see instructions below)

## Access Via MobaXterm

MobaXterm is your ultimate toolbox for remote computing. In a single Windows application, it provides loads of functions that are tailored for programmers, webmasters, IT administrators and pretty much all users who need to handle their remote jobs in a more simple fashion.

MobaXterm provides all the important remote network tools (SSH, X11, RDP, VNC, FTP, MOSH, ...) and Unix commands (bash, ls, cat, sed, grep, awk, rsync, ...) to Windows desktop, in a single portable exe file which works out of the box. 

### Install MobaXterm

1. Download the MobaXterm free edition: https://mobaxterm.mobatek.net/download-home-edition.html Note: Get the **installer edition**, not the portable edition. (The installer edition will enable you to save login profiles.) . Download zipfile, extract it and click on the msi file to install Mobaxterm.

   ![mobaxterm_edition](https://user-images.githubusercontent.com/56968566/67715527-3fee6500-f987-11e9-8961-6c0a38163bfc.png)
   
2. Open local terminal

### Automated Configuration using Intel's oneAPI OpenCL
1. Follow Instructions for Getting Started using OpenCL. The link on the GitHub mentioned above, https://devcloud.intel.com/fpga/connect/# doesn’t seem to work. Since the FPGA Devcloud is subset of oneAPI Devcloud, you can use base DevCloud for oneAPI to submit tasks on FPGA nodes. Therefore, you will need to follow the instructions here: https://devcloud.intel.com/oneapi/get_started/opencl/
2. The easiest method to set up an SSH connection to is by downloading and running an automated installer. The installer will add SSH configuration entries to ~/.ssh/config and create a private SSH key file inside ~/.ssh. Once logged into your DevCloud Account, navigate to https://devcloud.intel.com/oneapi/get_started/opencl/ and download the installer script. 
3. Run the script by adjusting the command according to your download location, or copy the script into `C:\Users\[Your Username]\AppData\Roaming\MobaXterm\home` and run it directly using the commands shown in the instructions from a terminal window in MobaXterm. 
![image](https://user-images.githubusercontent.com/56581520/155419372-775eed88-f436-47bc-96c3-56bffe4aca98.png)
4. You can set restrictive permissions for security purposes by running the following commands:
 ```bash
 chmod 600 ~/.ssh/devcloud-access-key-u12345.txt
 chmod 600 ~/.ssh/config
  ```

### Logging into DevCloud
After completing the steps outlined above, you should be able to login to the DevCloud without a password.
1. Enter the following command to login:
 ```bash
 ssh devcloud
  ```
Note that the following response is expected behavior:
> tty: standard input: Inappropriate ioctl for device
X11 forwarding request failed on channel 0

2. Type the following command to edit the `.bashrc` file:
```bash
 nano .bashrc
 ```
This command will pen a window to edit the `.bashrc` file. Add the following code to the top of the file: 
```
if [ -f /data/intel_fpga/devcloudLoginToolSetup.sh ]; then
    source /data/intel_fpga/devcloudLoginToolSetup.sh
fi
```
![image](https://user-images.githubusercontent.com/56581520/155421241-db69adf1-1ccf-419b-bea6-36deb6e0ad77.png)

3. After adding the code, press `Ctrl-O` to write the file, and press `Enter` to confirm. Press `Ctrl-X` to exit the editor. 
4. Now logout by entering the command:
```bash
 logout
 ```
5. Then log back in using the command: 
  ```bash
 ssh devcloud
  ```
6. Now you can login using the following command: 
```bash
 devcloud_login
  ```
  
7. Select l for Arria 10 PAC
8. Select 1 for release 1.2.1
9. To view the available nodes, type the following:
```bash
 devcloud_login -l
  ```
10. To report the status of your jobs running on the DevCloud using the login script provided, type the following:

```
qstatus
```
11. Jobs can be terminated with the following command when nodes are hanging with stalled jobs:
```
qdel XXXX.v-qsvr-fpga.aidevcloud
```


