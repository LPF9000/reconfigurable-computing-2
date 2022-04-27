# Report

# Crit Path 1
I ran the timing analyzer > Report path... > report 1 path for Slow 1200mV 85C Model

**Fmax = 104MHz**

First several critical paths were from the fifo_rd_data port to the multiplier inputs.

I right-clicked on "From Node" > Locate Path > Locate in Technology Map Viewer

Here's one of the paths:

![](./images/crit_1.png)

## Fix
Added fifo_rd_data_r

**New Fmax = 173.79 MHz**

# Crit Path 2

**Fmax = 173.79 MHz**

New critical path is in the FIFO count signal:



![](./images/crit_2.png)

Old FIFO:
![](./images/2_old_fifo.png)

New FIFO:
![](./images/2_new_fifo.png)

I'm honestly not sure _why_ this worked. It probably is more apparent in the Technology Map viewer.