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

<!-- # Crit Path 2 -->
