# Reconfigurable Computing 2
Link to Dr. Stitt's SystemVerilog tutorial: https://github.com/ARC-Lab-UF/sv-tutorial

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


