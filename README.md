# Design and Verification of the Arm Confidential Compute Architecture

This artifact includes the mechanized Coq proofs for the security of RMM/EL3M, the verified software stack for ACCA. It also provides instructions on running the performance evaluations of CCA KVM.

# Table of Contents

## 1. Coq Proofs

## 2. Performance Evaluation

Since hardware support for ACCA is not avaiable yet, we provide a Arm Neoverse N1 System Development Platform (N1SDP) that runs modified RMM and 
Trusted Firmware-A (TF-A) as EL3M to get a preliminary measure of CCA performance. We provide remote access for you to run benchmark on the N1SDP. 

### 2.1 Prerequisites

The N1SDP is connected to a jump host with a Intel Xeon E5-2690 8 cores CPU via a **TODO** switch. You can use the jump host to access the N1SDP and
run network benchmarks from the jump host as the client.

Send an email to **TODO** with the subject **TODO** and your ssh public key in the content so we can register you to the server and send you 
instructions on connecting to it.

### 2.2 N1SDP Serial Port

The N1SDP exposes two serial ports to the jump host as described below:

- `/dev/ttyUSB0`: Motherboard Configuration Controller (MCC) console, can be used for power cycle for the N1SDP
- `/dev/ttyUSB1`: the regular serial port for applicatons

To connect to the serial port, you can use [GNU Screen](https://www.gnu.org/software/screen/):

```
screen /dev/ttyUSB0 115200
```
#### 2.2.1 GNU Screen 101

Below is a simple instruction for GNU Screen. You may refer to the manual page for more information.
If you are familiar with the GNU Screen, you can go ahead to [Boot the N1SDP](#23-boot-the-n1sdp).

You can use `Ctrl-a` `c` to create a new window in the current session and open the other serial port:

```
screen /dev/ttyUSB1 115200
```

Then you can use `Ctrl-a` `c` again to create a new window to continue working on the shell of the jump host.

To switch between different windows in a session, you can use `Ctrl-a` `SPACE` to switch directly or use `Ctrl-a` `"` to show a list of windows
and choose the one you want to switch to.

To kill a window, you may `Ctrl-d` if the window opens a shell or `Ctrl-a` `k` if the window opens a serial port.
You can also use `Ctrl-a` `\` to kill all windows and terminate the current screen session.

If you disconnected from your ssh session, you can use:

```
screen -d
screen -r
```

to resume your previous screen session.

#### 2.2.2 More GNU Screen

Similar to vim, you can also split the current window in GNU Screen by `Ctrl-a` `|` for vertical split or `Ctrl-a` `S` for horizontal split.

You can use `Ctrl-a` `TAB` to switch between different splited windows.

You can use `Ctrl-a` `X` to close the splitted window(the closed window still runs on the background).

### 2.3 Boot the N1SDP

You can boot, reboot or shutdown the N1SDP through the MCC console (`/dev/ttyUSB0`).

Here's a list of useful command:

```
+ command ------------------+ function ---------------------------------+
| SHUTDOWN                  | Shutdown PSU (leave micro running)        |
| REBOOT                    | Power cycle system and reboot             |
+---------------------------+-------------------------------------------+
```

You can use `REBOOT` to power on the system if it is not yet and then you can checkout the application serial port `/dev/ttyUSB1` to see if the system
boots.

If the system boots successfully, a GRUB menu should show up shortly after the POST. We will have a detailed explanation for each entry shortly.

### 2.4 Run the Benchmarks

Due to license contraints, we are not able to provide source code of ACCA software stacks for you to compile and install on the N1SDP.
They are preinstalled on the N1SDP, including modified RMM, TF-A, CCA KVM and CCA QEMU, for running the benchmarks.

RMM and TF-A are automatically loaded from the board when the machine powered up and the kernel will be loaded by GRUB.

#### 2.4.1 Choose the Kernel

In the GRUB menu, you should see five (5) entries as explained below:

```
Ubuntu                            # DO NOT USE, Ubuntu stock kernel, incompatible with ACCA
Advanced options for Ubuntu       # DO NOT USE, Ubuntu stock kernel, incompatible with ACCA
Ubuntu N1SDP realm                # Linux v5.12 kernel modified for ACCA, used for VM benchmarks
Ubuntu N1SDP - SMP benchmark      # Linux v5.12 kernel, passed with cmdline maxcpus=1,mem=512m for baseline SMP native benchmarks
Ubuntu N1SDP - UP benchmark       # Linux v5.12 kernel, passed with cmdline maxcpus=1,mem=512m used for baseline UP native benchmarks
```

### 2.4.2 Run the VM

Make sure you choose the entry `Ubuntu N1SDP realm` in the GRUB menu. After the login interface prompts, you can ssh to the N1SDP from the jump host:

```
ssh root@192.168.11.10
```

After you loged in, you should run:

```
./net.sh
```

to configure the bridged network for the VM.

**TODO: better cmd**
Then you can use the following command to run the VM:

```
QEMU=./qemu/aarch64-softmmu/qemu-system-aarch64 \
    ./run-qemu-realm.sh -c 1 \
    -m 512m -k Image.nopref \
    -i ubuntu-apache.img \
    -a "swiotlb=force" \
    --machextra realm=false
```

You can replace `apache` in `ubuntu-apache.img` with `hack`, `kern`, `mongo` or `redis` for `hackbench`. `kernbench`, `MongoDB` or `Redis`, 
respectively.

After you run the command, QEMU will for the vCPUs being pinned to proceed. To pin the vCPUs, open a different shell and run:

```
./pin_vcpu.sh
```

