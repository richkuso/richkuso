

# 9.5.3.35 Error Log 1 (Offset 1090h)

This register is replicated per module. Offsets 1090h to 109Ch are used $\mathrm { i n }$ 4B offset increments for
multi-module scenarios.

<table>
<caption>Table 9-60. Error Log 1 Register</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>$7 : 0$</td>
<td>ROS</td>
<td>$S t a t e \left( N - 3 \right) :$ Captures the state status before State (N-2) was entered. encodings are the same as State N field. Default is 0</td>
</tr>
<tr>
<td>8</td>
<td>RW1CS</td>
<td>State Timeout Occurred: Hardware sets this to 1b if a Link Training State machine state or sub-state timed out and it was escalated as a fatal error. Default value is 0b.</td>
</tr>
<tr>
<td>9</td>
<td>RW1CS</td>
<td>Sideband Timeout Occurred: Hardware sets this to 1b if a sideband handshake timed out, for example, if a RDI request did not get a response for 8ms. Sideband handshakes related to Link Training messages are not included here. Default value is 0b.</td>
</tr>
<tr>
<td>10</td>
<td>RW1CS</td>
<td>Remote LinkError received: Hardware sets this to 1b if remote Link partner requested LinkError transition through RDI sideband. Default value is 0b.</td>
</tr>
<tr>
<td>11</td>
<td>RW1CS</td>
<td>Internal Error: Hardware sets this to 1b if any implementation specific internal error occurred in the Physical Layer. Default value is 0b.</td>
</tr>
<tr>
<td>$3 1 : 1 2$</td>
<td>RsvdZ</td>
<td>Reserved</td>
</tr>
</table>

# 9.5.3.36 Runtime Link Test Control (Offset 1100h)

<table>
<caption>Table 9-61. Runtime Link Test Control (Sheet 1 of 2)</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>0</td>
<td>RW/RO</td>
<td>Implementations are encouraged to implement this as an RO bit with a of 0. However, for backward compatibility, implementations are $\mathrm { p e r m i t t e d } t$ to implement this as an RW bit with a default value of 0.</td>
</tr>
<tr>
<td>1</td>
<td>RW/RO</td>
<td>Implementations are encouraged to implement this as an RO bit with a default value of 0. However, for backward compatibility, implementations are permitted to implement this as an RW bit with a default value of 0.</td>
</tr>
<tr>
<td>2</td>
<td>RW</td>
<td>Apply Module 0 Lane Repair: For Advanced Package, software programs this bit to inform Physical Layer hardware to apply Lane repair for this logical if this Module is operational. For Standard $\begin{array}{} { \text { module id at the next Retrain cycle, } } \\ { \text { Package, this bit will trigger a width } } \end{array}$ degrade for logical Module 0, if possible Default value is 0.</td>
</tr>
<tr>
<td>3</td>
<td>RW</td>
<td>Apply Module 1 Lane Repair: For Advanced Package, software programs this bit to inform Physical Layer hardware to apply Lane repair for this logical module id at the next Retrain cycle, if this Module is operational. For Standard Package, this bit will trigger a width degrade for logical Module 1, if possible and relevant. $\begin{array}{} { \text { Default value is } 0 . } \\ { \text { These bits are reserved if Module 1 is not present } } \end{array} .$</td>
</tr>
<tr>
<td>4</td>
<td>RW</td>
<td>Apply Module 2 Lane Repair: For Advanced Package, software programs this bit to inform Physical Layer hardware to apply Lane repair for this logical module id at the next Retrain cycle, if this Module is operational. For Standard Package, this bit will trigger a width degrade for logical Module 2, if possible and relevant. Default value is 0. These bits are reserved if Module 2 is not present.</td>
</tr>
</table>

<table>
<caption>Table 9-61. Runtime Link Test Control (Sheet 2 of 2)</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>5</td>
<td>RW</td>
<td>Apply Module 3 Lane Repair: For Advanced Package, software programs this bit to inform Physical Layer hardware to apply Lane repair for this logical module id at the next Retrain cycle, if this Module is operational. For Standard Package, this bit will trigger a width degrade for logical Module 3, if possible and relevant. Default value is 0. These bits are reserved if Module 3 is not present.</td>
</tr>
<tr>
<td>6</td>
<td>RW</td>
<td>Start: Software writes to this bit before setting Link Retrain bit to inform hardware that the contents of this register are valid. HW clears this bit to 0 after the Busy bit in the Runtime Link Test Status register is set to 1.</td>
</tr>
<tr>
<td>7</td>
<td>RW</td>
<td>$I n j e c t \quad S t u c k - a t \quad f a u l t : S o f t w a r e \quad w r i t e s \quad 1 b \quad t o \quad t h i s \quad b i t \quad t o \quad i n d i c a t e \quad h a r d w a r e$ specific Module's lane(s) in which the fault is injected is indicated by the `Apply Module x Lane Repair' bits) for the corresponding field. Injecting the fault at Tx or Rx is implementation specific. This bit takes effect during the next link retraining (see Section 4.5.3.7 for further details). Default value is 0b.</td>
</tr>
<tr>
<td>$1 4 : 8$</td>
<td>RW</td>
<td>Module 0 Lane repair id: For Advanced Package, software programs this bit to inform Physical Layer hardware to apply Lane repair for this logical transmit Lane id in logical Module 0 at the next Retrain cycle, if this Module is operational. For Standard Package, this bit will trigger a width degrade for logical Module 0, if possible and relevant. Default is 0. These bits are reserved if Module 0 is not present.</td>
</tr>
<tr>
<td>21:15</td>
<td>RW</td>
<td>Module 1 Lane repair id: For Advanced Package, software programs this bit to inform Physical Layer hardware to apply Lane repair for this logical transmit Lane id in logical Module 1 at the next Retrain cycle, if this Module is operational. For Standard Package, this bit will trigger a width degrade for logical Module 1, if possible and relevant. Default is 0. These bits are reserved if Module 1 is not present.</td>
</tr>
<tr>
<td>$2 8 : 2 2$</td>
<td>RW</td>
<td>Module 2 Lane repair id: For Advanced Package, software programs this bit to inform Physical Layer hardware to apply Lane repair for this logical transmit Lane id in logical Module 2 at the next Retrain cycle, if this Module is operational. For Standard Package, this bit will trigger a width degrade for logical Module 2, if possible and relevant. Default is 0. These bits are reserved if Module 2 is not present.</td>
</tr>
<tr>
<td>$3 5 : 2 9$</td>
<td>RW</td>
<td>Module 3 Lane repair id: For Advanced Package, software programs this bit to inform Physical Layer hardware to apply Lane repair for this logical transmit Lane id in logical Module 3 at the next Retrain cycle, if this Module is operational. For Standard Package, this bit will trigger a width degrade for logical Module 3, if possible and relevant. Default is 0. These bits are reserved if Module 3 is not present.</td>
</tr>
<tr>
<td>63:36</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

## 9.5.3.37 Runtime Link Test Status (Offset 1108h)

<table>
<caption>Table 9-62. Runtime Link Test Status Register</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>0</td>
<td>RO</td>
<td>Busy: Hardware loads 1b to this bit once Start bit is written by software. Hardware loads Ob to this bit once it has attempted to complete the actions requested in Runtime Link Test Control register. Default is 0</td>
</tr>
<tr>
<td>31:1</td>
<td>RsvdZ</td>
<td>Reserved</td>
</tr>
</table>

## 9.5.3.38 Mainband Data Repair (Offset 110Ch)

This register is replicated per advanced module. For Standard package, this register is not applicable.
Offsets 110Ch to 1124h are used in 8B offset increments for multi-module scenarios.

<table>
<caption>Table 9-63. Mainband Data Repair Register (Sheet 1 of 2)</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td rowspan="2">7:0</td>
<td rowspan="2">RO</td>
<td>Repair Address for TRD_P[0]: Indicates the physical Lane repaired when TRD_P[0] is used in remapping scheme</td>
</tr>
<tr>
<td>00h: TD_P[0] Repaired 1Eh: TD_P[30] Repaired 01h: TD_P[1] Repaired 1Fh: TD_P[31] Repaired 02h: TD_P[2] Repaired F0h: Repair attempt failed FFh: No Repair ...</td>
</tr>
<tr>
<td rowspan="2">15:8</td>
<td rowspan="2">RO</td>
<td>Repair Address for TRD_P[1]: Indicates the physical Lane repaired when TRD_P[1] is used in remapping scheme</td>
</tr>
<tr>
<td>00h: Invalid 1Eh: TD_P[30] Repaired 01h: TD_P[1] Repaired 1Fh: TD_P[31] Repaired 02h: TD_P[2] Repaired F0h: Repair attempt failed FFh: No Repair ...</td>
</tr>
<tr>
<td rowspan="3">$2 3 : 1 6$</td>
<td rowspan="3">$R O$</td>
<td>Repair Address for TRD_P[2]: Indicates the physical Lane repaired when TRD_P[2] is used in remapping scheme</td>
</tr>
<tr>
<td>20h: TD_P[32] Repaired $\begin{array}{} { \text { 3Eh: TD-P\left[62\right] Repairec } } \\ { 3 \text { Fh: } T D \text { PI } 6 3 1 \text { Repairec } } \end{array}$ 21h: TD_P[33] Repaired 22h: TD_P[34] Repaired F0h: Repair attempt failed FFh: No Repair ...</td>
</tr>
<tr>
<td>This field is reserved for UCIe-A x32 module implementations.</td>
</tr>
<tr>
<td rowspan="3">$3 1 : 2 4$</td>
<td rowspan="3">$R O$</td>
<td>Repair Address for TRD_P[3]: Indicates the physical Lane repaired when TRD_P[3] is used in remapping scheme</td>
</tr>
<tr>
<td>20h: Invalid 3Eh: TD_P[62] Repaired $\begin{array}{} { 2 1 h : \text { TD } - P \left[ 3 3 \right] \text { Repairec } } \\ { 2 2 h : \text { TD } P \left[ 3 4 \right] \text { Repairec } } \end{array}$ $3 F h : T D _ { - } P \left[ 6 3 \right]$ FFh: No Repair ...</td>
</tr>
<tr>
<td>This field is reserved for UCIe-A x32 module implementations.</td>
</tr>
<tr>
<td rowspan="2">$3 9 : 3 2$</td>
<td rowspan="2">$R O$</td>
<td>Repair Address for RRD_P[0]: Indicates the physical Lane repaired when RRD_P[0] is used in remapping scheme</td>
</tr>
<tr>
<td>00h: RD_P[0] Repaired 1Eh: RD_P[30] Repaired 01h: RD_P[1] Repaired 02h: RD_P[2] Repaired $\begin{array}{} { \text { 1Fh: RD_PIJ Repaired } } \\ { \text { FOh: Repair attempt failed } } \end{array}$ FFh: No Repair ...</td>
</tr>
</table>

<table>
<caption>Table 9-63. Mainband Data Repair Register (Sheet 2 of 2)</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th colspan="2">Description</th>
</tr>
<tr>
<td rowspan="2">$4 7 : 4 0$</td>
<td rowspan="2">$R O$</td>
<td colspan="2">Repair Address for RRD_P[1]: Indicates the physical Lane repaired when RRD_P[1] is used in remapping scheme</td>
</tr>
<tr>
<td>00h: RD_P[0] Repaired 01h: RD_P[1] Repaired 02h: RD_P[2] Repaired ...</td>
<td>1Eh: RD_P[30] Repaired 1Fh: RD_P[31] Repaired F0h: Repair attempt failed FFh: No Repair</td>
</tr>
<tr>
<td rowspan="3">$5 5 : 4 8$</td>
<td rowspan="3">$R O$</td>
<td colspan="2">Repair Address for RRD_P[2]: Indicates the physical Lane repaired when RRD_P[2] is used in remapping scheme</td>
</tr>
<tr>
<td>20h: RD_P[32] Repaired 21h: RD_P[33] Repaired 22h: RD_P[34] Repaired ...</td>
<td>$R D _ { - }$ 3Fh: RD_P[63] Repaired F0h: Repair attempt failed FFh: No Repair</td>
</tr>
<tr>
<td colspan="2">This field is reserved for UCIe-A x32 implementations.</td>
</tr>
<tr>
<td rowspan="3">$6 3 : 5 6$</td>
<td rowspan="3">$R O$</td>
<td colspan="2">Repair Address for RRD_P[3]: Indicates the physical Lane repaired when RRD_P[3] is used in remapping scheme</td>
</tr>
<tr>
<td colspan="2">20h: RD_P[32] Repaired 3Eh: RD_P[62] Repaired 21h: RD_P[33] Repaired 3Fh: RD_P[63] Repaired 22h: RD_P[34] Repaired F0h: Repair attempt failed FFh: No Repair ...</td>
</tr>
<tr>
<td colspan="2">This field is reserved for UCIe-A x32 module implementations.</td>
</tr>
</table>

## 9.5.3.39 Clock, Track, Valid and Sideband Repair (Offset 1134h)

This register is replicated per module. Offsets 1134h to 1140h are used in 4B offset increments for
multi-module scenarios.

<table>
<caption>Table 9-64. Clock, Track, Valid and Sideband Repair Register (Sheet 1 of 2)</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td rowspan="2">$3 : 0$</td>
<td rowspan="2">$R O$</td>
<td>Repair Address for TRDCK_P: Indicates the physical Lane repaired when TRDCK_P is used in remapping scheme</td>
</tr>
<tr>
<td>0h: TCKP _ P Repaired 7h: Repair attempt failed 1h: TCKN_P Repaired Fh: No Repair 2h: TTRK_P Repaired All other encodings are reserved.</td>
</tr>
<tr>
<td rowspan="2">$7 : 4$</td>
<td rowspan="2">RO</td>
<td>Repair Address for RRDCK_P: Indicates the physical Lane repaired when RRDCK_P is used in remapping scheme</td>
</tr>
<tr>
<td>0h: RCKP _ P Repaired 7h: Repair attempt failed $1 h : R C K N _ { - } P$ Fh: No Repair All other encodings are reserved. _</td>
</tr>
<tr>
<td rowspan="3">9:8</td>
<td rowspan="3">$R O$</td>
<td>Repair Address for TRDVLD_P: Indicates the physical Lane repaired when TRDVLD_P is used in remapping scheme</td>
</tr>
<tr>
<td>00b: TVLD_P Repaired 10b: Reserved</td>
</tr>
<tr>
<td>01b: Repair attempt failed 11b: No Repair</td>
</tr>
<tr>
<td rowspan="3">$1 1 : 1 0$</td>
<td rowspan="3">$R O$</td>
<td>Repair Address for RRDVLD_P: Indicates the physical Lane repaired when RRDVLD_P is used in remapping scheme</td>
</tr>
<tr>
<td>00b: RVLD_P Repaired 10b: Reserved</td>
</tr>
<tr>
<td>01b: Repair attempt failed 11b: No Repair</td>
</tr>
</table>

<table>
<caption>Table 9-64. Clock, Track, Valid and Sideband Repair Register (Sheet 2 of 2)</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>$1 5 : 1 2$</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
<tr>
<td>$1 9 : 1 6$</td>
<td>RO</td>
<td>Repair Address for Sideband Transmitter: Indicates sideband repair result for the Transmitter Result[3:0]</td>
</tr>
<tr>
<td>$2 3 : 2 0$</td>
<td>RO</td>
<td>Repair Address for Sideband Receiver: Indicates sideband repair result for the Transmitter Result[3:0]</td>
</tr>
<tr>
<td>$3 1 : 2 4$</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

## 9.5.3.40 UCIe Link Health Monitor (UHM) DVSEC

This DVSEC is an extended Capability. It is required for all devices that support Compliance testing
(as indicated by the presence of Compliance/Test Register Locator) and optional otherwise. This
DVSEC contains the required registers for SW to read eye margin values per lane. SW Flow for Eye
Margining is as follows:

· SW ensures that the Eye Margin Valid (EMV) bit in UHM_STS register is cleared

· SW triggers a retrain of the link

\- When the retrain completes (as indicated by bit 16 in the UCIe Link Status register) and the
EMV bit is set in the UHM_STS register, SW can read the EM *_ Ln \*_ Mod\* registers in UHM
DVSEC to know the margins. Receive margins are logged in the Tx UHM registers.

Note that HW may also measure Eye Margins during HW-autonomous retraining and/or initial training
and if measured, is permitted to report it in the Eye Margin registers whenever the EMV bit is cleared.

For x32 Advanced Packaging implementations, EML* and EMR* registers for Lanes 63:32 are RsvdP.

<table>
<caption>Figure 9-5. UCIe Link Health Monitor (UHM) DVSEC</caption>
<tr>
<th colspan="4">PCI Express Extended Capability Header</th>
</tr>
<tr>
<th colspan="4">Designated Vendor Specific Header 1</th>
</tr>
<tr>
<th colspan="2">Reserved</th>
<th colspan="2">Designated Vendor Specific Header 2</th>
</tr>
<tr>
<td colspan="2">UHM_STS</td>
<td colspan="2">Reserved</td>
</tr>
<tr>
<td colspan="4">Reserved</td>
</tr>
<tr>
<td colspan="4">Reserved</td>
</tr>
<tr>
<td>EMR_Ln1_Mod0</td>
<td>EML_Ln1_Mod0</td>
<td>EMR_Ln0_Mod0</td>
<td>EML_Ln0_Mod0</td>
</tr>
<tr>
<td>EMR_Ln3_Mod0</td>
<td>EML_Ln3_Mod0</td>
<td>EMR_Ln2_Mod0</td>
<td>EML_Ln2_Mod0</td>
</tr>
<tr>
<td colspan="2"></td>
<td colspan="2">...</td>
</tr>
<tr>
<td colspan="2"></td>
<td colspan="2">...</td>
</tr>
<tr>
<td>EMR_Ln1_Mod1</td>
<td>EML_Ln1_Mod1</td>
<td>EMR_Ln0_Mod1</td>
<td>EML_Ln0_Mod1</td>
</tr>
<tr>
<td>EMR_Ln3_Mod1</td>
<td>EML_Ln3_Mod1</td>
<td>EMR_Ln2_Mod1</td>
<td>EML_Ln2_Mod1</td>
</tr>
<tr>
<td colspan="4">...</td>
</tr>
<tr>
<td colspan="4">...</td>
</tr>
</table>

<table>
<caption>Table 9-65. UHM DVSEC - Designated Vendor Specific Header 1, 2 (Offsets 04h and 08h)</caption>
<tr>
<th>Register</th>
<th>Field</th>
<th>Bit Location</th>
<th>Value</th>
</tr>
<tr>
<td rowspan="3">Designated Vendor-Specific Header 1 (offset 04h)</td>
<td>DVSEC Vendor ID</td>
<td>15:0</td>
<td>D2DEh</td>
</tr>
<tr>
<td>DVSEC Revision</td>
<td>19:16</td>
<td>0h</td>
</tr>
<tr>
<td>Length</td>
<td>31:20</td>
<td>Design dependent</td>
</tr>
<tr>
<td>Designated Vendor-Specific Header 2 (offset 08h)</td>
<td>DVSEC ID</td>
<td>15:0</td>
<td>1h</td>
</tr>
</table>

# 9.5.3.40.1 UHM Status (Offset Eh)

<table>
<caption>Table 9-66. UHM Status</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>7:0</td>
<td>RO</td>
<td>Step Count Step count used in the reporting of margin information. A value of 0 indicates 256. For example, a value of 32 indicates that the UI is equally divided into 32 steps and Eye Margin registers provide the left and right margins in multiples of UI/32.</td>
</tr>
<tr>
<td>8</td>
<td>RW1C</td>
<td>Eye Margin Valid (EMV) This bit, when set, indicates that margin registers carry valid information from the last retrain. SW must clear this bit before initiating link retrain, if it intends to measure eye margins during the retrain. On a SW- initiated link retrain, if after retrain, this bit is cleared, then SW should infer that there was some error in margin measurement. Note that HW logs any new Eye Margin measurements (whether it is measured during SW-initiated retrain, during HW-autonomous retraining, or during initial training) in the Eye Margin registers only when this bit is cleared.</td>
</tr>
<tr>
<td>15:9</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

# 9.5.3.40.2 Eye Margin (Starting Offset 18h)

<table>
<caption>Table 9-67. EML_Lnx_Mody</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>7:0</td>
<td>RO</td>
<td>Eye Margin Left for Lane x and Module y Provides the left eye margin relative to the PI center, in units of $\mathrm { U I / S t e p }$ Count.</td>
</tr>
</table>

<table>
<caption>Table 9-68. EMR_Lnx_Mody</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>7:0</td>
<td>RO</td>
<td>Eye Margin Right for Lane x and Module y Provides the right eye margin relative to the PI center, in units of UI/ Step Count.</td>
</tr>
</table>

## 9.5.4 Test/Compliance Register Block

The Test/Compliance register block is 8 KB in size with first 4 KB from base address (as enumerated
via register locator with Register Block Identifier of 1h) used for D2D Adapter-related Test/Compliance
registers and the second 4 KB used for PHY-related Test/Compliance registers. For future extensibility,
these offsets are enumerable via the associated Register Block Offset registers, as shown in
Figure 9-6.

<figure>
<figcaption>Figure 9-6. UCIe Test/Compliance Register Block</figcaption>

PHY Test/Compliance
Register Block Mod 3

8K

PHY Test/Compliance
Register Block Mod 2

PHY Test/Compliance
Register Block Mod 1

PHY Test/Compliance
Register Block Mod 0

4K

D2D Adapter Test/
Compliance Register Block

Base address as indicated in
"Test/Compliance" Register
Locator

Rsvd
PHY Test/Compliance Register Block
Offset
D2D Adapter Test/Compliance Register
Block Offset

32

UCle Register Block Header

</figure>

### 9.5.4.1 UCIe Register Block Header

<table>
<caption>Table 9-69. UCIe Register Block Header (Offset 0h)</caption>
<tr>
<th>Bit</th>
<th>Attributes</th>
<th>Description</th>
</tr>
<tr>
<td>15:0</td>
<td>RO</td>
<td>Vendor ID Default is set to Vendor ID assigned for UCIe Consortium - D2DEh.</td>
</tr>
<tr>
<td>$3 1 \cdot 1 6$</td>
<td>RO</td>
<td>Vendor ID Register Block Set to 1h to indicate Test Compliance register block.</td>
</tr>
<tr>
<td>35:32</td>
<td>RO</td>
<td>Vendor Register Block Version Set to 0h.</td>
</tr>
<tr>
<td>$6 3 : 3 6$</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
<tr>
<td>$9 5 : 6 4$</td>
<td>$R O$</td>
<td>Vendor Register Block Length The number of bytes in the register block including the UCIe register block header. Default is 2000h.</td>
</tr>
<tr>
<td>127:96</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

### 9.5.4.2 D2D Adapter Test/Compliance Register Block Offset

<table>
<caption>Table 9-70. D2D Adapter Test/Compliance Register Block Offset (Offset 10h)</caption>
<tr>
<th>Bit</th>
<th>Attributes</th>
<th>Description</th>
</tr>
<tr>
<td>7:0</td>
<td>RO</td>
<td>D2D Adapter Test/Compliance Register Block Offset (D2DOFF) 4-KB granular offset from Test/Compliance Register Block base address for D2D Adapter Test/Compliance registers. This field should be set to 0. However, SW must read this field to know the actual offset, for future compatibility reasons.</td>
</tr>
<tr>
<td>15:8</td>
<td>RO</td>
<td>D2D Adapter Test/Compliance Register Block Length 4-KB granular length of the D2D Adapter Test/Compliance registers. This field should be set to 1 to indicate 4-KB length. However, SW must read this field to know the actual length, for future compatibility reasons.</td>
</tr>
<tr>
<td>31:16</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

### 9.5.4.3 PHY Test/Compliance Register Block Offset

<table>
<caption>Table 9-71. PHY Test/Compliance Register Block Offset (Offset 14h)</caption>
<tr>
<th>Bit</th>
<th>Attributes</th>
<th>Description</th>
</tr>
<tr>
<td>7:0</td>
<td>RO</td>
<td>PHY Test/Compliance Register Block Offset (PHYOFF) 4-KB granular offset from Test/Compliance Register Block base address for PHY Adapter Test/Compliance registers. This field should be set to 1, indicating that the registers start at 4 KB from the base address. However, SW must read this field to know the actual offset, for future compatibility reasons.</td>
</tr>
<tr>
<td>15:8</td>
<td>RO</td>
<td>PHY Test/Compliance Register Block Length 4-KB granular length of the PHY Test/Compliance registers. This field should be set to 1 to indicate 4-KB length. However, SW must read this field to know the actual length, for future compatibility reasons.</td>
</tr>
<tr>
<td>$3 1 : 1 6$</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

### 9.5.4.4 D2D Adapter Test/Compliance Register Block

#### 9.5.4.4.1 Adapter Compliance Control

<table>
<caption>Table 9-72. Adapter Compliance Control (Offset 20h from D2DOFF)</caption>
<tr>
<th>Bit</th>
<th>Attributes</th>
<th>Description</th>
</tr>
<tr>
<td rowspan="2">1:0</td>
<td rowspan="2">RW</td>
<td>Compliance Mode Any write to this register takes effect after the next entry of RDI state status to Retrain. · 00b = Normal mode of operation . 01b = PHY only Link Training or Retraining - Adapter performs the necessary RDI handshakes to bring RDI to Active but does not perform Parameter exchanges or Adapter vLSM handshakes and keeps FDI in Reset to prevent mainband traffic. - Adapter must still trigger RDI to Retrain if software programmed the Retrain bit in Link Control. - Sideband Register Access requests and completions are operational in this mode.</td>
</tr>
<tr>
<td>· 10b = Adapter Compliance - Adapter performs the necessary RDI handshakes to bring RDI to Active but does not perform Parameter exchanges or Adapter vLSM handshakes (unless triggered by software) and keeps FDI in Reset. - Adapter only performs actions based on the triggers and setup according to the registers defined in Section 9.5.4.4.2 to Section 9.5.4.4.6. - Adapter must still trigger RDI to Retrain if software programmed the Retrain bit in Link Control. - Sideband Register Access requests and completions are operational in this mode. · 11b = Reserved $\begin{array}{} { \text { Any RDI transition to LINKE } } \\ { \text { Anse not reset any registers } } \end{array}$ when this field is either 01b or 10b Default is 00b.</td>
</tr>
<tr>
<td>2</td>
<td>RW</td>
<td>Force Link Reset If set to 1b, Adapter transitions RDI to LinkError state. This bit is used by Compliance software to re-initialize the DUT anytime during Compliance testing. If SW expectation is that the DUT reinitializes to normal mode at the end of link reset, the Compliance Mode field in this register must be 00b and the Compliance Enable for PHY bit in the PHY Compliance Control Register must be 0b.</td>
</tr>
<tr>
<td>31:3</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

### 9.5.4.4.2 Flit $T x$ Injection Control

<table>
<caption>Table 9-73. Flit Tx Injection Control (Offset 28h from D2DOFF) (Sheet 1 of 2)</caption>
<tr>
<th>Bit</th>
<th>Attributes</th>
<th>Description</th>
</tr>
<tr>
<td>0</td>
<td>RW</td>
<td>Flit Tx Injection Enable Setting this bit to 1b starts Flit injection from the Adapter to the PHY at the Transmitter. Clearing this bit to Ob stops Flit injection on the Link. Default is 0b.</td>
</tr>
<tr>
<td>$3 : 1$</td>
<td>RW</td>
<td>Flit Type Type of Flit injected. . 000b = Adapter NOP Flits. These bypass TX retry buffer. · 001b = Test Flits. · 010b = Alternate between NOP Flits and Test Flits. . All other encodings are reserved. Default is 000b.</td>
</tr>
</table>

<table>
<caption>Table 9-73. Flit Tx Injection Control (Offset 28h from D2DOFF) (Sheet 2 of 2)</caption>
<tr>
<th>Bit</th>
<th>Attributes</th>
<th>Description</th>
</tr>
<tr>
<td rowspan="2">5:4</td>
<td rowspan="2">RW</td>
<td>Injection mode . 00b = Continuous injection of Flits as specified by Flit Type field. · 01b = Inject 'Flit Inject Number' of Flits contiguously without any intervening Protocol Flits.</td>
</tr>
<tr>
<td>· 10b = Inject 'Flit Inject Number' of Flits while interleaving with Protocol Flits. are available, alternate between Protocol Flits and Injected $F l i t s . I f \quad n o \quad P r o t o c o l$ Flits are available then, inject consecutively. · $1 1 b = R e s e r v e d .$ Default</td>
</tr>
<tr>
<td>$1 3 : 6$</td>
<td>RW</td>
<td>Flit Inject Number If the Injection mode is not 00b, this field indicates the number of Flits injected. Default is 00h.</td>
</tr>
<tr>
<td>$1 7 : 1 4$</td>
<td>RW</td>
<td>Payload Type This field determines the payload type used if Test Flits are injected. Payload includes all bits in the Flit with the exception of Flit Header, CRC, and Reserved bits. . $\begin{array}{} { \text { Oh } = \text { Fixed } 4 B \text { pattern picked up from Payload Fixed Pattern } ^ { \prime } \text { field of this } } \\ { \text { register, inserted so as to cover all the Payload bytes \left(with the same patter\right) } } \end{array}$ replicated in incrementing 4B chunks) · 1h = Random 4B pattern picked up from a 32b LFSR (linear feedback shift register used for pseudo random pattern generation), inserted so as to cover all the Payload bytes (with the same pattern replicated in incrementing 4B · $\begin{array}{} { \text { CnunKS\right) } } \\ { 2 h = \text { Fixed } 4 \text { byte pattern picked up from from Payload Fixed Pattern field of the } } \\ { \text { reaister inser tnsed once at the Flit Byte offset^{\prime } \text { location within thin tht } } \end{array}$ · 3h = Random 4B pattern picked up from a 32b LFSR, inserted once at the 'Flit Byte Offset' location within the Flit and the rest of the payload is assigned 0b · $4 h = S a m e \quad a s \quad 2 h ,$ except the 4B pattern is injected every 'Pattern Repetition' with 'Flit Byte Offset' . 5h = Same as 3h, except the 4B pattern is injected every 'Pattern Repetition' bytes starting with 'Flit Byte Offset' and the rest of the payload is assigned 0b · All other encodings are reserved Default is 0h. LFSR seed and primitive polynomial choice is implementation specific. Note: While in mission mode, because scrambling is always enabled, changing the Payload Type may have no benefit. This may, however, be useful during compliance testing with scrambling disabled.</td>
</tr>
<tr>
<td>$2 5 : 1 8$</td>
<td>$R W$</td>
<td>Flit Byte Offset See 'Payload Type'. Default is 00h.</td>
</tr>
<tr>
<td>$3 1 : 2 6$</td>
<td>RW</td>
<td>Pattern Repetition See 'Payload Type'. A value of 00h or 01h must be interpreted as a single pattern occurrence. Default is 00h.</td>
</tr>
<tr>
<td>63:32</td>
<td>RW</td>
<td>Payload Fixed Pattern See 'Payload Type'. Default is 0000 0000h.</td>
</tr>
</table>

### 9.5.4.4.3 Adapter Test Status (Offset 30h from D2DOFF)

<table>
<caption>Table 9-74. Adapter Test Status</caption>
<tr>
<th>Bit</th>
<th>Attributes</th>
<th>Description</th>
</tr>
<tr>
<td>0</td>
<td>$R O$</td>
<td>Compliance Status If Adapter is in 'PHY only Link Training or Retraining' or 'Adapter Compliance' mode, it is set to 1b; otherwise, it is 0b.</td>
</tr>
<tr>
<td>$2 : 1$</td>
<td>$R O$</td>
<td>Flit Tx Injection Status · 00b = No Flits injected. · 01b = At least one Flit was injected, but not completed. For Continuous from 1b to 0b. Injection mode, this will be the status until Flit Injection Enable transitions · 10b = Completed Flit Injection, for cases in which a finite number of Flit injections was set up. . 11b = Flit Injection Enable transitioned from 1b to Ob before Flit injections were complete. This field is cleared to 00b on a 0b-to-1b transition of Flit Injection Enable bit. Default is 00b.</td>
</tr>
<tr>
<td>$4 : 3$</td>
<td>RW1C</td>
<td>Flit Rx Status . 00b = No Test Flits received . 01b = Received at least one Test Flit without CRC error . All other encodings are reserved Default is 00b.</td>
</tr>
<tr>
<td>5</td>
<td>$R O$</td>
<td>Link State Request Injection Status for Stack 0 · Ob = No request injected · 1b = Completed Request Injection This bit is cleared to Ob on a Ob-to-1b transition of 'Link State Request or Response Injection Enable'.</td>
</tr>
<tr>
<td>6</td>
<td>$R O$</td>
<td>Link State Response Injection Status for Stack 0 · Ob = No response injected · 1b = Completed Response Injection This bit is cleared to Ob on a Ob-to-1b transition of 'Link State Request or Response Injection Enable'.</td>
</tr>
<tr>
<td>7</td>
<td>$R O$</td>
<td>Link State Request Injection Status for Stack 1 · Ob = No request injected · 1b = Completed Request Injection This bit is cleared to Ob on a Ob-to-1b transition of 'Link State Request or Response Injection Enable'.</td>
</tr>
<tr>
<td>8</td>
<td>$R O$</td>
<td>Link State Response Injection Status for Stack 1 · 0b = No response injected · 1b = Completed Response Injection This bit is cleared to Ob on a Ob-to-1b transition of 'Link State Request or Response Injection Enable'.</td>
</tr>
<tr>
<td>$1 0 : 9$</td>
<td>$R O$</td>
<td>Retry Injection Status . 00b = No errors injected on Transmitted Flits · 01b = Injected error on at least one transmitted Flit · 10b = Finished error injection sequence on transmitted Flits · 11b = Reserved This field is cleared to 00b on a Ob-to-1b transition of 'Retry Injection Enable'.</td>
</tr>
<tr>
<td>11</td>
<td>$R O$</td>
<td>Number of Retries Exceeded Threshold Set to 1b if the number of independent retry events exceed the threshold defined in 'Tx Retry Error Threshold'. This bit is cleared to Ob on a Ob-to-1b transition of 'Retry Injection Enable'.</td>
</tr>
<tr>
<td>$3 1 : 1 2$</td>
<td>RsvdZ</td>
<td>Reserved</td>
</tr>
</table>

### 9.5.4.4.4 Link State Injection Control Stack 0 (Offset 34h from D2DOFF)

As mentioned in Section 11.2, this register only takes effect when the Adapter is in Adapter
Compliance Mode. With respect to this register, the Adapter must trigger the corresponding RDI
handshakes if the required conditions are met. Also, if Link State Injection Control is enabled, then
unexpected responses are discarded and could lead to timeouts if the expected response is not
received within the 8-ms timeout window.

<table>
<caption>Table 9-75. Link State Injection Control Stack 0</caption>
<tr>
<th>Bit</th>
<th>Attributes</th>
<th>Description</th>
</tr>
<tr>
<td>0</td>
<td>RW</td>
<td>Link State Request or Response Injection Enable at Tx . Ob = Link State Request or Response Injection not enabled at Tx · 1b = Link State Request or Response Injection enabled at Tx</td>
</tr>
<tr>
<td>1</td>
<td>RW</td>
<td>Injection Type · Ob = Inject a request packet with the request matching "Link Request" field · 1b = Inject a response packet with the response matching "Link Response" field when a request matching "Link Request" field is received</td>
</tr>
<tr>
<td>5:2</td>
<td>RW</td>
<td>Link Request The encodings match the State request encodings of FDI.</td>
</tr>
<tr>
<td>9:6</td>
<td>RW</td>
<td>Link Response The encodings match the State response encodings of FDI.</td>
</tr>
<tr>
<td>31:10</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

### 9.5.4.4.5 Link State Injection Control Stack 1 (Offset 38h from D2DOFF)

As mentioned in Section 11.2, this register only takes effect when the Adapter is in Adapter
Compliance Mode. With respect to this register, the Adapter must trigger the corresponding RDI
handshakes if the required conditions are met. Also, if Link State Injection Control is enabled, then
unexpected responses are discarded and could lead to timeouts if the expected response is not
received within the 8-ms timeout window.

<table>
<caption>Table 9-76. Link State Injection Control Stack 1</caption>
<tr>
<th>Bit</th>
<th>Attributes</th>
<th>Description</th>
</tr>
<tr>
<td>0</td>
<td>RW</td>
<td>Link State Request or Response Injection Enable at Tx · Ob = Link State Request or Response Injection not enabled at Tx · 1b = Link State Request or Response Injection enabled at Tx</td>
</tr>
<tr>
<td>1</td>
<td>RW</td>
<td>Injection Type · Ob = Inject a request packet with the request matching "Link Request" field · 1b = Inject a response packet with the response matching "Link Response" field when a request matching "Link Request" field is received</td>
</tr>
<tr>
<td>5:2</td>
<td>RW</td>
<td>Link Request The encodings match the State request encodings of FDI.</td>
</tr>
<tr>
<td>$9 : 6$</td>
<td>RW</td>
<td>Link Response The encodings match the State response encodings of FDI.</td>
</tr>
<tr>
<td>$3 1 : 1 0$</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

### 9.5.4.4.6 Retry Injection Control (Offset 40h from D2DOFF)

<table>
<caption>Table 9-77. Retry Injection Control</caption>
<tr>
<th>Bit</th>
<th>Attributes</th>
<th>Description</th>
</tr>
<tr>
<td>0</td>
<td>RW</td>
<td>Retry Injection Enable Setting this bit to 1b enables and starts error injections at Tx to force Retry on the UCIe Link. Clearing this bit to 0b stops Flit injection on the Link. Default is 0b.</td>
</tr>
<tr>
<td>$3 : 1$</td>
<td>RW</td>
<td>Error Injection Type on Transmitted Flits . 000b = No errors injected on Transmitted Flits · 001b = 1-bit error injected in 'Byte Offset' of the Flit, it is permitted to invert any bit in the corresponding byte position · 010b = 2-bit error injected in 'Byte Offset' of the Flit, it is permitted to invert any two bits in the corresponding byte position · $0 1 1 b =$ 3-bit error injected in 'Byte Offset' of the Flit, it is permitted to invert any three bits in the corresponding byte position . All other encodings are reserved Default is 000b.</td>
</tr>
<tr>
<td>$1 1 : 4$</td>
<td>RW</td>
<td>Byte Offset See 'Error Injection Type on Transmitted Flits'. $0 0 h \quad m e a n s$ error is injected on Byte 0, 01h means error is injected in Byte 1, and Default is 00h.</td>
</tr>
<tr>
<td>$1 9 : 1 2$</td>
<td>RW</td>
<td>Number of Flits between Injected Errors A nonzero value indicates the exact number of Flits after which a subsequent error is injected. A value of 0 will inject errors after a pseudo-random number of Flits 31, chosen from a 32b LFSR output. $D e f a u l t \quad i s \quad 0 0 h .$</td>
</tr>
<tr>
<td>27:20</td>
<td>RW</td>
<td>Number of Errors Injected Represents the number of errors injected on the Transmitted Flits. A value of 0 indicates that the error injection continues until the Retry Injection Enable is disabled. Default is 00h.</td>
</tr>
<tr>
<td>30:28</td>
<td>RW</td>
<td>Flit Type for Error Injection . 000b = Inject errors on any Flit type. · 001b = Only inject errors on NOP Flits. · 010b = Only inject errors on Payload Flits (Protocol Flits or Test Flits). · 011b = Only inject errors on Test Flits. . 100b = Only inject errors on Payload Flits. Subsequent errors injected on the for this case). same sequence number (`Number of Flits between Injected Errors' is ignored Note: The 100b value can be used to test Replay number Rollover rules. . All other encodings are reserved Default value is 000b.</td>
</tr>
<tr>
<td>31</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
<tr>
<td>$3 5 : 3 2$</td>
<td>RW</td>
<td>Tx Retry Error Threshold If the number of independent retry events exceeds this threshold, Adapter must log this in 'Number of Retries Exceeded Threshold' and trigger Retrain on RDI. RDI state status going to Retrain also clears the internal count of independent retry events. Default value is 0h.</td>
</tr>
<tr>
<td>63:36</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

### 9.5.4.5 PHY Test/Compliance Register Block

Certain register bits described in this section take effect only when the PHY enters "PHY Compliance"
mode. This mode is entered when bit 0 of 'Physical Layer Compliance Control 1' register is written and
PHY subsequently enters PHYRETRAIN state. The latter happens when SW retrains the link. These
register bits are tagged with @PHY-Compliance for easy readability and intuitive understanding.

Transition to TRAINERROR @PHY-Compliance does not reset any of the registers defined in this
section.

SW is required to place the Adapter in one of the Compliance modes (defined in the Adapter
Compliance Control register) before enabling @PHY-Compliance.

All modules of a Link must be in @PHY-Compliance at the same time. The Link behavior is undefined
if a subset of modules of a Link are in @PHY-Compliance and others are not. All registers in this
section are replicated, one per module, as follows:

· Module 0 registers start at Offset 000h from PHYOFF

· Module 1 registers start at Offset 400h from PHYOFF

· Module 2 registers start at Offset 800h from PHYOFF

· Module 3 registers start at Offset COOh from PHYOFF

If certain modules are not implemented, those registers become reserved (as shown with gray boxes
in Figure 9-6).

### 9.5.4.5.1 Physical Layer Compliance Control 1 (Offsets 000h, 400h, 800h, and C00h from PHYOFF)

<table>
<caption>Table 9-78. Physical Layer Compliance Control 1 (Sheet 1 of 2)</caption>
<tr>
<th>Bit</th>
<th>Attributes</th>
<th>Description</th>
</tr>
<tr>
<td>0</td>
<td>RW</td>
<td>Compliance Enable for Physical Layer Setting this bit to 1b puts the Physical Layer in "PHY Compliance" on the next entry into PHYRETRAIN state. Even if RDI status moves to Active, it does not assert pl_trdy to the Adapter in this mode. Default is 0b.</td>
</tr>
<tr>
<td>1</td>
<td>RW</td>
<td>Scrambling Disabled @PHY-Compliance, when set to 1b, Physical Layer disables scrambling. Default is 0b.</td>
</tr>
<tr>
<td>2</td>
<td>RW</td>
<td>PHY Compliance Operation Trigger @PHY-Compliance, transitioning this bit from 0b-to-1b starts one iteration of the Link training basic operations set by `PHY Compliance Operation Type'. `PHY Compliance Operation Type' field identifies which of the Link training basic operations is performed. 'Training Setup 1', 'Training Setup 2', 'Training Setup 3', and 'Training Setup 4' registers determine the parameters to be used for this. Default is 0b.</td>
</tr>
</table>

<table>
<caption>Table 9-78. Physical Layer Compliance Control 1 (Sheet 2 of 2)</caption>
<tr>
<th>Bit</th>
<th>Attributes</th>
<th>Description</th>
</tr>
<tr>
<td rowspan="3">5:3</td>
<td rowspan="3">RW</td>
<td>PHY Compliance Operation Type @PHY-Compliance, where the Link training basic operation (see Section 4.5.1) is performed when `PHY Compliance Operation Trigger' transitions from 0b to 1b · 000b = No operation · 001b = Transmitter initiated Data-to-Clock point test (see Section 4.5.1.1) · 010b = Transmitter initiated Data-to-Clock eye width sweep (see Section 4.5.1.2)</td>
</tr>
<tr>
<td>· 011b = Receiver initiated Data-to-Clock point training (see Section 4.5.1.3) · 100b = Receiver initiated Data-to-Clock width sweep training (see Section 4.5.1.4)</td>
</tr>
<tr>
<td>· 101b = If the current state is MBTRAIN.RXDESKEW and the operating data rate is &gt; 32 GT/s, perform the relevant sideband handshakes to transition the state to MBTRAIN.DATACENTER1 and continue the Link training steps. Note that the "Initialization Control" settings of the PHY Initialization and Debug register apply to pause Link training at a subsequent state. Typical usage of this encoding is for software to step through the Link state machine to permit for Tx adjustments as software sweeps through the different EQ settings. · All other encodings are reserved</td>
</tr>
<tr>
<td>$7 : 6$</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
<tr>
<td rowspan="4">9:8</td>
<td rowspan="4">RW</td>
<td>Rx Vref Offset Enable @PHY-Compliance: . 00b = No change to trained Rx Vref value</td>
</tr>
<tr>
<td>· 01b = Add Rx Vref offset to trained Rx Vref value (up to maximum permitted Vref value)</td>
</tr>
<tr>
<td>· 10b = Subtract Rx Vref offset to trained Rx Vref value (down to minimum permitted Rx Vref, any negative value to be terminated at 0)</td>
</tr>
<tr>
<td>· 11b = Reserved</td>
</tr>
<tr>
<td>$1 7 : 1 0$</td>
<td>RW</td>
<td>Rx Vref Offset @PHY-Compliance, when 'Rx Vref Offset Enable' is set to 01b or 10b, this is the value that needs to be added or subtracted as defined in 'Rx Vref Offset Enable'. The Rx Vref value, after applying the Rx Vref offset, is expected to be monotonically $o f f s e t \quad r e l a t i v e \quad t o \quad t h e \quad t r a i n e d \quad v a l u e \quad a n d \quad m u s t \quad h a v e \quad s u f f i c i e n t \quad r a n g e \quad t o \quad c o v e r \quad t h e$ $\begin{array}{} { \text { Rx Vref Offset will be applied during } T x \text { or Ror Rx Data to Point Traint Trand the } } \\ { \text { Physical Layer must compare the per Lane errors with with error threshoid in per } } \end{array}$ Lane comparison', and aggregate Lane errors with 'Max Error Threshold in Aggregate Comparison' in the 'Training Setup 4' register. If the errors measured are greater than the corresponding threshold, then the device must set the Rx Vref offset status register to "failed". Software must increase or decrease the Rx Vref Offset by one from the previous value. Default is 00h.</td>
</tr>
<tr>
<td>$6 3 : 1 8$</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

### 9.5.4.5.2 Physical Layer Compliance Control 2 (Offsets 008h, 408h, 808h, and C08h from PHYOFF)

<table>
<caption>Table 9-79. Physical Layer Compliance Control 2 (Sheet 1 of 2)</caption>
<tr>
<th>Bit</th>
<th>Attributes</th>
<th>Description</th>
</tr>
<tr>
<td>0</td>
<td>RW</td>
<td>Even UI Compare Mask @PHY-Compliance, if this bit is set, any compare results for even UIs are masked (i.e., not counted toward error in per Lane or aggregate comparison (see Section 4.4)), where Even UI refers as to a Unit Interval data eye, the first data UI and · $O b = N o \quad e v e n \quad U I \quad c o m p a r e \quad r e s u l t \quad m a s k i n g$ • Default is 0b.</td>
</tr>
<tr>
<td>1</td>
<td>RW</td>
<td>Odd UI Compare Mask @PHY-Compliance, if this bit is set, any compare results for odd UIs are masked (i.e., not counted toward error in per Lane or aggregate comparison (see Section 4.4)), where Odd UI refers as to a Unit Interval data eye, the second data UI and every subsequent alternate UI). · Ob = No odd UI compare result masking compare results masked $D e f a u l t \quad i s \quad 0 b .$</td>
</tr>
<tr>
<td>2</td>
<td>RW</td>
<td>Track Enable If @PHY-Compliance { If this bit is set, Track Transmission is enabled during one of the operations set by Section 5.5.1. `PHY compliance operation type'. Track transmission complies with descriptions in } Else { The appropriate sideband handshakes as described in Section 4.6 needs to be followed irrespective of the value of this bit }</td>
</tr>
<tr>
<td>3</td>
<td>RW</td>
<td>Compare Setup · Ob = Aggregate comparison · 1b = Per Lane comparison Default is 0b. See Section 4.4 for more details.</td>
</tr>
<tr>
<td>4</td>
<td>RW</td>
<td>Group A UI Compare Mask This field is applicable if @PHY-Compliance and for an operating data rate &gt; 32 GT/s only. If this bit is set to 1, any compare results for Group A UIs are masked (i.e., not counted toward error in per-Lane nor aggregate comparison (see Section 4.4)), where Group A UI refers to a Unit Interval data $\mathrm { e y e } ,$ the 1st data UI and every subsequent 4th UI. · 0 = No Group A UI compare result masking · 1 = Group A UI compare result is masked Default is 0.</td>
</tr>
<tr>
<td>5</td>
<td>RW</td>
<td>Group B UI Compare Mask This field is applicable if @PHY-Compliance and for an operating data rate &gt; 32 GT/s only. If this bit is set to 1, any compare results for Group B UIs are masked (i.e., not counted toward error in per-Lane nor aggregate comparison (see Section 4.4)), where Group B UI refers to a Unit Interval data eye, the 2nd data UI and every subsequent 4th UI. · 0 = No Group B UI compare result masking · 1 = Group B UI compare result is masked Default is 0.</td>
</tr>
</table>

<table>
<caption>Table 9-79. Physical Layer Compliance Control 2 (Sheet 2 of 2)</caption>
<tr>
<th>Bit</th>
<th>Attributes</th>
<th>Description</th>
</tr>
<tr>
<td>6</td>
<td>RW</td>
<td>Group C UI Compare Mask This field is applicable if @PHY-Compliance and for an operating data rate &gt; 32 GT/s only. If this bit is set to 1, any compare results for Group C UIs are masked (i.e., not counted toward error in per-Lane nor aggregate comparison (see Section 4.4)), where Group C UI refers to a Unit Interval data eye, the 3rd data UI and every subsequent 4th UI. · 0 = No Group C UI compare result masking · 1 = Group C UI compare result is masked Default is 0.</td>
</tr>
<tr>
<td>7</td>
<td>RW</td>
<td>Group D UI Compare Mask This field is applicable if @PHY-Compliance and for an operating data rate &gt; 32 GT/s only. If this bit is set to 1, any compare results for Group D UIs are masked (i.e., not counted toward error in per-Lane nor aggregate comparison (see Section 4.4)), where Group D UI refers to a Unit Interval data eye, the 4th data UI and every subsequent 4th UI. · 0 = No Group D UI compare result masking · 1 = Group D UI compare result is masked Default is 0.</td>
</tr>
<tr>
<td>31:8</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

<table>
<caption>$9 . 5 . 4 . 5 . 3$ Physical Layer Compliance Status 1 (Offsets 010h, 410h, 810h, and C10h from PHYOFF) Table 9-80. Physical Layer Compliance Status 1</caption>
<tr>
<th>Bit</th>
<th>Attributes</th>
<th>Description</th>
</tr>
<tr>
<td>0</td>
<td>$R O$</td>
<td>PHY in Compliance mode If (@PHY-Compliance) 1b. Else 0b.</td>
</tr>
<tr>
<td>1</td>
<td>RO</td>
<td>PHY Compliance operation status If (@PHY-Compliance) { This bit is set to 1b if 'PHY compliance operation type' in 'Physical Layer Compliance Control 1' register is 001b, 010b, 011b, or 100b and hardware has performed the required operation. Else the bit is cleared to 0b. }</td>
</tr>
<tr>
<td>$3 : 2$</td>
<td>RW1C</td>
<td>Rx Vref Offset Operation Status @PHY-Compliance: · 00b = Device does not support applying any Rx Vref Offset value · 01b = 'Rx Vref Offset' has not been applied · 10b = Rx Vref Offset has been successfully applied . 11b = When any of the following conditions are met: - Did not apply 'Rx Vref Offset' as the resulting value exceeds the value supported by hardware - Applied the requested setting and the test failed (i.e., Link training failed) Default is 00b.</td>
</tr>
<tr>
<td>31:4</td>
<td>RsvdZ</td>
<td>Reserved</td>
</tr>
</table>

#### $9 . 5 . 4 . 5 . 4$ Physical Layer Compliance Status 2 (Offsets 018h, 418h, 818h, and C18h from PHYOFF)

<table>
<caption>Table 9-81. Physical Layer Compliance Status 2</caption>
<tr>
<th>Bit</th>
<th>Attributes</th>
<th>Description</th>
</tr>
<tr>
<td>$3 1 : 0$</td>
<td>RW1C</td>
<td>Aggregate Error Count @PHY-Compliance, this is the Error count of aggregate error comparison when 'PHY Compliance Operation Type' is 001b or 011b (performing point tests). Default is 0000 0000h.</td>
</tr>
<tr>
<td>39:32</td>
<td>$R O$</td>
<td>Supported Rx Vref Range Up Max step count supported up from the trained Rx Vref value for Vref margining.</td>
</tr>
<tr>
<td>47:40</td>
<td>RO</td>
<td>Supported Rx Vref Range Down Max step count supported down from the trained Rx Vref value for Vref margining.</td>
</tr>
<tr>
<td>$5 5 : 4 8$</td>
<td>RO</td>
<td>$\begin{array}{} { \text { Trained Value for Rx Vref } } \\ { \text { Rx Vref as trained, in resolution counts } } \end{array} .$</td>
</tr>
<tr>
<td>$6 3 : 5 6$</td>
<td>$R O$</td>
<td>Vref Step Count Resolution Increase in Vref value in mV between two consecutive encodings in ascending order.</td>
</tr>
</table>

### $9 . 5 . 4 . 5 . 5$ Physical Layer Compliance Status 3 (Offsets 020h, 420h, 820h, and C20h from PHYOFF)

<table>
<caption>Table 9-82. Physical Layer Compliance Status 3</caption>
<tr>
<th>Bit</th>
<th>Attributes</th>
<th>Description</th>
</tr>
<tr>
<td>$6 3 : 0$</td>
<td>RO</td>
<td>Per Lane Comparison Result Per Lane comparison result in PHY Compliance when 'PHY Compliance Operation Type' is 001b or 011b (performing point tests) and `Comparison Setup' is 1b (Per Lane comparison). [63:0]: Compare Results of all Logical Data Lanes (0h $\begin{array}{} \text { Fail \left(Errors> Max Error Threshold\right), } \\ \mathrm { P a s s } \left( \mathrm { E r r o r s } < = \mathrm { M a x } \mathrm { E r r o r } \mathrm { T h r e s h o l d } \right) \end{array}$ UCIe-A {RD_L [63], RD_L [62], ... , RD_L [1], RD_L [0]} UCIe-A x32 {32'h0, RD_L [31], RD_L [30], ... , RD_L [1], RD_L [0]} UCIe-S {48'h0, RD_L [15], RD_L [14], ... , RD_L [1], RD_L [0]} Default is all 0s.</td>
</tr>
</table>

### 9.5.5 Implementation Specific Register Blocks

These are left to be vendor defined. There is a separate implementation specific register Block for
D2D Adapter and PHY. These register blocks should carry the same header as defined in Table 9-26,
at offset Oh of the register block. And the VendorID should be set to the specific vendor's ID and the
'VendorID register block' field set to 2h or 3h to indicate that it is a vendor specific register block. The
other fields in that header are set by the vendor to track their revision number and the block length.
Max length cannot exceed 1MB in size and length is always in multiples of 4KB. Implementations are
highly encouraged to pack registers and reduce length of the region as much as possible.

#### 9.6 UCIe Link Registers in Streaming Mode and System SW/ FW Implications

##### IMPLEMENTATION NOTE

While the SW view of Protocol Layer for streaming protocols is implementation-
specific, it is strongly recommended that UCIe link-related registers defined in this
chapter be implemented as-is for streaming mode solutions as well. If a streaming
mode solution chooses to support the industry-standard PCIe hierarchical tree model
for enumeration/control, it must be compliant with the enumeration model and
registers defined in this chapter. A UCIe port in such an implementation would expose
UCIe link registers consistent with the RP/DSP or EP/USP functionality it represents.

In some streaming mode solutions, it might be desirable to implement UCIe link as a
fully symmetric link, such as in a Symmetric Multi-Processing system that uses UCIe
as a D2D interconnect. In such solutions, there is no notion of Upstream Port or
Downstream Port on a UCIe link and also typically system firmware knows the D2D
link connections a priori and it is able to configure them without requiring any "link
discovery" mechanisms. It is recommended that both ends of the link implement
UCIe registers defined for a Root Port, in such streaming mode solutions. Note that in
this model, several link-related features become fully symmetric as well. For
example, link training, mailbox trigger, and direct link-event/error reporting to
Software are now possible from either end of the link. Whether such symmetric UCIe
links are exposed to OS for native management, or system FW fully manages these
links, is a system-architecture choice. Exposing such links natively to the OS could be
in the form of exposing each side as an ACPI device or in the form of an FW
intermediary that emulates a traditional PCIe hierarchical tree model for the
symmetric link. Such choices are implementation-specific and could depend on the
extent of OS support for symmetric topology.

###### 9.7 MSI and MSI-X Capability in Hosts/Switches for UCIe Interrupt

Follow the base spec for details, but MSI/MSI-X capability implemented in host and switch must
request 2 vectors for UCIe usage - 1 for Link status events and 1 for Link error events. Note that in
MSI scenario, OS might not always allot both the requested vectors and in that case both the Link
Status and Link error events use the same MSI vector number. The MSI designs must also support the
Pending and Mask bits. MSI capability in UiRB must always set the 'Next Capability Pointer' field to 0h.
SW must check for a value of 0005h in Bytes 0 and 1 of a capability to infer that it is an MSI
capability. SW must terminate the capability linked list in UiRB when it sees the MSI Capability.

####### 9.8 UCIe Early Discovery Table (UEDT)

<table>
<caption>Table 9-83. UEDT Header</caption>
<tr>
<th>Field</th>
<th>Byte Offset</th>
<th>$L e n g t h$</th>
<th>Description</th>
</tr>
<tr>
<td>Signature</td>
<td>00h</td>
<td>4</td>
<td>Signature for the UCIe Early Discovery Table (UEDT).</td>
</tr>
<tr>
<td>Length</td>
<td>04h</td>
<td>4</td>
<td>Length, in bytes, of the entire UEDT.</td>
</tr>
<tr>
<td>Revision</td>
<td>08h</td>
<td>1</td>
<td>Value is 1h for the first UCIe instance.</td>
</tr>
<tr>
<td>Checksum</td>
<td>09h</td>
<td>1</td>
<td>Entire table must sum to 0.</td>
</tr>
<tr>
<td>OEM ID</td>
<td>0Ah</td>
<td>6</td>
<td>OEM ID</td>
</tr>
<tr>
<td>OEM Table ID</td>
<td>10h</td>
<td>8</td>
<td>Manufacturer Model ID</td>
</tr>
<tr>
<td>OEM Revision</td>
<td>18h</td>
<td>4</td>
<td>OEM Revision</td>
</tr>
<tr>
<td>Creator ID</td>
<td>1Ch</td>
<td>4</td>
<td>Vendor ID of the utility that created this table.</td>
</tr>
<tr>
<td>Creator Revision</td>
<td>20h</td>
<td>4</td>
<td>Revision of the utility that created this table.</td>
</tr>
<tr>
<td>UEDT Structure[n]</td>
<td>24h</td>
<td>Varies</td>
<td>A list of UEDT structures for this implementation. · 0h = UCIe Link structure (UCLS) . All other encodings are reserved</td>
</tr>
</table>

<table>
<caption>Table 9-84. UCIe Link Structure (UCLS)</caption>
<tr>
<th>Field</th>
<th>Byte Offset</th>
<th>Length in Bytes</th>
<th>Description</th>
</tr>
<tr>
<td>Type</td>
<td>00h</td>
<td>1</td>
<td>Signature for the UCIe Early Discovery Table (UEDT).</td>
</tr>
<tr>
<td>Revision</td>
<td>01h</td>
<td>1</td>
<td>Value is 1h for the first UCLS definition.</td>
</tr>
<tr>
<td>Record Length</td>
<td>02h</td>
<td>2</td>
<td>Length of this record, in bytes.</td>
</tr>
<tr>
<td>UID</td>
<td>04h</td>
<td>4</td>
<td>Host Bridge Unique ID. Used to associate a UCLS instance with a Host Bridge instance. The value of this field shall match the output of UID under the associated Host Bridge in ACPI namespace.</td>
</tr>
<tr>
<td>UCIe Stack Size</td>
<td>08h</td>
<td>4</td>
<td>· $1 h = O n e \quad R P$ · 2h = Two RPs</td>
</tr>
<tr>
<td>Reserved</td>
<td>0Ch</td>
<td>4</td>
<td>Reserved</td>
</tr>
<tr>
<td>Base</td>
<td>10h</td>
<td>8</td>
<td>Base address of UiRB, aligned to a 4-KB boundary.</td>
</tr>
<tr>
<td>Length</td>
<td>18h</td>
<td>8</td>
<td>$\tan$ anywhere from 12 KB to 2 MB, in multiples</td>
</tr>
<tr>
<td>$D F 1$</td>
<td>$2 0 h$</td>
<td>1</td>
<td>Device Function of the PCIe/CXL RP 1 associated with the UCLS.</td>
</tr>
<tr>
<td>DF2</td>
<td>21h</td>
<td>1</td>
<td>Device Function of the PCIe/CXL RP 2 (if multi-stack implementation) associated with the UCLS.</td>
</tr>
</table>

####### 10.0 Interface Definitions

This chapter will cover the details of interface operation and signal definitions for the Raw Die-to-Die
Interface (RDI), as well as the Flit-Aware Die-to-Die Interface (FDI). Common rules across RDI and
FDI are covered as a separate section. The convention used in this chapter is that "assertion" of a
signal is for Ob to 1b transition, and "de-assertion" of a signal is for 1b to Ob transition. A "pulse" of
"n" cycles for a signal is defined as an event where the signal transitions from 0b to 1b, stays 1b for
"n" clock cycles, and subsequently returns to Ob. A receiver sampling this signal on the same clock as
the transmitter will see it being asserted for "n" clock cycles. If a value of "n" is not specified, it is
interpreted as a value of one. In the context of error signals defined as pulses, the receiving logic for
error logging must treat the rising edge as a new event indication and not rely on the length of the
pulse.

In this chapter, interface reset/domain reset also applies to all forms of Conventional Reset defined in
PCIe Base Specification, if the Protocol is PCIe or CXL. In the sections that follow, "UCIe Flit mode"
refers to scenarios in which the Link is not operating in Raw Format, and "UCIe Raw Format" or "Raw
Format" refers to scenarios in which the Link is operating in Raw Format.

######## 10.1 Raw Die-to-Die Interface (RDI)

This section defines the signal descriptions and functionality associated with a single instance of Raw
Die-to-Die Interface (RDI). A single instance could be used for a configuration associated with a single
Die-to-Die module (i.e., one Die-to-Die Adapter for one module), or a single instance is also
applicable for configurations where multiple modules are grouped together for a single logical Die-to-
Die Link (i.e., one Die-to-Die Adapter for multiple modules). Figure 10-1 shows example
configurations using RDI.

<figure>
<figcaption>Figure 10-1. Example configurations using RDI</figcaption>

Die-to-Die
Adapter

$D i e - t o - D i e$
Adapter

$R D I$

$R D I$

Physical Layer
(single module)

Multi-module PHY Logic
(two modules)

$A F E$

Module 0 AFE/PHY Logic

Module 1 AFE/PHY Logic

(a)

(b)

Die-to-Die
Adapter

$R D I$

Multi-module PHY Logic
(four modules)

Module 0 AFE/PHY Logic

Module 1 AFE/PHY Logic

Module 2 AFE/PHY Logic

Module 3 AFE/PHY Logic

(c)

</figure>

Table 10-1 lists the RDI signals and their descriptions. In Table 10-1:

. $p l \_ *$ indicates that the signal is driven away from the Physical Layer to the Die-to-Die Adapter.

. lp * indicates that the signal is driven away from the Die-to-Die Adapter to the Physical Layer.

<table>
<caption>Table 10-1. RDI signal list (Sheet 1 of 5)</caption>
<tr>
<th>Signal Name</th>
<th>Signal Description</th>
</tr>
<tr>
<td>$l c l k$</td>
<td>The clock at which RDI operates.</td>
</tr>
<tr>
<td>$l p \_ i r d y$</td>
<td>Adapter to Physical Layer signal indication that the Adapter has data to send. This must be asserted if lp_valid is asserted and the Adapter wants the Physical Layer to sample the data. lp_irdy must not be presented by the Adapter when pl_state_sts is Reset except when the status transitions from LinkError to Reset. On a LinkError to Reset transition, it is permitted for lp_irdy to be asserted for a few clocks but it must be de-asserted eventually. Physical Layer must ignore lp_irdy when status is Reset.</td>
</tr>
<tr>
<td>lp_valid</td>
<td>Adapter to Physical Layer indication that data is valid on the corresponding lp_data bytes.</td>
</tr>
<tr>
<td>$l p \_ d a t a \left[ N B Y T E S - 1 : 0 \right] \left[ 7 : 0 \right]$</td>
<td>Layer data, where 'NBYTES' equals number of bytes determined by the</td>
</tr>
<tr>
<td>lp_retimer_crd</td>
<td>$W h e n \quad a s s e r t e d \quad a t \quad a \quad r i s i n g \quad c l o c k \quad e d g e , i t \quad i n d i c a t e s \quad a \quad s i n g l e \quad c r e d i t \quad r e t u r n \quad f r o m \quad t h e \quad A d a p t e r \quad t o$ the mainband data. This signal must NOT assert for dies that are not UCIe Retimers.</td>
</tr>
<tr>
<td>$p l \_ t r d y$</td>
<td>The Physical Layer is ready to accept data. Data is accepted by the Physical Layer when pl_trdy, lp_valid, and lp_irdy are asserted at the rising edge of lclk. This signal must only be asserted if pl_state_sts is Active or when performing the pl_stallreq/lp_stallack handshake when the pl_state_sts is LinkError (see Section 10.3.3.7).</td>
</tr>
<tr>
<td>pl_valid</td>
<td>Physical Layer to Adapter indication that data is valid on pl_data.</td>
</tr>
<tr>
<td>pl_data [NBYTES-1 : 0] [7: 0]</td>
<td>Physical Layer to Adapter data, where NBYTES equals the number of bytes determined by the data width for the RDI instance.</td>
</tr>
</table>

<table>
<caption>Table 10-1. RDI signal list (Sheet 2 of 5)</caption>
<tr>
<th>Signal Name</th>
<th>Signal Description</th>
</tr>
<tr>
<td>pl_retimer_crd</td>
<td>When asserted at a rising clock edge, it indicates a single credit return from the Retimer to the Adapter. Each credit corresponds to 256B of mainband data. This signal must NOT assert if the remote Link partner is not a Retimer.</td>
</tr>
<tr>
<td rowspan="3">lp_state_req [3: 0]</td>
<td>Adapter request to Physical Layer to request state change. Encodings as follows:</td>
</tr>
<tr>
<td>$\begin{array}{} { 0 0 0 0 b : N O P } \\ { 0 0 0 1 b : A c t i v e } \end{array}$ 1001b: LinkReset</td>
</tr>
<tr>
<td>1011b: Retrain 0100b: L1 1100b: Disabled 1000b: L2 All other encodings are reserved.</td>
</tr>
<tr>
<td>lp_linkerror</td>
<td>Adapter to Physical Layer indication that an error has occurred which requires the Link to go down. Physical Layer must move to LinkError state and stay there as long as The reason for having this be an indication decoupled from regular $\begin{array}{} { \text { 1p 1 inkerror=1 } } \\ { \text { state transitions is t } } \end{array}$ allow immediate action on part of the Adapter and Physical Layer in order to provide the quickest path for error containment when applicable (for example, a viral error escalation must map to the LinkError state). The Adapter must OR internal error conditions with lp_linkerror received from Protocol Layer on FDI.</td>
</tr>
<tr>
<td rowspan="4">pl_state_sts [3: 0]</td>
<td>Physical Layer to Adapter Status indication of the Interface. Encodings as follows:</td>
</tr>
<tr>
<td>0000b: Reset 1001b: LinkReset</td>
</tr>
<tr>
<td>0001b: Active 1010b: LinkError</td>
</tr>
<tr>
<td>0011b: Active.PMNAK 1011b: Retrain 0100b: L1 1100b: Disabled 1000b: L2 All other encodings are reserved. The status signal is permitted to transition from Physical Layer autonomously when applicable. For example the Physical Layer asserts the Retrain status when it decides to enter retraining either autonomously or when requested by remote agent.</td>
</tr>
<tr>
<td>pl_inband_pres</td>
<td>Physical Layer to the Adapter indication that the Die-to-Die Link has finished training and is ready for RDI transition to Active and Stage 3 of bring up. Once it transitions to 1b, this must stay 1b until Physical Layer determines the Link is down (i.e., the Link Training State Machine transitions to TrainError or Reset).</td>
</tr>
</table>

<table>
<caption>Table 10-1. RDI signal list (Sheet 3 of 5)</caption>
<tr>
<th>Signal Name</th>
<th>Signal Description</th>
</tr>
<tr>
<td>pl_error</td>
<td>Physical Layer to the Adapter indication that it has detected a framing related error which is recoverable through Link Retrain. An example is where the Physical Layer received an invalid encoding on the Valid Lane. It is a pulse of one or more cycles that must occur only when RDI is in Active state. It is permitted to de-assert at the same clock edge where the state transitions away from Active state. It is pipelined with the receive data path such that the error indication reaches the Adapter before or at the same time as the corrupted data. Physical Layer is expected to go through Retrain flow after this signal has been asserted and it must not send valid data to Adapter until the Link has retrained. It is permitted for the Physical Layer to squash the pl_valid internally for the corrupted data. Once pl_error is asserted, pl_valid should not be asserted (without pl_error assertion in the same cycle) until the state status has transitioned to Active after Retrain entry and exit. $\begin{array}{} { \text { If } p 1 \text { error=1 and } p 1 \text { val id } = 1 \text { in the same clock clorle, the Adater must dist dite } } \\ { \text { correspondina Filt \left(even if it it only partially recived whed wror asser assrerted\right). } } \end{array}$ In UCIe Flit mode, when retry is enabled, it is the responsibility of the Adapter to ensure data integrity for Flits forwarded to FDI, and that they are canceled following the rules of pl_flit_cancel if they are suspected of corruption (see Section 10.2). A couple of examples are given below: . For 68B Flit Format, the Adapter could discard partially received Flits, but in 256B Latency optimized modes, it could have processed one half correctly, and the error the other half, and so it has to track that and process future • $\begin{array}{} { \text { mavaccordingly. } } \\ { \text { Another example is is not doined berored receiving the remaing 64B of the 128B half, } } \\ { \text { Another exrors happerd berore reciving the der dor dor dis } } \end{array} ,$ it $\begin{array}{} { \text { needs to send dumm } } \\ { \text { half of the Flit. } } \end{array}$ data $I n \quad U C I e \quad F l i t$ mode with Retry enabled for the Adapter, Retrain exit would naturally result in any partially received Flits eventually (see Section 3.8). $\mathrm { I n } \mathrm { U C I e } \mathrm { F l i t } \mathrm { m o d e r }$ with Retry disabled, the Adapter must map pl_error assertion to an Error and escalate it accordingly. If the Link is operating in Raw Format, the Adapter forwards pl_error to the Protocol Layer such that it is pipeline matched to the data bus, and Protocol Layer handles it in an implementation-specific manner.</td>
</tr>
<tr>
<td>pl_cerror</td>
<td>not $\begin{array}{} { \text { Physical Layer to the Aabpter indication that a that a corrector elctable erracte detered the doetr } } \\ { \text { enabled, the Adapter must oR the ple prinde and pl } } \\ { \text { rnabled, the Adapter muust oR the errond sl } } \end{array}$ $I n \quad U C I e \quad F l i t \quad m o d e \quad w i t h \quad R e t r y \quad d i s a b l e d \quad o r \quad w h e n \quad t h e \quad L i n k \quad i s \quad o p e r a t i n g \quad i n \quad R a w \quad F o r m a t , t h e$ cycles which can occur in any RDI state. If it is a state in which $\begin{array}{} { \text { It is a pulse of one or more c } } \\ { \text { clock gating is permited, it } } \end{array}$ is the responsibility of the Physical Layer to perform the clock gating exit handshake with the Adapter before asserting this signal. Clock gating can resume once pl_cerror de-asserts and all other conditions permitting clock gating are satisfied.</td>
</tr>
<tr>
<td>pl_nferror</td>
<td>Physical Layer to the Adapter indication that a non-fatal error was detected. There is no architecturally defined error condition for the Physical Layer currently asserting this signal; however, the signal is provided on the interface for any implementation-specific non-fatal errors. The Adapter treats this in the same manner as when it received a Sideband Non- Fatal Error Message from the remote Link partner. It is a pulse of one or more cycles that can occur in any RDI state. If it is a state where clock gating is permitted, it is the responsibility of the Physical Layer to perform the clock gating exit handshake with the Adapter before asserting this signal. Clock gating can resume after pl_nferror is de-asserted and all other conditions permitting clock gating have been met.</td>
</tr>
<tr>
<td>pl_trainerror</td>
<td>Indicates a fatal error from the Physical Layer. Physical Layer must transition pl_state_sts to LinkError if not already in LinkError state. This must be escalated to upper Protocol Layers based on the mask and severity programming of Uncorrectable Internal Error in the Adapter. Implementations are permitted to map any fatal error to this signal that require upper layer escalation (or interrupt generation) depending on system-level requirements. It is a level signal that can assert in any RDI state but remains asserted until RDI exits the LinkError state to Reset state.</td>
</tr>
</table>

<table>
<caption>Table 10-1. RDI signal list (Sheet 4 of 5)</caption>
<tr>
<th>Signal Name</th>
<th>Signal Description</th>
</tr>
<tr>
<td>pl_phyinrecenter</td>
<td>Physical Layer indication to Adapter that the Physical Layer is training or retraining. If this is asserted during a state where clock gating is permitted, the pl_clk_req/lp_clk_ack handshake must be performed with the upper layer. The upper layers are permitted to use this to update the "Link Training/Retraining" bit in the UCIe Link Status register.</td>
</tr>
<tr>
<td>pl_stallreq</td>
<td>Physical Layer request to Adapter to align Transmitter at Flit boundary and not send any new Flits to prepare for state transition. See Section 10.3.2.</td>
</tr>
<tr>
<td>lp_stallack</td>
<td>Adapter to Physical Layer indication that the Flits are aligned and stalled (if pl_stallreq was asserted). It is strongly recommended that this response logic be on a global free running clock, so the Adapter can respond to pl_stallreq with lp_stallack even if other significant portions of the Adapter are clock gated. See Section 10.3.2.</td>
</tr>
<tr>
<td rowspan="2">pl_speedmode $\left[ 2 : 0 \right]$</td>
<td>Current Link speed. The following encodings are used:</td>
</tr>
<tr>
<td>000b: 4 GT/s 100b: 24 GT/s 001b: 8 GT/s 101b: 32 GT/s 010b: 12 GT/s $1 1 0 b : 4 8 \quad G T / s$ 011b: 16 GT/s The Adapter must only consider this signal to be relevant when the RDI state is Active or Retrain. For multi-module configurations, all modules must operate at the same speed.</td>
</tr>
<tr>
<td>pl_max_speedmode</td>
<td>Negotiated Maximum Data Rate. The following encodings are used: 0: &lt;= 32 GT/s 1: &gt; 32 GT/s The Adapter must only consider this signal to be relevant when the RDI state transitions from Reset to Active. It indicates the negotiated maximum data rate by the Physical Layer during MBINIT.PARAM; thus, this signal can only change while RDI is in Reset state. The Adapter uses this signal to determine the negotiated maximum data rate before the Protocol Parameter exchange handshakes.</td>
</tr>
<tr>
<td>pl_lnk_cfg[2:0]</td>
<td>Current Link Configuration. Indicates the current operating width of a module. $0 0 0 b : x 4$ 100b: x64 x8 $\begin{array}{} { 1 0 1 b : \times 1 2 8 } \\ { 1 1 0 b : \times 2 5 6 } \end{array}$ $0 1 0 b : x 1 6$ 011b: x32 other encodings are reserved. $m o d u l e s . F o r \quad U C I e - S \quad t h e \quad m a x i m u m \quad e n c o d i n g \quad w o u l d \quad b e \quad x 6 4 , f o r \quad U C I e - A \quad t h e \quad m a x i m u m$ The Adapter must only consider this signal to be relevant when the RDI state is Active or Retrain. This signal indicates the total width across all Active Modules corresponding to the RDI instance.</td>
</tr>
<tr>
<td>$p l _ { - } c l k _ { - } r e q$</td>
<td>Request from the Physical Layer to remove clock gating from the internal logic of the Adapter. This is an asynchronous signal relative to 1clk from the Adapter's perspective since it is not tied to 1clk being available in the Adapter. Together with 1p_clk_ack, it forms a four-way handshake to enable dynamic clock gating in the Adapter. When dynamic clock gating is supported, the Adapter must use this signal to exit clock gating before responding with lp_clk_ack. signal to 1b. If dynamic clock gating is not supported, it is permitted for the Physical Layer to tie this</td>
</tr>
<tr>
<td>$1 p _ { - } c l k _ { - } a c k$</td>
<td>Response from the Adapter to the Physical Layer acknowledging that its clocks have been ungated in response to pl_clk_req. This signal is only asserted when pl_clk_req is asserted, and de-asserted after pl_clk_req has de-asserted. When dynamic clock gating is not supported by the Adapter, it must stage pl_clk_req internally for one or more clock cycles and turn it around as 1p_clk_ack. This way it will still participate in the handshake even though it does not support dynamic clock gating.</td>
</tr>
<tr>
<td>lp_wake_req</td>
<td>Request from the Adapter to remove clock gating from the internal logic of the Physical Layer. This is an asynchronous signal from the Physical Layer's perspective since it is not tied to 1clk being available in the Physical Layer. Together with pl_wake_ack, it forms a four-way handshake to enable dynamic clock gating in the Physical Layer. When dynamic clock gating is supported, the Physical Layer must use this signal to exit clock gating before responding with pl_wake_ack. $\begin{array}{} { \text { If dynami } } \\ { \text { to } 1 h } \end{array}$ clock gating is not supported, it is permitted for the Adapter to tie this signal</td>
</tr>
</table>

<table>
<caption>Table 10-1. RDI signal list (Sheet 5 of 5)</caption>
<tr>
<th>Signal Name</th>
<th>Signal Description</th>
</tr>
<tr>
<td>pl_wake_ack</td>
<td>Response from the Physical Layer to the Adapter acknowledging that its clocks have been ungated in response to lp_wake_req. This signal is only asserted after lp_wake_req has asserted, and is de-asserted after 1p_wake_req has de-asserted. When dynamic clock gating is not supported by the Physical Layer, it must stage lp_wake_req internally for one or more clock cycles and turn it around as pl_wake_ack. This way it will still participate in the handshake even though it does not support dynamic clock gating.</td>
</tr>
<tr>
<td>$p l _ { n } c f g \left[ N C - 1 : 0 \right]$</td>
<td>This is the sideband interface from the Physical Layer to the Adapter. See Chapter 7.0 for packet format details. NC is the width of the interface. Supported values are 8, 16, and 32. Register accesses must be implemented by hardware to be atomic regardless of the width of the interface (i.e., all 32 bits of a register must be updated in the same cycle for a 32-bit register write, and similarly all 64 bits of a register must be updated in the same cycle for a 64-bit register write).</td>
</tr>
<tr>
<td>$p l _ { - } c f g _ { - } v l d$</td>
<td>the Adapter. When asserted, indicates that pl_cfg has valid information that should be consumed by</td>
</tr>
<tr>
<td>pl_cfg_crd</td>
<td>Credit return for sideband packets from the Physical Layer to the Adapter for sideband data. Even transactions $t h a t \quad d o \quad n o t \quad c a r r y \quad d a t a \quad o r \quad c a r r y \quad 3 2 \quad b i t s \quad o f \quad d a t a \quad c o n s u m e \quad t h e \quad s a m e \quad c r e d i t \quad a n d \quad t h e \quad P h y s i c a l$ Layer returns the deallocated from its internal buffers. See Section 7.1.3.1 for additional flow control rules. A value of 1 sampled at a rising clock edge indicates a single credit return. Because the advertised credits are design parameters, the Adapter transmitter updates the credit counters with initial credits on domain reset exit, and no initialization credits are returned over the interface. Credit returns must follow the same rules of clock gating exit handshakes as the sideband packets to ensure that no credit returns are dropped by the receiver of the credit returns.</td>
</tr>
<tr>
<td>$1 p _ { - } c f g \left[ N C - 1 : 0 \right]$</td>
<td>This is the sideband interface from Adapter to the Physical Layer. See Chapter 7.0 for details. NC is the width of the interface. Supported values are 8, 16, and 32. Register accesses must be implemented by hardware to be atomic regardless of the width of the interface (i.e., all 32 bits of a register must be updated in the same cycle for a 32-bit register write, and similarly all 64 bits of a register must be updated in the same cycle for a 64-bit register write).</td>
</tr>
<tr>
<td>$1 p _ { - } c f g _ { - } v l d$</td>
<td>When asserted, indicates that lp_cfg has valid information that should be consumed by the Physical Layer.</td>
</tr>
<tr>
<td>lp_cfg_crd</td>
<td>Credit return for sideband packets from the Adapter to the Physical Layer for sideband packets. Each credit corresponds to 64 bits of header and 64 bits of data. Even transactions that do not carry data or carry 32 bits of data consume the same credit and the Adapter returns the credit once the corresponding transaction has been processed or deallocated from its internal buffers. See Section 7.1.3.1 for additional flow control rules. A value of 1 sampled at a rising clock edge indicates a single credit return. Because the advertised credits are design parameters, the Physical Layer transmitter updates the credit counters with initial credits on domain reset exit, and no initialization $C r e d i t \quad r e t u r n s \quad m u s t \quad f o l l o w \quad t h e \quad s a m e \quad r u l e s \quad o f \quad c l o c k \quad g a t i n g \quad e x i t \quad h a n d s h a k e s \quad a s \quad t h e \quad s i d e b a n d$</td>
</tr>
<tr>
<td>pl_vendor_defined [VS-1 : 0]</td>
<td>Optional Vendor Defined signals. See Section 10.3.4 for an example usage of these signals. If these signals are instantiated, but the UCIe stack is not operating in a mode that utilizes them, these signals should not assert.</td>
</tr>
<tr>
<td>$1 p _ { - }$</td>
<td>Optional Vendor Defined signals. See Section 10.3.4 for an example usage of these signals. If these signals are instantiated, but the UCIe stack is not operating in a mode that utilizes them, these signals should not assert.</td>
</tr>
</table>

Signals in Table 10-2 apply only when supporting MPM over sideband. The choice for whether these
signals run on the lclk or the Mgmt_Clk is implementation-specific.

<table>
<caption>Table 10-2. RDI Config interface extensions for Management Transport (Sheet 1 of 3)</caption>
<tr>
<th>Signal Name</th>
<th>Signal Description</th>
</tr>
<tr>
<td>pm_param_done</td>
<td>Management transport negotiation phase completed. Signal de-asserts after being asserted for two clocks. This signal asserts when MBINIT.PARAM management transport negotiation phase completes. Note that this signal is asserted even if MBINIT.PARAM Configuration or SBFE exchanges indicate no support for management transport in the partner chiplet.</td>
</tr>
<tr>
<td>pm_param_local_count [N-1 : 0]</td>
<td>Number of modules that successfully negotiated Management transport on transmit side. This field is sampled only when pm_param_done signal is asserted. $0 0 0 b : 0 \quad m o d u l e s$ 011b: 3 modules 001b: 1 module $1 0 0 b : 4 \quad m o d u l e s$ 010b: 2 modules Others: Reserved N=2 for 1, 2, or 3 modules scenarios, and N=3 for 4 modules scenario.</td>
</tr>
<tr>
<td>pm_param_remote_count [N- 1:0]</td>
<td>Number of modules that successfully negotiated Management transport on receive side. This field is sampled only when pm_param_done signal is asserted. 000b: 0 modules 011b: 3 modules 001b: 1 module 100b: 4 modules 010b: 2 modules Others: Reserved $N = 2 \text { for } 1 , 2 ,$</td>
</tr>
<tr>
<td>mp_mgmt_init_done</td>
<td>$I n d i c a t i o n \quad f r o m \quad M a n a g e m e n t \quad P o r t \quad G a t e w a y \quad t h a t \quad i n i t i a l i z a t i o n \quad p h a s e \quad c o m p l e t e d$ (successfully or unsuccessfully). machine state beyond MBINIT.PARAM, if other conditions allow. Signal de-asserts after being asserted for two clocks. The PHY should not depend on this signal for advancing the state machine when the management path is already up or when the partner chiplet indicated no support for management transport.</td>
</tr>
<tr>
<td>mp_mgmt_init_start</td>
<td>A two-clock trigger pulse from Management Port Gateway to PHY to start negotiation on the sideband links. Management Port Gateway must ensure that the mp_mgmt_up de-asserted when this signal is pulsed. This signal forces the link state machine $t o \quad R E S E T$ state (if it is not already there) and hence can bring the mainband link down $\lim k .$ The standard TRAINERROR flow applies here as well for transitioning signal is pulsed. to RESET if the state machine is not already in that state when this</td>
</tr>
<tr>
<td>mp_mgmt_up</td>
<td>Indication from Management Port Gateway that is signaled along with mp_mgmt_init_done, that Management Transport Initialization Phase completed successfully (mp_mgmt_up=1) or unsuccessfully (mp_mgmt_up=0). This is used by PHY to set the SB_MGMT_UP flag.</td>
</tr>
<tr>
<td>mp_mgmt_port_gateway_ready</td>
<td>Indication to PHY that Management Port Gateway is ready for management transport path initialization. The PHY uses this as one of the conditions to trigger or respond to a trigger for Management Transport path initialization. This asserts after the Management Port Gateway is ready for management path setup after Management Reset. Once asserted, this signal de-asserts on a Management Port Gateway reset (either because of management domain reset or after a heartbeat timeout or an 'Init Done' Timeout or any fatal error on sideband) condition.</td>
</tr>
<tr>
<td>mp_stall_after_mbinit_param</td>
<td>Management Port Gateway asserts this signal concurrent with asserting mp_mgmt_port_gateway_ready to indicate to the PHY that it must stall the training on the receive side using an {MBINIT.PARAM SBFE resp} sideband message stall encoding as described in Section 4.5.3.3.1.2. This signal remains asserted until the MPG determines that stalling is no longer necessary (i.e., that it is okay for link initialization to proceed). When de-asserted, the receive side training does not cause a "stall". When a sideband-only link is negotiated, this signal is not used by the PHY to determine the Link training state machine progress.</td>
</tr>
</table>

<table>
<caption>Table 10-2. RDI Config interface extensions for Management Transport (Sheet 2 of 3)</caption>
<tr>
<th>Signal Name</th>
<th>Signal Description</th>
</tr>
<tr>
<td>pm_cfg_credit [N-1: 0]</td>
<td>This is credit return for the Flow control buffers over RDI (see Section 8.2.5.1.1) used by the Management Port Gateway to transmit management packets to the remote Management Port Gateway. Each credit corresponds to 64 bits of buffer space. Physical Layer returns the credit once the corresponding transaction has been deallocated from its internal buffers. See Section 8.2.5.1.1 for additional flow control rules. Because the advertised credits are design parameters, the Management Port Gateway transmitter updates the credit counters with initial credits on Management reset exit or on 'Heartbeat timeout', and no initialization credits are returned over the interface for these conditions. Credit returns must follow the same rules of clock gating exit handshakes as the sideband packets to are dropped by the receiver of the credit returns. $\text { There is a signal per } R \times Q - I D$ in the design and hence N can be 1, 2, 3, or 4.</td>
</tr>
<tr>
<td>mp_rxqid [N-1 : 0]</td>
<td>$\begin{array}{} { \text { RxQ-ID associated with the message. Has meaning when men men men rignal is } } \\ { \text { asserted on a RDI transfer. Used by PHY to steer the packt to the corret SB link. } } \end{array}$ On encapsulated MTPs and PM Req messages, this carries the far-end Rx queue's RxQ- ID. On Credit return, Init Done and PM Ack messages this carries the RxQ-ID of the local $N \quad i s \quad e i t h e r \quad 2 \left( f o r \quad 4 \quad m o d u l e s \quad l i n k s \quad s c e n a r i o s \right) o r \quad 1 \left( 1 \quad o r \quad 2 \quad m o d u l e s \quad l i n k s \quad s c e n a r i o s \right) . T h e r e$ is a fixed mapping in the negotiation on the $\begin{array}{} { \text { transmit side. The chosen SB link a given Ror a ginen the must be onf the sine that } } \\ { \text { successfully trained for managent transport on the transmit side } } \end{array}$</td>
</tr>
<tr>
<td>$p m \_ r x q i d \left[ N - 1 : 0 \right]$</td>
<td>RxQ-ID associated with the message. Has meaning when pm_mgmt_pkt signal is asserted on a RDI transfer. Used by Management Port Gateway to internally steer the packet to the correct RxQ. N is either 2 (for 4 modules/sideband-only links scenarios) or 1 (1 or 2 modules/ sideband-only links scenarios). Valid for all MPM config bus transmissions. PHY uses the link to drive $t h e s e \quad s i g n a l s \quad o n \quad c o n f i g \quad i n t e r f a c e . T h e s e \quad s i g n a l s \quad a r e \quad u n d e f i n e d \quad f o r \quad S o C \quad C a p a b i l i t i e s$</td>
</tr>
<tr>
<td>mp_wake_req</td>
<td>Request from the Management Port Gateway to remove clock gating from the internal logic of the Physical Layer that handles management transport traffic. This is an asynchronous signal from the Physical Layer's perspective since it is not tied to Iclk being available in the Physical Layer. Together with pm_wake_ack, it forms a four-way handshake to enable dynamic clock gating in the Physical Layer for logic that handles management transport traffic. This handshake is independent of any RDI state-related clock gating rules. When dynamic clock gating is supported, the Physical Layer must use this signal to exit clock gating before responding with pm_wake_ack. If dynamic clock gating is not supported, Management Port Gateway must tie this signal to 1.</td>
</tr>
<tr>
<td>pm_wake_ack</td>
<td>Response from the Physical Layer to the Management Port Gateway acknowledging that its clocks have been ungated in response to mp_wake_req. This signal is only asserted asserted. after mp_wake_req has asserted, and is de-asserted after mp_wake_req has de- When dynamic clock gating is not supported by the Physical Layer, it must stage mp_wake_req internally for one or more clock cycles and turn it around as pm_wake_ack. This way it will still participate in the handshake even though it does not support dynamic clock gating.</td>
</tr>
<tr>
<td>$\mathrm { p m } _ { - } \mathrm { c l k } _ { - } \mathrm { r e q }$</td>
<td>Request from the Physical Layer to remove clock gating from the internal logic of the Management Port Gateway. This is an asynchronous signal relative to lclk/Mgmt_clk from the Management Port Gateway perspective because it is not tied to 1clk/ Mgmt_clk being available in the Management Port Gateway. This handshake is independent of any RDI state-related clock gating rules. Together with mp_clk_ack, it forms a four-way handshake to enable dynamic clock gating in the Management Port Gateway. When dynamic clock gating is supported, the Management Port Gateway must use this signal to exit clock gating before responding $\begin{array}{} { \text { with mp } - c 1 k } \\ { \text { siqnal to } 1 } \end{array} .$ If dynamic clock gating is not supported, Physical Layer must tie this</td>
</tr>
</table>

<table>
<caption>Table 10-2. RDI Config interface extensions for Management Transport (Sheet 3 of 3)</caption>
<tr>
<th>Signal Name</th>
<th>Signal Description</th>
</tr>
<tr>
<td>mp_clk_ack</td>
<td>Response from the Management Port Gateway to the PHY acknowledging that its clocks have been ungated in response to pm_clk_req. This signal is asserted only when pm_clk_req is asserted, and de-asserted after pm_clk_req has de-asserted. When dynamic clock gating is not supported by the Management Port Gateway, it must stage pm_clk_req internally for one or more clock cycles and turn it around as mp_clk_ack. This way it will still participate in the handshake even though it does not support dynamic clock gating. When supporting dynamic clock gating of the Management Port Gateway, PHY must ensure that pulsed signals (e.g., pm_param_done), are delivered only after the mp_clk_ack is set to ensure that the Management Port Gateway saw those pulses.</td>
</tr>
<tr>
<td>mp_mgmt_pkt</td>
<td>During a valid RDI data transfer to PHY, this signal indicates whether the transfer is for an MPM. 0: Link management packet. 1: MPM. Used by PHY to steer the packet to the correct RDI credit buffer.</td>
</tr>
<tr>
<td>pm_mgmt_pkt</td>
<td>During a valid RDI data transfer from PHY, this signal indicates whether the transfer is for an MPM. 0: Link management packet. D2D Adapter. 1: MPM. Used by the Management Port Gateway to steer the packet to RxQ buffers or to</td>
</tr>
<tr>
<td>pm_so</td>
<td>When asserted, indicates to Management Port Gateway that SO mode was negotiated. On ports that have sideband-only link physically present, this can be tied off to 1.</td>
</tr>
<tr>
<td>Mgmt_clk</td>
<td>Optional clock used for the Configuration interface on the RDI for implementations in which the main RDI clock is not available for Management Transport path initialization.</td>
</tr>
<tr>
<td>pm_fatal_error</td>
<td>Set by any sideband link fatal error indication, such as parity error on a sideband packet. Cleared by a Management Reset.</td>
</tr>
<tr>
<td>mp_fatal_error</td>
<td>Used by Management Port Gateway to instruct the PHY to transition to TRAINERROR state. This is a two-clock pulse.</td>
</tr>
</table>

### 10.1.1 Interface reset requirements

RDI does not define a separate interface signal for reset; however, it is required that the logic entities
on both sides of RDI are in the same reset domain and the reset for each side is derived from the
same source. Because reset may be staggered due to SoC routing, all signals coming out of reset
must be driven to 0, unless otherwise specified.

### 10.1.2 Interface clocking requirements

RDI requires both sides of the interface to be on the same clock domain. The sideband interface
includes the pl_cfg, pl_cfg_vld, pl_cfg_crd, lp_cfg, lp_cfg_vld, and lp_cfg_crd signals.
If Management Transport is not supported over sideband, all signals are synchronous to lclk. When
Management Transport is supported, the sideband interface as well as the signals in Table 10-2 are
permitted to be on a separate Mgmt_clk domain. For example, this Mgmt_clk can be the auxiliary
clock so that the management transport is available over the sideband even if the clocks required for
the mainband and for lclk are unavailable.

Each side is permitted to internally instantiate clock-crossing FIFOs if needed, as long as it does not
violate the requirements at the interface itself.

It is important to note that back pressure is not possible from the Adapter to the Physical Layer on the
main data path. So any clock-crossing-related logic internal to the Adapter must take this into
consideration.

For example, for a 64-Lane module with a maximum speed of 16 $\mathrm { G T } / \mathrm { s } ,$ the RDI could be 64B wide
running at 2 GHz to be exactly bandwidth matched.

### 10.1.3 Dynamic clock gating

Dynamic coarse clock gating is permitted in the Adapter and Physical Layer when pl_state_sts is
Reset, LinkReset, Disabled, or PM. This section defines the rules around entry and exit of clock gating.
Note that clock gating is not permitted in LinkError state; it is expected that for UCIe usages, error
handlers will be enabled to make sure the Link is not stuck in LinkError state if the intent is save
power for Links in error state.

### 10.1.3.1 Rules and description for lp_wake_req/pl_wake_ack handshake

Adapter can request removal of clock gating of the Physical Layer by asserting lp_wake_req
(asynchronous to lclk availability in the Physical Layer). All Physical Layer implementations must
respond with a pl_wake_ack (synchronous to lclk). The extent of internal clock ungating when
pl_wake_ack is asserted is implementation-specific, but lclk must be available by this time to
enable RDI signal transitions from the Adapters. The Wake Req/Ack is a full handshake and it must be
used for state transition requests (on lp_state_req or lp_linkerror) when moving away from a
state in which clock gating is permitted. It must also be used for sending packets on the sideband
interface.

Rules for this handshake:

1\. Adapter asserts lp_wake_req to request ungating of clocks by the Physical Layer.

2\. The Physical Layer asserts pl_wake_ack to indicate that clock gating has been removed. There
must be at least one clock cycle bubble between lp_wake_req assertion and pl_wake_ack
assertion.

3\. lp_wake_req must de-assert before pl_wake_ack de-asserts. It is the responsibility of the
Adapter to control the specific scenario of de-assertion. As an example, when performing the
handshake for a state request, it is permitted to keep lp_wake_req asserted until it observes the
desired state status. Adapter is also permitted to keep lp_wake_req asserted through states
where clock gating is not permitted in the Physical Layer (i.e., Active, LinkError, or Retrain).

4\. lp_wake_req should not be the only consideration for Physical Layer to perform clock gating, it
must take into account pl_state_sts and other internal or Link requirements before performing
global and/or local clock gating.

5\. When performing lp_wake_req/pl_wake_ack handshake for lp_state_req transitions or
lp_linkerror transition, the Adapter is permitted to not wait for pl_wake_ack before
changing lp_state_req or lp_linkerror.

6\. When performing lp_wake_req/pl_wake_ack handshake for lp_cfg transitions, Adapter must
wait for pl_wake_ack before changing lp_cfg or lp_cfg_vld. Because lp_cfg can have
multiple transitions for a single packet transfer, it is necessary to make sure that the Physical
Layer clocks are up before transfer begins.

### 10.1.3.2 Rules and description for pl_clk_req/lp_clk_ack handshake

Physical Layer is permitted to initiate pl_clk_req/lp_clk_ack handshake at any time and the
Adapter must respond.

Rules for this handshake:

1\. Physical Layer asserts pl_clk_req to request removal of clock gating by the Adapter. This can
be done anytime, and independent of current RDI state.

2\. The Adapter asserts lp_clk_ack to indicate that clock gating has been removed. There must be
at least one clock cycle bubble between pl_clk_req assertion and lp_clk_ack assertion.

3\. pl_clk_req must de-assert before lp_clk_ack. It is the responsibility of the Physical Layer to
control the specific scenario of de-assertion, after the required actions for this handshake are
completed.

4\. pl_clk_req should not be the only consideration for the Adapter to perform clock gating, it must
take into account pl_state_sts and other protocol-specific requirements before performing
trunk and/or local clock gating.

5\. The Physical Layer must use this handshake to ensure transitions of pl_inband_pres have been
observed by the Adapter. Because pl_inband_pres is a level-oriented signal (once asserted,
pl_inband_pres remains asserted during the lifetime of Link operation), the Physical Layer is
permitted to let pl_inband pres transition without waiting for 1p_clk_ack. When this is done
during initial Link bring up, it is strongly recommended for the Physical Layer to keep
pl_clk_req asserted until the state status transitions away from Reset to a state where clock
gating is not permitted. It is permitted for pl_inband_pres to assert before OR after
pl_clk_req asserts; however, pl_inband_pres assertion is not guaranteed to be observed by
the Adapter until the pl_clk_req/lp_clk_ack handshake is complete.

<figure>
<figcaption>Figure 10-2. Example Waveform Showing Handling of Level Transition</figcaption>

0

1

2

3

4

5

6

7

8

9

10

11

12

13

14

15

lclk

pl_clk_req

lp_clk_ack

11

pl_inband_pres

</figure>

6\. The Physical Layer must also perform this handshake before transition to LinkError state from
Reset or PM state (when the LinkError transition occurs by the Physical Layer without being
directed by the Adapter). It is permitted to assert pl_clk_req before the state change, in which
case it must stay asserted until the state status transitions. It is also permitted to assert
pl_clk_req after the state status transition, but in this case Physical Layer must wait for
lp_clk_ack before performing another state transition.

7\. The Physical Layer must also perform this handshake when the status is PM and remote Link
partner is requesting PM exit. For exit from Reset or PM states to a state that is not LinkError, it is
required to assert pl_clk_req before the status change, and in this case it must stay asserted until
the state status transitions away from Reset or PM.

8\. When clock-gated in RESET states, Adapters that rely on dynamic clock gating to save power
must wait in clock gated state for pl_inband_pres=1. The Physical Layer will request clock
gating exit when it transitions pl_inband_pres, and the Adapter must wait for
pl_inband_pres assertion before requesting lp_state_req = ACTIVE. If pl_inband_pres
de-asserts while pl_state_sts = RESET, then the Adapter is permitted to return to clock-gated
state after moving lp_state_req to NOP.

9\. Physical Layer must also perform this handshake for sideband traffic to Adapter. When performing
the handshake for pl_cfg transitions, Physical Layer must wait for lp_clk_ack before changing
pl_cfg or pl_cfg_vld. Because pl_cfg can have multiple transitions for a single packet
transfer, it is necessary to make sure that the Adapter clocks are up before transfer begins.

# 10.1.4 Data Transfer

As indicated in the signal list descriptions, when Adapter is sending data to the Physical Layer, data is
transferred when lp_irdy, pl_trdy, and lp_valid are asserted. Figure 10-3 shows an example
waveform for data transfer from the Adapter to the Physical Layer. Data is transmitted on clock cycles
1, 2, and 5. No assumption should be made by Adapter about when pl_trdy can de-assert or for
how many cycles it remains de-asserted before it is asserted again, unless explicitly guaranteed by
the Physical Layer. If a Flit transfer takes multiple clock cycles, the Adapter is not permitted to insert
bubbles in the middle of a Flit transfer. This means that lp_valid and lp_irdy must be asserted
continuously until the Flit transfer is complete. Of course, data transfer can stall because of pl_trdy
de-assertion.

<figure>
<figcaption>Figure 10-3. Data Transfer from Adapter to Physical Layer</figcaption>

0

1

2

3

4

5

6

clk

$\mathrm { l p } _ { - } \mathrm { i r d y }$

lp_data

Dat0

Dat1

Dat2

lp_valid

pl_trdy

</figure>

As indicated in the signal list descriptions, when the Physical Layer is sending data to the Adapter,
there is no backpressure mechanism, and data is transferred whenever pl_valid is asserted. The
Physical Layer is permitted to insert bubbles in the middle of a Flit transfer and the Adapter must be
able to handle that.

## IMPLEMENTATION NOTE

For the transmit side of the Physical Layer for data sent over the UCIe Link, it must
ensure that if the Adapter has a continuous stream of packets to transmit (lp_irdy
and lp_valid do not de-assert), it does not insert bubbles in valid frames on the
Physical Link.

For the Runtime Link Testing feature with parity insertion, the Adapter as a receiver of
parity bytes is permitted to issue a {ParityFeature.Nak} if software sets up a number
of parity byte insertions ("Number of 64 Byte Inserts" field in the "Error and Link
Testing Control" register) that does not amount to 256B or a multiple of the RDI width
(to save the implementation cost of barrel shifting the parity bytes). For example, if
the RDI width is 64B then either 64B, 128B, or 256B of inserted parity bytes are okay,
but if the RDI width is 256B or larger, then it is better to always have 256B of inserted
parity bytes so that it matches the data transfer granularity of Flits.

# IMPLEMENTATION NOTE

It is permitted to use lp_irdy as an early indication that the valid data will be
resuming imminently, and the Physical Layer needs to ungate clocks and assert
pl_trdy when it is ready to receive data. A couple of examples are shown in
Figure 10-4 and Figure 10-5. Note that pl_trdy could have asserted as early as
Clock Cycle 1 in Figure 10-4.

<figure>
<figcaption>Figure 10-4. lp_irdy asserting two cycles before lp_valid</figcaption>

0

1

2

3

4

5

6

clk

Ip_irdy

Ip_data

Dat0

Dat1

Ip_valid

pl_trdy

</figure>

<figure>
<figcaption>Figure 10-5. lp_irdy asserting at the same cycle as lp_valid</figcaption>

0

1

2

3

4

5

6

clk

Ip_irdy

Ip_data

Dat0

Dat1

Ip_valid

pl_trdy

</figure>

## 10.1.5 RDI State Machine

<figure>
<figcaption>Figure 10-6 shows the RDI state machine. Figure 10-6. RDI State Machine</figcaption>

Domain Reset Exit

Link Error

From Any State

Reset

Disabled

From Any State
(except LinkError)

L2

LinkReset

Active

From Any State
(except Disabled and
LinkError)

PMNAK

L1

Retrain

</figure>

## 10.1.6 RDI bring up flow

Figure 10-7 shows an example flow for Stage 2 of the Link bring up highlighting the transitions on
RDI. This stage requires sequencing on RDI that coordinates the state transition from Reset to Active.

1\. Once Physical Layer has completed Link training, it must do the pl_clk_req handshake with the
Adapter and reflect pl_inband_pres=1 on RDI. Note that the pl_clk_req handshake is not
shown in the example flow in Figure 10-7

2\. Observing pl_inband_pres=1 is the trigger for Adapter to request Active state. It must perform
the lp_wake_req handshake as described in Section 10.1.3. Note that the lp_wake_req
handshake is not shown in the example flow in Figure 10-7.

3\. Only after sampling 1p_state_req $\mathrm { r e q } = \mathrm { A c t i v e } ,$ the Physical Layer must send the
{LinkMgmt.RDI.Req.Active} sideband message to remote Link partner's Physical Layer.

4\. The Physical Layer must respond to the {LinkMgmt.RDI.Req.Active} sideband message with a
{LinkMgmt.RDI.Rsp.Active} sideband message. The {LinkMgmt.RDI.Rsp.Active} sideband
message must only be sent after the Physical Layer has sampled lp_state_req = Active from
its local RDI.

5\. Once the Physical Layer has sent and received the {LinkMgmt.RDI.Rsp.Active} sideband
message, it must transition pl_state_sts to Active.

6\. This opens up the Adapter to transition to Stage 3 of the bring up flow.

Steps 3 to 5 are referred to as the "Active Entry handshake" and must be performed for every entry
to Active state. Active.PMNAK to Active transition is not considered here because Active.PMNAK is
only a sub-state of Active.

<figure>
<figcaption>Figure 10-7. Example flow of Link bring up on RDI</figcaption>

Adapter
Die 0

Physical Layer
$D i e \quad 0$

CHANNEL

Physical Layer
$D i e \quad 1$

Adapter
Die 1

Reset flow for Die 0
(independent of Die 1)
Stage 0

Reset flow for Die 1
(independent of Die 0)
Stage 0

$p l \_ s t a t e \_ s t s = R e s e t$

pl_state_sts = Reset

Sideband initialization
Stage 1

Training parameter exchanges on sideband and
Mainband (Repair and) Training
Stage 2 Start

Adapter exits clock gating, gives
Active request once it is ready to
receive and send protocol
parameter exchanges

$p l \_ i n b a n d \_ p r e s = 0 - > 1$

pl_inband_pres = 0->1

Adapter exits clock gating, gives
Active request once it is ready to
receive and send protocol
parameter exchanges

Ip_state_req=Active

lp_state_req=Active

SB MSG {LinkMgmt.RDI.Req.Active}
SB MSG {LinkMgmt.RDI.Rsp.Active}
I

SB MSG {LinkMgmt.RDI.Req.Active}
$- S B \quad M S G L i n k M g m t . R D I . R s p . A c t i v e$

pl_state_sts $= A c t i v e$

$p l \_ s t a t e \_ s t s = A c t i v e$

Either side can start
the SB exchange

Physical Layer returns
pl_state_sts = Active once it
$h a s \quad s e n t \quad a n d \quad r e c e i v e d \quad a n$
"Active Status" SB MSG

Physical Layer returns
$p l \_ s t a t e \_ s t s = A c t i v e \quad o n c e$ it
has sent and received an
"Active Status" SB MSG

Stage 2 Complete

</figure>

### 10.1.7 RDI PM flow

This section defines the rules for PM entry, exit and abort flows as they apply to handshakes on the
RDI. The rules for L1 and L2 are the same, except that exit from L2 is to Reset state, whereas exit
from L1 is to Retrain state. This section uses PM to denote L1 or L2. A "PM Request" sideband
message is {LinkMgmt.RDI.Req.L1} or {LinkMgmt.RDI.Req.L2}. A "PM Response" sideband message
is {LinkMgmt.RDI.Rsp.L1} or {LinkMgmt.RDI.Rsp.L2}.

. Regardless of protocol, the PM entry or exit flow is symmetric on RDI. Both Physical Layer must
issue PM entry request through a sideband message once the conditions of PM entry have been
satisfied. PM entry is considered successful and complete once both sides have received a valid
"PM Response" sideband message. Figure 10-8 shows an example flow for L1. Once the RDI
status is PM, the Physical Layer can transition itself to a power savings state (turning off the PLL
for example). Note that the sideband logic and corresponding PLL needs to stay on even during L1
state.

. All the Adapter state machines (Adapter LSMs) in the Adapter must have moved to the
corresponding PM state before the Adapter requests PM entry from remote Link partner. Adapter
LSM in PM implies the retry buffer of the Adapter must be empty, and it must not have any new
Flits (or Ack/Nak) pending to be scheduled. Essentially there should be no traffic on mainband
when PM entry is requested by the Adapter to the Physical Layer. The Adapter is permitted to
clock gate its sideband logic once RDI status is PM and there are no outstanding transactions or
responses on sideband. Physical Layer must do pl_clk_req handshake (if pl_clk_req is not
already asserted or status is not Active) before forwarding sideband requests from the Link to the
Adapter.

· Adapter requests PM entry by transitioning 1p_state_req to the corresponding PM encoding.
Once requested, the Adapter cannot change this request until it observes PM, Active. PMNAK,
Retrain, or LinkError state on pl_state_sts. While requesting PM state, if the Adapter receives
Active request from the Protocol Layer, or a PM exit request for the Adapter LSM on sideband, it
must sink the message but delay processing it until pl_state_sts has resolved. Once the RDI
state is resolved, the Adapter must first bring it back to Active before processing the other
requests.

\- If the resolution is PM (upon successful PM entry) and the Protocol Layer needs to exit PM (or
there is a pending Protocol Layer Active request from remote Link partner), then the Adapter
must initiate PM exit flow on RDI by requesting lp_state_req = Active. All PM entry-related
handshakes must have finished prior to this (this is when the Physical Layer on both sides of
the Link have received a valid "PM Response" sideband message).

\- If the resolution is Active. PMNAK, the Adapter must initiate a request of Active on RDI. Once
the status moves to Active, the Adapter is permitted to re-request PM entry (if all conditions
of PM entry are still met). Figure 10-9 shows an example of PM abort flow. The PM request
could have been from either side.

\- If the resolution is LinkError, then the Adapter must propagate this to Protocol Layers. This
also resets any outstanding PM handshakes.

· Physical Layer initiates a "PM Request" sideband message once it samples the corresponding PM
encoding on lp_state_req and has completed the StallReq/Ack handshake with its Adapter.

. Once a Physical Layer receives a "PM request" sideband message, it must respond to it within 2
us:

\- If its local Adapter is requesting the corresponding PM state, it must respond with the
corresponding "PM Response" sideband message. If the current status is not PM, it must
transition pl_state_sts to PM after responding to the sideband message.

\- If the current pl_state_sts = PM, it must respond with "PM Response" sideband message.

\- If pl_state_sts = Active and 1p_state_req = Active and it remains this way for 1us after
receiving the "PM Request" sideband message, it must respond with
{LinkMgmt.RDI.Rsp.PMNAK} sideband message.

· If a Physical Layer receives a "PM Response" sideband message in response to a "PM Request"
sideband message, it must transition pl_state_sts on its local RDI to PM (if it is currently in
Active state). If the current state is not Active, no action needs to be taken.

· If a Physical Layer receives a {LinkMgmt.RDI.Rsp.PMNAK} sideband message in response to a
"PM Request" sideband message, it must transition pl_state_sts on its local RDI to
Active.PMNAK state if it is currently in Active state. If it is not in Active state, no action needs to
be taken. The Physical Layer is permitted to retry PM entry handshake (if all conditions of PM
entry are satisfied) at least 2 us after receiving the {LinkMgmt.RDI.Rsp.PMNAK} sideband
message OR if it received a corresponding "PM Request" sideband message from the remote Link
partner.

· PM exit is initiated by the Adapter requesting Active on RDI. This triggers the Physical Layer to
initiate PM exit by sending a {LinkMgmt.RDI.Req.Active} sideband message. Physical Layer must
make sure it has finished any Link retraining steps before it responds with the
{LinkMgmt.RDI.Rsp.Active} sideband message. Figure 10-10 shows an example flow of PM exit
on RDI.

\- PM exit handshake completion requires both Physical Layers to send as well as receive a
{LinkMgmt.RDI.Rsp.Active} sideband message. Once this has completed, the Physical Layer
is permitted to transition pl_state_sts to Active on RDI.

\- If pl_state_sts = PM and a {LinkMgmt.RDI.Req.Active} sideband message is received, the
Physical Layer must initiate pl_clk_req handshake with the Adapter, and transition
pl_state_sts to Retrain. This must trigger the Adapter to request Active on
lp_state_req (if not already doing so), and this in turn triggers the Physical Layer to send
{LinkMgmt.RDI.Req.Active} sideband message to the remote Link partner. Figure 10-11
shows an example of the L1 exit flow on RDI and its interaction with the LTSM in the Physical
Layer. It is permitted for the LTSM to begin the Link PM exit and retraining flow when a
{LinkMgmt.RDI.Req.Active} sideband message is received or when the Adapter requests
Active on RDI. The timeout counters for the Active Request sideband message handshake
must begin only after LTSM is in the LINKINIT state. L2 exit follows a similar flow for cases in
which graceful exit is required without domain reset; however, the L2 exit is via Reset state
on RDI, and not Retrain. Exit conditions from Reset state apply for L2 exit (i.e., a NOP ->
Active transition is required on lp_state_req for the Physical Layer to exit Reset state on
RDI).

Note that the following figures are examples for L1, and do not show the lp_wake_req,
pl_clk_req handshakes. Implementations must follow the rules outlined for these handshakes in
previous sections.

<figure>
<figcaption>Figure 10-8. Successful PM entry flow</figcaption>

Adapter
$\mathrm { D i e } 0$

Physical layer
Die 0

CHANNEL

Physical layer
Die 1

Adapter
Die 1

$p l \_ s t a t e \_ s t s = A c t i v e$

$p l \_ s t a t e \_ s t s = A c t i v e$

Adapter ensures all Adapter
LSMs have moved to PM
state before requesting PM

$\mathrm { l p } \_ \mathrm { s t a t e } \_ \mathrm { r e q } = \mathrm { L }$

Adapter ensures all Adapter
LSMs have moved to PM
state before requesting PM

SB MSG {LinkMgmt.RDI.Req.L1}

Physical Layer must wait for
1us to see if Adapter
requests PM

lp_state_req=L1

SB MSG {LinkMgmt.RDI.Req.L1}
SB MSG {LinkMgmt.RDI.Rsp.L1}

pl_state_sts = PM-

SB MSG {LinkMgmt.RDI.Rsp.L1}

$\mathrm { s t a t e } _ { - } s t s$ = PM-

</figure>

<figure>
<figcaption>Figure 10-9. PM Abort flow</figcaption>

Adapter
Die 0

$\begin{array}{} { \text { Physical layer } } \\ { \text { Die } 0 } \end{array}$

CHANNEL

Physical layer
Die 1

Adapter
Die 1

pl_state_sts $= A c t i v e$

pl_state_sts $= A c t i v e$

lp_state_req=Active

lp_state_req=L1

SB MSG {LinkMgmt.RDI.Req.L1}

Physical Layer must wait for
1us to see if Adapter
requests PM

Adapter must continue to
receive (but not process)
sideband packets that may
request PM exit for Adapter
LSM.

SB MSG {LinkMgmt.RDI.Rs p.PM NAK}-

pl_state_sts = Active. PM NAK

$l p \_ s t a t e \_ r e q = A c t i v e$
$p l \_ s t a t e \_ s t s = A c t i v e$

Adapter can retry PM entry
2us after receiving PMNAK,
if all conditions of PM entry
are still met. This is also the
$p o i n t \quad a f t e r \quad w h i c h \quad a n y$
pending sideband requests
for PM exit of protocol layer
can be processed.

</figure>

<figure>
<figcaption>Figure 10-10. PM Exit flow</figcaption>

Adapter
Die 0

Physical layer
$D i e \quad 0$

CHANNEL

Physical layer
Die 1

Adapter
Die 1

$p l \_ s t a t e \_ s t s = L 1$

pl_state_sts =L1

$\mathrm { l p } _ { - } \mathrm { s t a t e } _ { - } \mathrm { r e q } = \mathrm { A } \mathrm { c t i v e }$

SB MSG {LinkMgmt. RDI.Req.Active}-

SB MSG {LinkMgmt.RDI.Rsp.Active}

pl_state_sts = Retrain

lp_state_req=Active

SB MSG {LinkMgmt.RDI.Req.Active}

$p l \_ s t a t e \_ s t s = R e t r a i n$

SB MSG $\left. \mathrm { R s p } . \mathrm { A c t i v e } \right\}$

pl_state_sts = Active

$p | _ { - } s \text { tate } _ { - } s t s = A c t i v e$

</figure>

<figure>
<figcaption>Figure 10-11. RDI PM Exit Example Showing Interactions with LTSM</figcaption>

Adapter
Die 0

Physical Layer
Die 0

CHANNEL

Physical Layer
Die 1

Adapter
Die 1

pl_state_sts = L1

pl_state_sts =L1

$1 p _ { - } s \text { tate } _ { - } r e q = A c t i v e$

SB MSG {LinkMgmt.RDI.Req.Active}

$p l \_ s t a t e \_ s t s = R e t r a i n$

lp_state_req=Active

SB MSG {LinkMgmt.RDI.Req.Active}

$p l \_ s t a t e \_ s t s = R e t r a i n$

LTSM is in LINKINIT

LTSM is in LINKINIT

RDI. Rs p.Active }

SB MSG {LinkMgmt.RDI.Rsp.Active}

LTSM is in Active

LTSM is in Active

pl_state_sts = Active

pl_state_sts = Active

☐
LTSM performs L1 exit-related Link Training

</figure>

## 10.2 Flit-Aware Die-to-Die Interface (FDI)

This section defines the signal descriptions and functionality associated with a single instance of Flit-
Aware Die-to-Die Interface (FDI). A single instance is used for a Protocol Layer to Adapter $\begin{array}{} { \text { er connection } } \\ { \text { FDI } } \end{array} .$
However, a single Adapter can host multiple protocol stacks using multiple instances of
Figure 10-12 shows example configurations using multiple instances of FDI.

<figure>
<figcaption>Figure 10-12. Example configurations using FDI</figcaption>

Protocol Layer

$P r o t o c o l \quad L a y e r$
$\left( \alpha _ { L . i o } \right)$

Protocol Layer
(CXL.cachemem)

FDI

$F D I$

Arb/Mux
Die-to-Die Adapter

Die-to-Die Adapter

RDI

RDI

(a) Single Protocol

(b) Single CXL stack

Protocol Layer

Protocol Layer

Protocol Layer
$\left( \alpha _ { L . i o } \right)$

Protocol Layer
$\left( \mathrm { c u l } . . \mathrm { c a c h e m e m } \right)$

Protocol Layer
$\left( C \alpha L i o \right)$

Protocol Layer
$\left( \mathrm { c x L } . \mathrm { c a c h e m e m } \right)$

$F D I$

FDI

Stack Mux
Die-to-Die Adapter

$\mathrm { A r b / M u x }$

Arb/Mux

Stack Mux

RDI

Die-to-Die Adapter

RDI

(c) Two Protocol Stacks

(d) Two CXL stacks multiplexed inside the adapter

</figure>

Table 10-3 lists the FDI signals and their descriptions. In Table 10-3:

. pl _* indicates that the signal is driven away from the Die-to-Die Adapter to the Protocol Layer.

· lp _* indicates that the signal is driven away from the Protocol Layer to the Die-to-Die Adapter.

Note:
The same signal-naming convention as RDI is used to highlight that RDI signal list is a
proper subset of FDI signal list.

Signal encodings pertaining to 'Management Transport protocol' are applicable only when
Management Transport protocol was successfully negotiated on the mainband. Otherwise, those
encodings are reserved. Also, dm * signals in Table 10-3 are applicable only when supporting
Management Transport path over the mainband ("dm" is an abbreviation for "d2d_adapter-to-
management_port_gateway").

<table>
<caption>Table 10-3. FDI signal list (Sheet 1 of 7)</caption>
<tr>
<th>Signal Name</th>
<th>Signal Description</th>
</tr>
<tr>
<td>lclk</td>
<td>$T h e \quad c l o c k \quad a t \quad w h i c h \quad F D I \quad o p e r a t e s .$</td>
</tr>
<tr>
<td>$l p \_ i r d y$</td>
<td>Signal indicating that the Protocol Layer potentially has data to send. This must be asserted if lp_valid is asserted and the Protocol Layer wants the Adapter to sample the data. $l p \_ i r d y \quad m u s t \quad n o t \quad b e$ presented by the Protocol Layer when pl_state_sts is Reset status transitions from LinkError to Reset. On a LinkError to Reset transition, it is permitted for lp_irdy to be asserted for a few clocks but it must be de- asserted eventually. Physical Layer must ignore 1p_irdy when status is Reset.</td>
</tr>
<tr>
<td>lp_valid</td>
<td>Protocol Layer to Adapter indication that data is valid on the corresponding lp_data bytes.</td>
</tr>
<tr>
<td>$l p \_ d a t a \left[ N B Y T E S - 1 : 0 \right] \left[ 7 : 0 \right]$</td>
<td>$\begin{array}{} { \text { Protocol Layer to Adapter data, where } } \\ { \text { the data width for the FDI instance. } } \end{array}$ 'NBYTES' equals number of bytes determined by</td>
</tr>
<tr>
<td>lp_retimer_crd</td>
<td>When asserted at a rising clock edge, it indicates a single credit return for the Retimer Receiver buffer. Each credit corresponds to 256B of mainband data (including Flit header and CRC, etc.). This signal must NOT assert if a Retimer is not present. On FDI, this is an optional signal. It is permitted to have the Receiver buffers in the Protocol Layer for Raw Format only. If this is not exposed to Protocol Layer, Adapter must track credit at 256B granularity even for Raw Format and return credits to Physical Layer on RDI. When this is exposed on FDI, the Adapter must have the initial credits knowledge through other implementation specific means in order to advertise this to the remote Link partner during parameter exchanges.</td>
</tr>
<tr>
<td>lp_corrupt_crc</td>
<td>$\begin{array}{} { \left. \text { This signal is only applicable for CXL.crhemem in UCIe Flit Mode \left(i.e., the Adapter doingter } \right) } \\ { \text { Retry\right) for } C M L 2 5 6 B \text { Fit Mode. Tis Isment as a latenchornons thorhothors } } \end{array}$ detection and containment for viral or poison using the Adapter to corrupt CRC of outgoing Flit. It is recommended to corrupt CRC by performing a bitwise XOR of the computed CRC with the syndrome 138Eh. The syndrome was computed such that no 1- bit or 2-bit errors alias to this syndrome, and it has the least probability of aliasing with 3-bit errors. For Standard 256B Flits, Protocol Layer asserts this along with lp_valid for the last chunk of the Flit that needs containment. Adapter corrupts CRC for both of the 128B halves of the Flit which had this set. It also must make sure to overwrite this flit (with the next flit sent by the Protocol Layer) in the Tx Retry buffer. $\begin{array}{} { \text { For Latency-Optimized } 2 5 6 B \text { Flits } } \\ { \text { the last chunk of the } 1 2 8 B \text { Flit } h } \end{array} ,$ Protocol Layer asserts this along with lp_valid for that needs containment. If 1p_corrupt_crc is asserted on the first 128B half of the Flit, Protocol Layer must assert it on the second 128B half of the Flit as well. The very next Flit from the Protocol Layer after this signal must carry the information relevant for viral, as defined in the CXL $s p e c i f i c a t i o n . I f \quad t h i s$ was asserted on the second 128B half of the Flit only, it is the Protocol Layer to send the first 128B half exactly as before, and $\begin{array}{} { \text { insert the viral information in the se } } \\ { 1 2 8 B \text { half of the Flit which had this } } \end{array}$ second half of the Flit. Adapter corrupts CRC for the set. It also must make sure to overwrite this flit (with Layer) in the Tx Retry buffer.</td>
</tr>
<tr>
<td>$1 p _ { - } d 1 1 p \left[ \text { NDLLP-1 } : 0 \right]$</td>
<td>Protocol Layer to Adapter transfer of DLLP bytes. This is not used for 68B Flit Mode, CXL.cachemem or Streaming protocols. For a 64B data path on Ip_data, it is recommended to assign NDLLP &gt;= 8, so that 1 DLLP per Flit can be transferred from the Protocol Layer to the Adapter on average. The Adapter is responsible for inserting DLLP into DLP bytes 2:5 if the Flit packing rules permit it. See Section 10.2.4.1 for additional rules.</td>
</tr>
<tr>
<td>$1 p _ { - } d 1 1 p _ { - } v a l i d$</td>
<td>$\begin{array}{} { \text { Indicates valid DLLP transfer on } 1 p \text { d11p. DLLP. transfers art subt subject to } } \\ { \text { oackpressure by p1 trady the Adapter must have storage for different types of DLLP } } \end{array}$ and this can be overwritten so that the latest DLLPs are sent to remote Link partner). DLLP transfers are subject to backpressure by pl_stallreq - Protocol Layer must stop DLLP transfers at DLLP Flit aligned boundary before giving p_stallack or requesting PM.</td>
</tr>
<tr>
<td>$1 p _ { - } d 1 1 p _ { - } o f c$</td>
<td>Indicates that the corresponding DLLP bytes on lp_dllp follow the Optimized_Update_FC format. It must stay asserted for the entire duration of the DLLP transfer on lp_dllp.</td>
</tr>
</table>

<table>
<caption>Table 10-3. FDI signal list (Sheet 2 of 7)</caption>
<tr>
<th>Signal Name</th>
<th>Signal Description</th>
</tr>
<tr>
<td rowspan="2">$l p \_ s t r e a m \left[ 7 : 0 \right]$</td>
<td>Protocol Layer to Adapter signal that indicates the stream ID to use with data. Each stream ID maps to a unique protocol and stack. It is relevant only when 1p_valid is 1. 00h: Reserved 11h: Stack 1: PCIe</td>
</tr>
<tr>
<td>01h: Stack 0: PCIe 12h: Stack 1: CXL.io 02h: $S t a c k \quad 0 :$ CXL.io 13h: Stack 1: CXL.cachemem 03h: Stack 0: CXL.cachemem 14h: Stack 1: Streaming protocol 04h: Stack 0: Streaming protocol 15h: Stack 1: Management Transport 05h: Stack 0: Management Transport protocol protocol Other encodings are Reserved.</td>
</tr>
<tr>
<td>pl_trdy</td>
<td>The Adapter is ready to accept data. Data is accepted by the Adapter when pl_trdy, lp_valid, and lp_irdy are asserted at the rising edge of lclk. This signal must be asserted only if pl_state_sts is Active or when performing the $\frac { p 1 } { \left. \text { Section } 1 0 . 3 . 3 . 7 \right) }$ handshake when the pl_state_sts is LinkError (see</td>
</tr>
<tr>
<td>$p l _ { - }$</td>
<td>Adapter to Protocol Layer indication that data is valid on pl_data.</td>
</tr>
<tr>
<td>pl_data [NBYTES-1 : 0] [ 7: 0]</td>
<td>Adapter to Protocol Layer data, where NBYTES equals the number of bytes determined by the data width for the FDI instance.</td>
</tr>
<tr>
<td>pl_retimer_crd</td>
<td>$\text { When asserted at rising clock edge, it indicates a sindiched rinding Fithe and cher and } C R C _ { \prime } .$ This signal must NOT assert if a Retimer is not present. On FDI, this is an optional signal. It is permitted to expose these credits to Protocol Layer for Raw Format only. If this is not exposed to Protocol Layer, Adapter must track credit at 256B granularity even for Raw Format and back-pressure the Protocol Layer using pl_trdy. When this is exposed on FDI, the Adapter converts the initial credits received from the Retimer over sideband to credit returns to the Protocol Layer on this bit after Adapter LSM has moved to Active state.</td>
</tr>
<tr>
<td>$p l _ { - } d l l p \left[ N D L l l p - 1 : 0 \right]$</td>
<td>Adapter to Protocol Layer transfer of DLLP bytes. This is not used for 68B Flit mode, CXL.cachemem or Streaming protocols. For a 64B data path on pl_data, it is recommended to assign NDLLP &gt;= 8, so that 1 DLLP per Flit can be transferred from the Adapter to the Protocol Layer, on average. The Adapter is responsible for extracting DLLP $f r o m \quad D L P \quad B y t e s \quad 2 : 5 \quad i f \quad a \quad F l i t \quad M a r k e r \quad i s \quad n o t \quad p r e s e n t . T h e \quad A d a p t e r \quad i s \quad a l s o \quad r e s p o n s i b l e \quad f o r$ corresponding transfer on FDI.</td>
</tr>
<tr>
<td>pl_dllp_valid</td>
<td>Indicates valid DLLP transfer on pl_dllp. DLLPs can be transferred to the Protocol Layer whenever valid Flits can be transferred on pl_data. There is no backpressure and the Protocol Layer must always sink DLLPs.</td>
</tr>
<tr>
<td>pl_dllp_ofc</td>
<td>Indicates that the corresponding DLLP bytes on pl_dllp follow the Optimized_Update_FC format. It must stay asserted for the entire duration of the DLLP transfer on pl_dllp.</td>
</tr>
<tr>
<td rowspan="2">$p l _ { - } \text { stream } \left[ 7 : 0 \right]$</td>
<td>Adapter to Protocol Layer signal that indicates the stream ID to use with data. Each stream ID maps to a unique protocol. It is relevant only when pl_valid is 1.</td>
</tr>
<tr>
<td>$0 0 h : R e s e r v e d$ 11h: Stack 1: PCIe 01h: PCIe 12h: Stack 1: CXL.io 02h: Stack 0: CXL.io 13h: Stack 1: CXL.cachemem 03h: Stack 0: CXL.cachemem 14h: Stack 1: Streaming protocol 04h: Stack 0: Streaming protocol 15h: Stack 1: Management Transport 05h: Stack 0: Management Transport protocol protocol Other encodings are Reserved.</td>
</tr>
</table>

<table>
<caption>Table 10-3. FDI signal list (Sheet 3 of 7)</caption>
<tr>
<th>Signal Name</th>
<th>Signal Description</th>
</tr>
<tr>
<td>pl_flit_cancel</td>
<td>Adapter to Protocol Layer indication to dump a Flit. This enables latency optimizations on the Receiver data path when CRC checking is enabled in the Adapter. It is not applicable for Raw Format or 68B Flit Format. For Standard 256B Flit, it is required to have a fixed number of clock cycle delay between the last chunk of a Flit transfer and the assertion of pl_flit_cancel. This delay is fixed to be 1 cycle (i.e., the cycle after the last chunk transfer of a Flit). When this signal is asserted, Protocol Layer must not consume the associated Flit. For Latency-Optimized 256B Flits, it is required to have a fixed number of clock cycle delay between the last chunk of a 128B half Flit transfer and the assertion of pl_flit_cancel. This delay is fixed to be 1 cycle (i.e., the cycle after the last transfer of the corresponding 128B chunk). When this signal is asserted, Protocol Layer must not consume the associated Flit half. When this mode is supported, Protocol Layer must support it for all applicable Flit Formats associated with the corresponding protocol. Adapter must guarantee this to be a single cycle pulse when dumping a Flit or Flit half. It is the responsibility of the Adapter to ensure that the canceled Flits or Flit halves are eventually replayed on the interface without cancellation in the correct order once they pass CRC after Retry etc. See Section 10.2.5 for examples. When operating in UCIe Flit mode, it is permitted to use this signal to also cancel valid NOP Flits for the Protocol Layer to prevent forwarding these to the Protocol Layer. However for interoperability, if a Protocol Layer receives a NOP Flit without a corresponding pl_flit_cancel, it must discard these Flits.</td>
</tr>
<tr>
<td>lp_state_req [3: 0]</td>
<td>Protocol Layer request to Adapter to request state change. Encodings as follows: $0 0 0 0 b : N O P$ 1001b: LinkReset 1011b: Retrain 0100b: L1 1100b: Disabled 1000b: L2 All other encodings are reserved.</td>
</tr>
<tr>
<td>lp_linkerror</td>
<td>Protocol Layer to Adapter indication that an error has occurred which requires the Link to go down. Adapter must propagate this request to RDI, and move the Adapter LSMs (and CXL vLSMs if applicable) to LinkError state once RDI is in LinkError state. It must stay there as long as $\begin{array}{} { \text { 1p 1 inkerror } = 1 . \text { The reason for having this } } \\ { \text { eqular state transitions is to allow immediate } a } \end{array}$ be an indication decoupled from action on part of the Protocol Layer and Adapter in order to provide the quickest path for error containment when applicable (e.g., a viral error escalation could map to the LinkError state).</td>
</tr>
<tr>
<td rowspan="4">$p l _ { - } \text { state } _ { - } \text { sts } \left[ 3 : 0 \right]$</td>
<td>Adapter to Protocol Layer Status indication of the Interface. Encodings as follows:</td>
</tr>
<tr>
<td>0000b: Reset 1001b: LinkReset</td>
</tr>
<tr>
<td>0001b: Active 1010b: LinkError 0011b: Active.PMNAK 1011b: Retrain L1 1100b: Disabled $1 0 0 0 b : L 2$ All other encodings are reserved.</td>
</tr>
<tr>
<td>The status signal is permitted to transition from Adapter autonomously when applicable. For example the Adapter asserts the Retrain status when it decides to enter retraining either autonomously or when requested by remote agent. For PCIe/Streaming protocols, the Adapter LSM is exposed as pl_state_sts to the Protocol Layer. For CXL protocol, the ARB/MUX vLSM is exposed as pl_state_sts to the Protocol Layer. The Link Status is considered to be Up from Protocol Layer perspective when FDI status is Active, Active.PMNAK, Retrain, L1, or L2. The Link Status is considered Down for other states of FDI.</td>
</tr>
<tr>
<td>pl_inband_pres</td>
<td>Adapter to the Protocol Layer indication that the Die-to-Die Link has finished negotiation with remote Link partner and is ready for transitioning the FDI Link State $M a c h i n e \left( L S M \right)$ to Active. Once it transitions to 1b, this must stay 1b until FDI moves to Active or LinkError. It stays asserted while FDI is in Retrain, Active, Active. PMNAK, L1, or L2. It must de-assert during Reset, LinkReset, Disabled or LinkError states.</td>
</tr>
</table>

<table>
<caption>Table 10-3. FDI signal list (Sheet 4 of 7)</caption>
<tr>
<th>Signal Name</th>
<th>Signal Description</th>
</tr>
<tr>
<td>$p l _ { n } e r r o r$</td>
<td>Adapter to the Protocol Layer indication that it has detected a framing related error. It is pipeline matched with the receive data path. In UCIe Raw mode, it must also assert if pl_error was asserted on RDI by the Physical Layer for a Flit which the Adapter is forwarding to the Protocol Layer. In UCIe Flit Mode, it is permitted for Protocol Layer to use pl_error indication to log correctable errors when Retry is enabled from the Adapter. The Adapter must finish any partial Flits sent to the Protocol Layer and assert pl_flit_cancel in order to prevent consumption of that Flit by the Protocol Layer. Adapter must initiate Link Retrain on RDI following this, if it was a framing error detected by the Adapter. In UCIe Flit Mode, if Retry is disabled, the Adapter is responsible for mapping internally detected framing errors or Physical Layer received pl_error to an Uncorrectable Internal Error and escalate it as pl_trainerror if the mask and severity registers permit the escalation. If the Link is operating in Raw Format, the Adapter has no internal detection of framing errors, it just forwards any pl_error indication received from the Physical Layer on FDI such that it is pipeline matched to the data path. It is a pulse indication that can occur only when FDI receiver is Active (i.e.</td>
</tr>
<tr>
<td>pl_cerror</td>
<td>$\frac { p 1 } { - 1 }$ not affect the data path. In UCIe Raw mode, the Protocol Layer must and pl_cerror signals for Correctable Error Logging. In UCIe Raw mode, pl_cerror is used for Correctable Error Logging, whereas pl_error mapping to correctable or uncorrectable error is implementation specific depending on the requirements of the underlying protocol. Errors logged in the Correctable Error Status register are mapped to this signal if the corresponding mask bit in the Correctable Error Mask register is cleared to 0. It is a pulse of one or more cycles that can occur in any FDI state. If it is a state in which clock gating is permitted, it is the responsibility of the Adapter to perform the clock gating exit handshake with the Protocol Layer before asserting this signal. Clock gating can resume after pl_cerror is de-asserted and all other conditions permitting clock gating have been met.</td>
</tr>
<tr>
<td>pl_nferror</td>
<td>Adapter to the Protocol Layer indication that a non-fatal error was detected. This is used by Protocol Layer for error logging and corresponding escalation to software. The Adapter must OR any internally detected errors with pl_nferror on RDI and forward the result on FDI. Errors logged in Uncorrectable Error Status Register are mapped to this signal if the corresponding Severity and Mask bits are cleared to 0. It is a pulse of one or more cycles that can occur in any FDI state. If it is a state in which to perform the clock $g a t i n g \quad e x i t \quad h a n d s h a k e \quad w i t h \quad t h e \quad P r o t o c o l \quad L a y e r \quad b e f o r e \quad a s s e r t i n g \quad t h i s \quad s i g n a l . C l o c k \quad g a t i n g$ $p$</td>
</tr>
<tr>
<td>pl_trainerror</td>
<td>Indicates a fatal error from the Adapter. Adapter must transition pl_state_sts to LinkError if not already in LinkError state. (Note that the Adapter first takes RDI to LinkError, and that LinkError is eventually propagated to all the FDI states). $I m p l e m e n t a t i o n s \quad a r e \quad p e r m i t t e d \quad t o \quad m a p \quad a n y \quad f a t a l \quad e r r o r \quad t o \quad t h i s \quad s i g n a l \quad t h a t \quad r e q u i r e \quad u p p e r$ $\begin{array}{} { \text { Errors loged in Uncorrectable Error Status Reqister are mapped this signal if the } } \\ { \text { corresponding Severity is set to to to thac corresponding Mask bit is cleared to } 0 . } \end{array}$ $I t \quad i s \quad a \quad l e v e l \quad s i g n a l$ that can assert in any FDI state but stays asserted until FDI exits the to Reset state.</td>
</tr>
<tr>
<td>pl_rx_active_req</td>
<td>Adapter asserts this signal to request the Protocol Layer to open its Receiver's data path and get ready for receiving protocol data or Flits. The rising edge of this signal must be when pl_state_sts is Reset, Retrain or Active. Together with lp_rx_active_sts, it forms a four way handshake. See Section 10.2.7 for rules related to this handshake.</td>
</tr>
<tr>
<td>lp_rx_active_sts</td>
<td>Protocol Layer responds to pl_rx_active_req after it is ready to receive and parse protocol data or Flits. Together with pl_rx_active_req, it forms a four way handshake. See Section 10.2.7 for rules related to this handshake.</td>
</tr>
</table>

<table>
<caption>Table 10-3. FDI signal list (Sheet 5 of 7)</caption>
<tr>
<th>Signal Name</th>
<th>Signal Description</th>
</tr>
<tr>
<td>pl_protocol [3: 0]</td>
<td>Adapter indication to Protocol Layer of the protocol that was negotiated during training. 0000b: PCIe without Management Transport 0011b: CXL.1 [Single protocol, i.e., CXL.io] without Management Transport 0100b: CXL.2 [Multi-protocol, Type 1 device] without Management Transport 0101b: CXL.3 [Multi-protocol, Type 2 device] without Management Transport 0110b: CXL.4 [Multi-protocol, Type 3 device] without Management Transport 0111b: Streaming protocol without Management Transport 1000b: PCIe with Management Transport 1001b: Management Transport 1011b: CXL.1 [Single protocol, i.e., CXL.io] with Management Transport 1100b: CXL.2 [Multi-protocol, $\left. T y p e \quad 2 \quad d e v i c e \right] w i t h \quad M a n a g e m e n t \quad T r a n s p o r t$ $\begin{array}{} { 1 1 0 1 0 : C X L . 3 \left[ \text { MUIt } - p r C \right. } \\ { 1 1 1 0 b : C X L . 4 \left[ M u l t i - p r c \right. } \end{array} ,$ Type 3 device] with Management Transport 1111b: Streaming protocol with Management Transport Other encodings are Reserved</td>
</tr>
<tr>
<td>pl_protocol_flitfmt [3: 0]</td>
<td>This indicates the negotiated Format. See Chapter 3.0 for the definitions of these formats. 0001b: Format 1: Raw Format 0010b: Format 2: 68B Flit Format $\begin{array}{} { 0 0 1 1 b : \text { Format } 3 : \text { Standard } 2 5 6 B \text { Endrint Filt Furt Furt } } \\ { 0 1 0 0 b : \text { Format } 4 : \text { Standard } 2 5 6 B \text { Start Header Flit Forma } } \end{array}$ 5: Latency-Optimized 256B without Optional Bytes Flit Format $0 1 1 0 b : F o r m a t \quad 6 :$ Latency-Optimized 256B with Optional Bytes Flit Format Other encodings are Reserved</td>
</tr>
<tr>
<td>pl_protocol_vld</td>
<td>Indication that pl_protocol, and pl_protocol_flitfmt have valid information. This is a level signal, asserted when the Adapter has determined the appropriate protocol, but must only de-assert again after subsequent transitions to LinkError or Reset state depending on the Link state machine transitions. $w h e n \quad p l \_ p r o t o c o l \_ v l d = 1 \quad a n d \quad p l \_ s t a t e \_ s t s = R e s e t \quad a n d \quad p l \_ i n b a n d \_ p r e s =$ 1. The Adapter must ensure that if pl_inband_pres = 1, pl_protocol_vld = 1 and pl_state_sts = Reset, then pl_protocol and pl_protocol_flitfmt are the correct values that can be sampled by the Protocol Layer.</td>
</tr>
<tr>
<td>pl_stallreq</td>
<td>Adapter request to Protocol Layer to flush all Flits for state transition and not prepare any new Flits.</td>
</tr>
<tr>
<td>lp_stallack</td>
<td>$P r o t o c o l \quad L a y e r \quad t o \quad A d a p t e r \quad i n d i c a t i o n \quad t h a t \quad t h e \quad F l i t s \quad a r e \quad a l i g n e d \quad a n d \quad s t a l l e d \left( i f \right.$ pl_stallreq was asserted). It is strongly a global free running clock, so the Protocol Layer can respond to pl_stallreq with lp_stallack even if other significant portions of the Protocol Layer are clock gated.</td>
</tr>
<tr>
<td>pl_phyinrecenter</td>
<td>Adapter indication to Protocol Layer that the Link is doing training or retraining (i.e., RDI has pl_phyinrecenter asserted or the Adapter LSM has not moved to Active yet). If this is asserted during a state where clock gating is permitted, the pl_clk_req/ lp_clk_ack handshake must be performed with the upper layer. The upper layers are permitted to use this to update the "Link Training/Retraining" bit in the UCIe Link Status register.</td>
</tr>
<tr>
<td>pl_phyinl1</td>
<td>Adapter indication to Protocol Layer that the Physical Layer is in L1 power management state (i.e., RDI is in L1 state).</td>
</tr>
<tr>
<td>pl_phyinl2</td>
<td>Adapter indication to Protocol Layer that the Physical Layer is in L2 power management state (i.e., RDI is in L2 state).</td>
</tr>
</table>

<table>
<caption>Table 10-3. FDI signal list (Sheet 6 of 7)</caption>
<tr>
<th>Signal Name</th>
<th>Signal Description</th>
</tr>
<tr>
<td>pl_speedmode $\mathrm { d e } \left[ 2 : 0 \right]$</td>
<td>Current Link speed. The following encodings are used: 000b: 4 GT/s 100b: 24 GT/s 001b: 8 GT/s 101b: 32 GT/s 010b: 12 GT/s 110b: 48 GT/s 011b: 16 GT/s 111b: 64 GT/s The Protocol Layer must only consider this signal to be relevant when the FDI state is Active or Retrain. For multi-module configurations, all modules must operate at the same speed.</td>
</tr>
<tr>
<td>pl_max_speedmode</td>
<td>Maximum Data Rate. The following encodings are used: $0 : < = 3 2 \quad G T / s$ 1: &gt; 32 GT/s The Protocol Layer must only consider this signal to be relevant when the FDI state transitions from Reset to Active. It indicates the negotiated maximum data rate by the Physical Layer during MBINIT.PARAM; thus, this signal can only change while FDI is in Reset state.</td>
</tr>
<tr>
<td>pl_lnk_cfg[2:0]</td>
<td>Current Link Configuration. Indicates the current operating width of a module. 000b: x4 100b: x64 001b: x8 101b: x128 010b: x16 110b: x256 $0 1 1 b : \times 3 2$ other encodings are reserved. The Protocol Layer must only consider this signal to be relevant when the FDI state is Active or Retrain. This is the total width across all Active modules for the corresponding FDI instance.</td>
</tr>
<tr>
<td>pl_clk_req</td>
<td>Request from the Adapter to remove clock gating from the internal logic of the Protocol Layer. This is an asynchronous signal from the Protocol Layer's perspective since it is not tied to 1clk being available in the Protocol Layer. Together with lp_clk_ack, it forms a four-way handshake to enable dynamic clock gating in the Protocol Layer. When dynamic clock gating is supported, the Protocol Layer must use this signal to exit clock gating before responding with lp_clk_ack. If dynamic clock gating is not supported, it is permitted for the Adapter to tie this signal to 1b.</td>
</tr>
<tr>
<td>$l p \_ c l k \_ a c k$</td>
<td>Response from the Protocol Layer to the Adapter acknowledging that its clocks have been ungated in response to pl_clk_req. This signal is only asserted when pl_clk_req is asserted, and de-asserted after pl_clk_req has de-asserted. When dynamic clock gating is not supported by the Protocol Layer, it must stage pl_clk_req internally for one or more clock cycles and turn it around as 1p_clk_ack. clock gating. This way it will still participate in the handshake even though it does not support dynamic</td>
</tr>
<tr>
<td>lp_wake_req</td>
<td>Request from the Protocol Layer to remove clock gating from the internal logic of the Adapter. This is an asynchronous signal relative to 1clk from the Adapter's perspective since it is not tied to 1clk being available in the Adapter. Together with pl_wake_ack, it forms a four-way handshake to enable dynamic clock gating in the Adapter. $S ^ { 1 }$ signal to 1b.</td>
</tr>
<tr>
<td>pl_wake_ack</td>
<td>Response from the Adapter to the Protocol Layer acknowledging that its clocks have been ungated in response to lp_wake_req. This signal is only asserted after lp_wake_req has asserted, and is de-asserted after 1p_wake_req has de-asserted. When dynamic clock gating is not supported by the Adapter, it must stage p_wake_req internally for one or more clock cycles and turn it around as pl_wake_ack. This way it will still participate in the handshake even though it does not support dynamic clock gating.</td>
</tr>
</table>

<table>
<caption>Table 10-3. FDI signal list (Sheet 7 of 7)</caption>
<tr>
<th>Signal Name</th>
<th>Signal Description</th>
</tr>
<tr>
<td>$p l _ { - } c f g \left[ N C - 1 : 0 \right.$</td>
<td>This is the sideband interface from the Adapter to the Protocol Layer. See Chapter 7.0 for details. NC is the width of the interface. Supported values are 8, 16, and 32. must be implemented by hardware to be atomic regardless of the width $o f \quad t h e \quad i n t e r f a c e \left( i . e . , \right.$ all 32 bits of a register must be updated in the same cycle for a 32- bit register write, and similarly all 64 bits of a register must be updated in the same cycle</td>
</tr>
<tr>
<td>pl_cfg_vld</td>
<td>$W h e n \quad a s s e r t e d , i n d i c a t e s \quad t h a t \quad p l \_ c f g \quad h a s \quad v a l i d$ information that should be consumed by</td>
</tr>
<tr>
<td>pl_cfg_crd</td>
<td>Credit return for sideband packets from the Adapter to the Protocol Layer for sideband corresponds to 64 bits of header and 64 bits of data. Even $t r a n s a c t i o n s \quad t h a t \quad d o \quad n o t \quad c a r r y$ data or carry 32 bits of data consume the same credit and the Receiver returns the credit once the corresponding transaction has been processed or de-allocated from its internal buffers. See Section 7.1.3.1 for additional flow control rules. A value of 1 sampled at a rising clock edge indicates a single credit return. Because the advertised credits are design parameters, the Protocol Layer transmitter updates the credit counters with initial credits on domain reset exit, and no initialization credits are returned over the interface. Credit returns must follow the same rules of clock gating exit handshakes as the sideband packets to ensure that no credit returns are dropped by the receiver of the credit returns.</td>
</tr>
<tr>
<td>$1 p _ { - } \text { cfg } \left[ N C - 1 : 0 \right]$</td>
<td>This is the sideband interface from Protocol Layer to the Adapter. See Chapter 7.0 for details. NC is the width of the interface. Supported values are 8, 16, and 32. Register accesses must be implemented by hardware to be atomic regardless of the width of the interface (i.e., all 32 bits of a register must be updated in the same cycle for a 32- bit register write, and similarly all 64 bits of a register must be updated in the same cycle for a 64-bit register write).</td>
</tr>
<tr>
<td>$l p \_ c f g \_ v l d$</td>
<td>the Adapter. When asserted, indicates that lp_cfg has valid information that should be consumed by</td>
</tr>
<tr>
<td>lp_cfg_crd</td>
<td>Credit return for sideband packets from the Protocol Layer to the Adapter for sideband packets. Each credit corresponds to 64 bits of header and 64 bits of data. Even transactions that do not carry data or carry 32 bits of data consume the same credit and the Receiver returns the credit once the corresponding transaction has been processed or de-allocated from its internal buffers. See Section 7.1.3.1 for additional flow control rules. A value of 1 sampled at a rising clock edge indicates a single credit return. Because the advertised credits are design parameters, the Adapter transmitter updates the credit counters with initial credits on domain reset exit, and no initialization credits are returned over the interface. Credit returns must follow the same rules of clock gating exit handshakes as the sideband packets to ensure that no credit returns are dropped by the receiver of the credit returns.</td>
</tr>
<tr>
<td>dm_param_exchange_done</td>
<td>Signal resets to 0 on a Domain Reset. In single stack management transport implementations, this signal is asserted when $a d a p t e r \quad p a r a m e t e r \quad e x c h a n g e \quad h a s \quad c o m p l e t e d \quad b e t w e e n \quad b o t h \quad s i d e s \quad a n d \quad f l i t \quad f o r m a t / p r o t o c o l$ $\begin{array}{} { \text { In multi-stack managent transport implement inations, this signal is anser onter ontrationer } } \\ { \text { both stacks have completed their individual adapter pararter exthanges and protocol } } \end{array}$ $\begin{array}{} { \text { has been fi } } \\ { \text { of the activ } } \end{array}$ finalized (successfully or unsuccessfully) across both stacks. If at run time one stacks enters link status=down condition, this signal de-asserts and asserts again only when the above condition is again met.</td>
</tr>
<tr>
<td>dm_param_stack_count [N-1: 0]</td>
<td>Number of stacks that successfully negotiated Management Transport protocol. This field is sampled only when dm_param_exchange_done signal is asserted. If 68B Flit format was finalized, this field must be cleared to 00b. $0 0 b : 0 \quad s t a c k$ 10b: 2 stacks 01b: 1 stack Others: reserved N=1 for single stack and 2 for 2 stacks.</td>
</tr>
<tr>
<td>pl_vendor_defined [VS-1 : 0]</td>
<td>Optional Vendor Defined signals. See Section 10.3.4 for an example usage of these signals. If these signals are instantiated, but the UCIe stack is not operating in a mode that utilizes them, these signals should not assert.</td>
</tr>
<tr>
<td>lp_vendor_defined [VS-1 : 0]</td>
<td>Optional Vendor Defined signals. See Section 10.3.4 for an example usage of these signals. If these signals are instantiated, but the UCIe stack is not operating in a mode that utilizes them, these signals should not assert.</td>
</tr>
</table>

### 10.2.1 Interface reset requirements

FDI does not define a separate interface signal for reset; however, it is required that the logic entities
on both sides of FDI are in the same reset domain and the reset for each side is derived from the
same source. Because reset may be staggered due to SoC routing, all signals coming out of reset
must be driven to 0, unless otherwise specified. lp_stream and pl_stream are exceptions to this
rule if they are tied off to their expected values at the time of integration. If lp_stream and
pl_stream are not tied off, they must be driven to 0 when coming out of reset.

### 10.2.2 Interface clocking requirements

FDI requires both sides of the interface to be on the same clock domain. Moreover, the clock domain
for sideband interface $\left( * _ { \mathrm { C } } \mathrm { f } \mathrm { g } ^ { * } \right)$ is the same as the mainband signals. The sideband interface includes
the pl_cfg, pl_cfg_vld, pl_cfg_crd, lp_cfg, lp_cfg_vld, and lp_cfg_crd signals. If
Management Transport is not supported over sideband, all signals are synchronous to lclk. When
Management Transport is supported over the sideband and exposed to the FDI interface, the sideband
interface as well as the signals in Table 10-2 are permitted to be on a separate Mgmt_clk domain. For
example, this Mgmt_clk can be the auxiliary clock so that the management transport is available
over the sideband even if the clocks required for the mainband and for lclk are unavailable.

Each side is permitted to instantiate clock crossing FIFOs internally if needed, as long as it does not
violate the requirements at the interface itself.

It is important to note that there is no back pressure possible from the Protocol Layer to the Adapter
on the main data path. So any clock crossing related logic internal to the Protocol Layer must take
this into consideration.

### 10.2.3 Dynamic clock gating

Dynamic coarse clock gating is permitted in the Adapter and Protocol Layer when pl_state_sts is
Reset, LinkReset, Disabled or PM states. This section defines the rules around entry and exit of clock
gating. Note that clock gating is not permitted in LinkError states - it is expected that the UCIe usages
will enable error handlers to make sure the Link is not stuck in a LinkError state, if the intent is to
save power when a Link is in an error state.

#### 10.2.3.1 Rules and description for Ip_wake_req/pl_wake_ack handshake

Protocol Layer can request removal of clock gating of the Adapter by asserting lp_wake_req
(asynchronous to lclk availability in the Adapter). All Adapter implementations must respond with a
pl_wake_ack (synchronous to lclk). The extent of internal clock ungating when pl_wake_ack is
asserted is implementation-specific, but Iclk must be available by this time to enable FDI transitions
from the Protocol Layers. The Wake Req/Ack is a full handshake and it must be used for state
transition requests (on lp_state_req or lp_linkerror) when moving away from a state in which
clock gating is permitted. It must also be used for sending packets on the sideband interface.

Rules for this handshake:

1\. Protocol Layer asserts lp_wake_req to request ungating of clocks by the Adapter.

2\. The Adapter asserts pl_wake_ack to indicate that clock gating has been removed. There must
be at least one clock cycle bubble between lp_wake_req assertion and pl_wake_ack assertion.

3\. lp_wake_req must de-assert before pl_wake_ack de-asserts. It is the responsibility of the
Protocol Layer to control the specific scenario of de-assertion. As an example, when performing
the handshake for a state request, it is permitted to keep lp_wake_req asserted until it observes
the desired state status. Protocol Layer is also permitted to keep lp_wake_req asserted through
states where clock gating is not permitted in the Adapter (i.e., Active, LinkError or Retrain).

4\. lp_wake_req should not be the only consideration for Adapter to perform clock gating, it must
take into account pl_state_sts and other internal or Link requirements before performing
global and/or local clock gating.

5\. When performing lp_wake_req/pl_wake_ack handshake for lp_state_req transitions or
lp_linkerror transition, the Protocol Layer is permitted to not wait for pl_wake_ack before
changing lp_state_req or lp_linkerror.

6\. When performing lp_wake_req/pl_wake_ack handshake for lp_cfg transitions, Protocol
Layer must wait for pl_wake_ack before changing lp_cfg or lp_cfg_vld. Because lp_cfg
can have multiple transitions for a single packet transfer, it is necessary to make sure that the
Adapter clocks are up before transfer begins.

#### 10.2.3.2 Rules and description for pl_clk_req/lp_clk_ack handshake

Adapter is allowed to initiate pl_clk_req/lp_clk_ack handshake at any time and the Protocol
Layer must respond.

Rules for this handshake:

1\. Adapter asserts pl_clk_req to request removal of clock gating by the Protocol Layer. This can
be done anytime, and independent of current FDI state.

2\. The Protocol Layer asserts lp_clk_ack to indicate that clock gating has been removed. There
must be at least one clock cycle bubble between pl_clk_req assertion and lp_clk_ack
assertion.

3\. pl_clk_req must de-assert before lp_clk_ack. It is the responsibility of the Adapter to control
the specific scenario of de-assertion, after the required actions for this handshake are completed.

4\. pl_clk_req should not be the only consideration for the Protocol Layer to perform clock gating,
it must take into account pl_state_sts and other protocol-specific requirements before
performing trunk and/or local clock gating.

5\. The Adapter must use this handshake to ensure transitions of pl_inband_pres, pl_phyinl1,
pl_phyinl2, pl_phyinrecenter, and pl_rx_active_req have been observed by the
Protocol Layer. Because these are level-oriented signals, the Adapter is permitted to let the
signals transition without waiting for lp_clk_ack. When this is done during initial Link bring up,
it is strongly recommended for the Adapter to keep pl_clk_req asserted until the state status
transitions away from Reset to a state where clock gating is not permitted or until the state status
is Reset and pl_inband_pres de-asserts. It is permitted for any of pl_inband_pres,
pl_phyinl1, pl_phyinl2, and/or pl_phyinrecenter to assert before OR after pl_clk_req
asserts; however, their assertion is not guaranteed to be observed by the Adapter until the
pl_clk_req/lp_clk_ack handshake is complete.

Figure 10-13. Example Waveform Showing Handling of Level Transition

<figure>

0

1

2

3

4

5

6

7

8

9

10

11

12

13

14

15

$\mathrm { l c l k }$

pl_clk_req

lp_clk_ack

pl_inband_pres

</figure>

6\. The Adapter must also perform this handshake before transition to LinkError state from Reset,
LinkReset, Disabled or PM state (especially when the LinkError transition occurs by the Adapter
without being directed by the Protocol Layer). It is permitted to assert pl_clk_req before the
state change, in which case it must stay asserted until the state status transitions. It is also
permitted to assert pl_clk_req after the state status transition, but in this case Adapter must
wait for lp_clk_ack before performing another state transition.

7\. The Adapter must also perform this handshake when the status is PM and remote Link partner is
requesting PM exit. For exit from Reset, LinkReset, Disabled or PM states to a state that is not
LinkError, it is required to assert pl_clk_req before the status change, and in this case it must
stay asserted until the state status transitions away from Reset or PM.

8\. The Adapter must also perform this handshake for sideband transfers from the Adapter to the
Protocol Layer. When performing the handshake for pl_cfg transitions, Adapter must wait for
lp_clk_ack before changing pl_cfg or pl_cfg_vld. Because pl_cfg can have multiple
transitions for a single packet transfer, it is necessary to make sure that the Protocol Layer clocks
are up before transfer begins.

When clock-gated in Reset states, Protocol Layers that rely on dynamic clock gating to save power
must wait in clock gated state for pl_inband_pres=1. The Adapter will request clock gating exit
when it transitions pl_inband_pres, and the Protocol Layer must wait for pl_inband_pres
assertion before requesting lp_state_req = ACTIVE. If pl_inband_pres de-asserts while
pl_state_sts = Reset, then the Protocol Layer is permitted to return to clock-gated state after
moving lp_state_req to NOP.

### 10.2.4 Data Transfer

As indicated in the signal list descriptions, when Protocol Layer is sending data to the Adapter, data is
transferred when lp_irdy, pl_trdy and lp_valid are asserted. Figure 10-14 shows an example
waveform for data transfer from the Protocol Layer to the Adapter. Data is transmitted on clock cycles
1, 2, and 5. No assumption should be made by Protocol Layer about when pl_trdy can de-assert or
for how many cycles it remains de-asserted before it is asserted again, unless explicitly guaranteed by
the Adapter. If a Flit transfer takes multiple clock cycles, the Protocol Layer is not permitted to insert
bubbles in the middle of a Flit transfer (i.e., lp_valid and lp_irdy must be asserted continuously
until the Flit transfer is complete. Of course, data transfer can stall because of pl_trdy de-
assertion).

<figure>
<figcaption>Figure 10-14. Data Transfer from Protocol Layer to Adapter</figcaption>

0

1

2

3

4

5

6

$\mathrm { c l k }$

$\mathrm { l p } \_ \mathrm { i r d y }$

lp_data

Dat0

Dat1

Dat2

lp_valid

pl_trdy

</figure>

As indicated in the signal list descriptions, when Adapter is sending data to the Protocol layer, there is
no back-pressure mechanism, and data is transferred whenever pl_valid is asserted. The Adapter
is permitted to insert bubbles in the middle of a Flit transfer and the Protocol Layer must be able to
handle that.

### 10.2.4.1 DLLP transfer rules for 256B Flit Mode

For PCIe and CXL.io 256B Flits (both Standard and Latency-Optimized), FDI provides a separate
signal for DLLP transfers from the Protocol Layer to the Adapter and vice-versa. Since the DLLPs have
to bypass the Retry buffer, the separate signal enables the Adapter to insert DLLPs into the Flits from
the Protocol Layer or the Retry buffer, if it is permitted to do so per the Flit packing rules of the
corresponding Flit Format. Rules relevant for FDI operation (per FDI instance) are outlined below:

For the Transmitting side:

· Protocol Layer is responsible for sending the relevant DLLPs at the rate defined by the underlying
Protocol to prevent timeouts of DLLP exchanges. If the Protocol Layer has no TLPs to send, it
must insert NOP Flits to ensure that the Adapter gets an opportunity to insert the DLLP bytes.

· When transferring DLLP or Optimized_Update_FC, the least significant byte is sent over Byte 0 of
the FDI bus, the next byte over Byte 1 and so on. When the transfer is over multiple chunks
across FDI, Byte 0 is transferred on the first chunk LSB, Byte 1 following it and so on.

· The Adapter must have storage for at least 1 DLLP of every unique DLLP encoding (including
Optimized_Update_FC) per supported VC that is possible for transfer to remote Link partner. The
Adapter tracks pending DLLPs and schedules them on the next available opportunity for the
relevant Flits. Credit update DLLPs must not be reordered for a VC by the Adapter. It is however
permitted to discard a pending credit DLLP if the Protocol Layer presented a new credit DLLP of
the same FC and VC. This extends to Optimized_Update_FC packets; i.e., it is permitted to
discard any pending NP or P Update FC DLLPs, if the Protocol Layer transferred an
Optimized_Update_FC for the corresponding VC.

On the Receiving side:

. The Adapter must extract DLLPs from received Flits of the corresponding protocol and forward
them to the Protocol Layer. The FDI signal width of pl_dllp must be wide enough to keep up
with the maximum rate of DLLPs that could be received from the Link.

. When transferring DLLP over multiple chunks across FDI, Byte 0 is transferred on the first chunk
LSB, Byte 1 following it and so on.

. The Protocol Identifier corresponding to D2D Adapter in the Flit Header overlaps with the $\mathrm { F l i t }$
usage of NOP Flits defined in PCIe and CXL specifications. The Adapter must check for available

DLLPs in these Flits as well. All 0 bits in the DLLP byte positions indicate a NOP DLLP, and must
not be forwarded to the Protocol Layer.

### 10.2.5 Examples of pl_flit_cancel Timing Relationships

In all the examples shown in this section, a 64B datapath on FDI is shown, and "FOBytes" in the
figures correspond to "Flit 0 Bytes".

Figure 10-15 shows an example timing relationship for pl_flit_cancel and pl_data for Latency-
Optimized Flits when the first Flit half fails CRC check. Both Flit halves are canceled by the Adapter in
this example by asserting pl_flit_cancel one clock after the last chunk transfer of the
corresponding Flit half. It is permitted for the Adapter to de-assert pl_valid on clock cycles 5 and 6
instead of canceling that Flit half; however, this might have implications to meeting physical design
timing margins in the Adapter. The use of pl_flit_cancel allows the Adapter to perform the CRC
check on the side without putting the CRC logic in the critical timing path of the data flow and thus
permitting higher frequency operation for implementations. In the example shown, after replay flow
the entire Flit is transferred to the Protocol Layer without canceling as CRC checks pass.

<figure>
<figcaption>Figure 10-15. Example for pl_flit_cancel for Latency-Optimized Flits and CRC Error on First Flit Half</figcaption>

2

J

4

5

a

1

n

Icik

pl_data(63:0][7.0]

FOBytes(83.0]

FOBytes(127.64]

FOBytes(191:128]

FOBytes(255:192]

F0Bytes(63.0]

F0Bytes(127.64]

FOBytes[191:128]

FOBytes[255.192]

p_valid

pl_fit_cancel

</figure>

Figure 10-16 and Figure 10-17 show examples of two possible implementations of timing relationship
for pl_flit_cancel and pl_data for Latency-Optimized Flits when the second Flit half fails CRC
check. In both cases, the first half of the Flit is consumed by the Protocol Layer because it is not
canceled by the Adapter (the data transferred on clock cycles 3 and 4).

In the first case (shown in Figure 10-16), after the replay flow, CRC passes, and the Adapter ensures
that the Protocol Layer does not re-consume the first half again by asserting pl_flit_cancel for it.
In this case, pl_valid asserts for the entire Flit, but only the second half is consumed because the
first half was canceled on clock cycle (n+2).

In the second case (shown in Figure 10-17), after the replay flow, CRC passes, and the Adapter
ensures that the Protocol Layer does not re-consume the first half again by not asserting pl_valid
for it.

Figure 10-16. Example for pl_flit_cancel for Latency-Optimized Flits
and CRC Error on Second Flit Half

<figure>
<figcaption>Figure 10-17. Example for pl_flit_cancel for Latency-Optimized Flits and CRC Error on Second Flit Half, Alternate Implementation Example</figcaption>

2

2

5

6

7

n

Icik

pl_data[63:0|17:0]

FOBytes(63.0)

FOBytes(127.64]

FOBytes[191:128

FOBytes(255:192]

FOBytes(63:0)

FOBytes(127:64)

FOBytes|191:128

(FOBytes(256:192)

p_valid

pl __ cancel

</figure>

<figure>

2

9

1

5

0

n

TH

DJ 3

ICK

pl data[63.0|70]

FOBytes[63-0]

FOBytes|127.64]

FOBytes

191:128]

FOBytes[255:192]

FOBytes(63:0]

FOBytes[127:64]

FOBytes[191:128]

FOBytes[255.192]

pl_ valid

pl_fit_cancel

</figure>

Figure 10-18 shows an example for a Standard 256B Flit. In this case, the CRC bytes are packed
toward the end of the Flit and thus a CRC error on either of the two halves cancels the entire Flit.
After replay flow, CRC passes, and the entire Flit is sent to the Protocol Layer without canceling it.

<figure>
<figcaption>Figure 10-18. Example for pl_flit_cancel for Standard 256B Flits</figcaption>

1

a

3

\-

5

6

7

n+P

pl_data(63 0][7 0]

FOBytes(63.01

FOBytes(127.64]

FOBytes(191:128]

FOBytes[255. 192]

FÜBytes(83.0]

FOBytes[127.84]

FOBytes(191. 128)

FOBytes(255.1921

pl_valid

pl_Ilrt_cancel

</figure>

## 10.2.6 FDI State Machine

<figure>
<figcaption>Figure 10-19 shows the FDI state machine. Figure 10-19. FDI State Machine</figcaption>

Domain Reset Exit

Link Error

From Any State

Reset

Disabled

From Any State
(except LinkError)

L2

Active

LinkReset

From Any State
(except Disabled and
LinkError)

PMNAK

L1

Retrain

</figure>

### 10.2.7 Rx_active_req/Sts Handshake

The Adapter negotiates Active state transitions on FDI using sideband messages when the Adapter
LSM is exposed to the Protocol Layer. Since the sideband Link is running slower than the mainband
Link, the Adapter needs to make sure that the Protocol Layer's Receiver is already in Active state
(even though pl_state_sts might not have moved to Active yet) before responding to the Active
request sideband message from remote Link partner. Rx_active_req/Sts handshake facilitates this.

When CXL is sent over UCIe, ARB/MUX functionality is performed by the Adapter and CXL vLSMs are
exposed on FDI. Although ALMPs are transmitted over mainband, the interface to the Protocol Layer is
FDI and it follows the rules of Rx_active_req/Sts Handshake as well.

Rules for this handshake:

1\. The Adapter (or ARB/MUX) asserts pl_rx_active_req to trigger the Protocol Layer to open its
Receiver's data path for receiving protocol data or Flits. This signal does not affect the Transmitter
data path (it must wait for pl_state_sts to move to Active and follow the rules of pl_trdy).

pl_rx_active_req should have a rising edge only when lp_rx_active_sts = 0 and
pl_state_sts is Reset, Retrain or Active.

2\. The Protocol Layer asserts lp_rx_active_sts after pl_rx_active_req has asserted and
when it is ready to receive protocol data or Flits. There must be at least one clock cycle delay
between pl_rx_active_req assertion and lp_rx_active_sts assertion to prevent a
combinatorial loop.

3\. When pl_rx_active_req = 1 and lp_rx_active_sts = 1, the Receiver is in Active state if
pl_state_sts is Reset, Retrain, or Active.

4\. pl_rx_active_req should have a falling edge only when lp_rx_active_sts = 1. This must
trigger Protocol Layer to de-assert lp_rx_active_sts, and this completes the transition of the
Receiver away from Active state.

5\. For graceful exit from Active state (i.e., a transition to PM, Retrain, LinkReset or Disabled states),
both pl_rx_active_req and lp_rx_active_sts must de-assert before pl_state_sts
transitions away from Active.

6\. If pl_rx_active_req = 0 while pl_state_sts = Active, the Adapter must guarantee no Flits
would be sent to the Protocol Layer (for example, this can happen if the Adapter LSM or RDI is in
Retrain, but the vLSM exposed to Protocol Layer is still in Active). Thus, it is permitted to perform
this handshake even when the state status on FDI remains Active throughout.

7\. For Active to LinkError transition, it is permitted for pl_state_sts to transition to LinkError
before pl_rx_active_req de-asserts, but both pl_rx_active_req and lp_rx_active_sts
must de-assert before pl_state_sts transitions away from LinkError.

#### 10.2.8 FDI Bring up flow

Figure 10-20 shows an example flow for Stage 3 of the Link bring up highlighting the transitions on
FDI. This stage requires sequencing on FDI that coordinates the state transition from Reset to Active.
If multiple stacks of protocol or ARB/MUX is present, the same sequence happens independently for
each Protocol Layer stack. The flows on FDI are illustrated for Adapter 0 LSM in the sideband message
encodings, however Adapter 1 LSM must send the sideband message encodings corresponding to
Adapter 1 to its remote Link partner.

1\. Once Adapter has completed transition to Active on RDI and successful parameter negotiation
with the remote Link partner, it must do the pl_clk_req handshake with the Protocol Layer and
reflect pl_inband_pres=1 on FDI. Note that the pl_clk_req handshake is not shown in the
example flow in Figure 10-20

2\. This is the trigger for Protocol Layer to request Active state. It is permitted for the Protocol Layer
to wait unlit pl_protocol_vld = 1 before requesting Active. It must perform the lp_wake_req
handshake as described in Section 10.2.3.1. Note that the lp_wake_req handshake is not shown
in the example flow in Figure 10-20.

3\. On sampling lp_state_req = Active, the Adapter must send the
{LinkMgmt.Adapter0.Req.Active} sideband message to remote Link partner.

4\. The Adapter must respond to the {LinkMgmt.Adapter.Req.Active} sideband message with a
{LinkMgmt.Adapter.Rsp.Active} sideband message after making sure that the Protocol Layer's
Receiver is ready. The {LinkMgmt.Adapter0.Rsp.Active} must only be sent after the Adapter has
sampled pl_rx_active_req = lp_rx_active_sts = 1. As mentioned previously, the
pl_clk_req handshake applies to pl_rx_active_req as well; it is permitted for the Adapter
to keep pl_clk_req asserted continuously (once it has been asserted for pl_inband_pres)
while doing the bring up flow. Note once the Adapter has sent the
{LinkMgmt.Adapter0.Rsp.Active} sideband message, if it receives Flits from the remote Link
partner, it must process them as applicable (i.e. for UCIe Flit mode, the Adapter must respond to
the Sequence Number Handshake initiated by the remote Link or respond with Ack/Nak for
Payload Flits. The Adapter will have to insert NOPs in case the pl_state_sts signal has not yet
transitioned to Active).

5\. If no ARB/MUX is present, once the Adapter has sent and received the
{LinkMgmt.Adapter0.Rsp.Active} sideband message, it must transition pl_state_sts to Active
for the Protocol Layer, and Flit transfer can begin (i.e., new Flits can be accepted from the Protocol
Layer, and in UCIe Flit mode, the Adapter is permitted to initiate the Sequence Number
Handshake Phase if it has not already done so as a result of Step 4).

6\. If ARB/MUX is present, the sending and receipt of {LinkMgmt.Adapter0.Rsp.Active} sideband
message opens up the ARB/MUX to perform ALMP exchanges over mainband and eventually
transition the vLSMs to Active state.

Step 3 through Step 6 constitute the "Active Entry Handshake" on FDI and must be performed for
every entry to Active state. The Active.PMNAK to Active transition is not considered here because
Active.PMNAK is only a sub-state of Active. When Adapter 0 as well as Adapter 1 LSMs are proceeding
with the Retrain to Active transition, then in addition to the above rules, the Adapter must have
received both the {LinkMgmt.Adapter0.Rsp.Active} and {LinkMgmt.Adapter1.Rsp.Active} sideband
messages before the Sequence Number Handshake can be initiated. This is because the Retry buffer
is shared between both the Protocol Layer stacks, and thus both stacks must be ready to receive Flits
before initiating the Sequence Number Handshake.

<figure>
<figcaption>Figure 10-20. FDI Bring up flow</figcaption>

Protocol Layer
$D i e \quad 0$

Adapter
Die 0

Physical layer
Die 0

CHANNEL

Physical layer
Die 1

Adapter
Die 1

Protocol Layer
Die 1

Stage 2 Complete

Protocol para meter exchanges on sideband
Stage 3 Start

-pl_inband_pres = 0->1

pl_inband_pres = 0->1-

Protocol layer exits clock
gating, gives Active request

Protocol layer exits clock
gating, gives Active request

-lp_state_req=Active

$t p l \_ r x \_ a c t i v e \_ r e q = 0 - > 1$
lp_rx_active_sts=0->1-

SB MSG {LinkMgmt.Adapter0.Req.Active}

SB MSG {LinkMgmt.Adapter0.Rsp.Active}-

$- 1 p _ { - }$

SB MSG {LinkMgmt.Adapter0.Req.Active}

pl_rx_active_req=0->1-
Mlp_rx_active_sts = 0->1

SB MSG {LinkMgmt.AdapterO.Rsp.Active}

pl_state_sts =Active

pl_state_sts =Active-

Adapter opens TX and
moves to Active status once
it has sent and received an
Active Status

Adapter opens TX and
moves to Active status once
it has sent and received an
Active Status

If ARB/MUX exists, it performs the ALMP exchanges with remote ARB/MUX
before moving pl_state_sts to Active for the Protocol Layer

Stage 3 Complete. Flit transfer can begin

</figure>

##### 10.2.9 FDI PM Flow

This section describes the sequencing and rules for PM entry and exit on FDI. The rules are the same
for L1 or L2 entry. L1 exit transitions the state machine through Retrain to Active, whereas L2 exit
transitions the state machine through Reset to Active. The flow illustrations in the section use L1 as
an example. A "PM request" sideband message is {LinkMgmt.Adapter *. Req.L1} or
{LinkMgmt.Adapter *. Req.L2}. A "PM Response" sideband message is {LinkMgmt.Adapter *. Rsp.L1}
or {LinkMgmt.Adapter *. Rsp.L2}. The flows on FDI are illustrated for Adapter 0 LSM in the sideband
message encodings; however, Adapter 1 LSM must send the sideband message encodings
corresponding to Adapter 1 to its remote Link partner.

. The Protocol Layer requests PM entry on FDI after idle time criteria has been met. The criteria for
idle time is implementation specific and could be dependent on the protocol. For PCIe and CXL.io
protocols, PM DLLPs are not used to negotiate PM entry/exit when using D2D Adapter's Retry
buffer (i.e., UCIe Flit mode).

. If operating in UCIe Flit mode, ARB/MUX is present within the D2D Adapter, and it follows the
rules of CXL Specification (for 256B Flit mode) to take the vLSMs to the corresponding PM state.
Note that even for CXL 68B Flit mode, the same ALMP rules as 256B Flit mode are used. This is a
simplification on UCIe, because ALMPs always go through the retry buffer. Once vLSMs are in the
PM state, ARB/MUX requests the Adapter Link State Machine to enter the corresponding PM state.
The Adapter Link State Machine transition to PM follows the same rules as outlined for Protocol
Layer and Adapter below.

· If CXL or PCIe protocol has been negotiated, only the upstream port (UP) can initiate PM entry.
This is done using a sideband message from the UP Adapter to the downstream port (DP) Adapter.
DP Adapter must not initiate entry into PM. PM support is required for CXL and PCIe protocols. PM
entry is considered successful and complete once UP receives a valid "PM Response" sideband
message. Figure 10-21 shows an example flow for CXL or PCIe protocol PM Entry on FDI and
Adapter. Once the FDI status is PM for all Protocol Layers, the Adapter can request PM transition
on RDI.

. If Streaming protocol has been negotiated, OR UCIe is in Raw Format, OR Management Transport
protocol was negotiated over the mainband without CXL or PCIe, then both side Adapters must
issue a PM entry request through a sideband message once the conditions of PM entry have been
satisfied. PM entry is considered successful and complete once both sides have received a valid
"PM Response" sideband message. Figure 10-22 shows an example flow for symmetric protocols.
Once the FDI status is PM for all Protocol Layers, the Adapter can request PM transition on the
RDI.

· Protocol Layer requests PM entry once it has blocked transmission of any new Protocol Layer Flits,
by transitioning p_state_req to L1 or L2 encoding. Once requested, the Protocol Layer cannot
change this request until it observes the corresponding PM state, Retrain, Active.PMNAK or
LinkError state on pl_state_sts; unless it is a DP Protocol Layer for PCIe or CXL. Once the FDI
state is resolved, the Adapter must first bring it back to Active before processing any new PM
requests from the Protocol Layer.

\- If the resolution is PM (upon successful PM entry) and the Protocol Layer needs to exit PM (or
there is a pending Protocol Layer Active request from remote Link partner) then the Protocol
Layer must initiate PM exit flow on FDI by requesting lp_state_req = Active. All PM entry
related handshakes must have finished prior to this (for CXL/PCIe protocols, this is when UP
has received a valid "PM Response" sideband message. For symmetric protocols, this is when
both sides Adapter have received a valid "PM Response" sideband message).

\- If the resolution is Active. PMNAK, the Protocol Layer must initiate a request of Active on FDI.
Once the status moves to Active, the Protocol Layer is permitted to re-request PM entry (if all
conditions of PM entry are still met). Figure 10-23 shows an example of PM abort flow. The PM

request could have been from either side depending on the configuration. Protocol Layer must
continue receiving protocol data or Flits while the status is Active or Active. PMNAK.

\- DP Protocol Layer for PCIe or CXL is permitted to change request from PM to Active without
waiting for PM or Active. PMNAK (the DP FDI will never have pl_state_sts =Active.PMNAK
since it does not send "PM Request" sideband messages); however, it is still possible for the
Adapter to initiate a stallreq/ack and complete PM entry if it was in the process of committing
to PM entry when the Protocol Layer changed its request. In this scenario, the Protocol Layer
will see pl_state_sts transition to PM and it is permitted to continue asking for the new
state request.

\- If the resolution is LinkError, then the Link is down and it resets any outstanding PM
handshakes.

· Adapter (UP port only if CXL or PCIe protocol), initiates a "PM request" sideband message once it
samples a PM request on lp_state_req and has completed the StallReq/Ack handshake with
the corresponding Protocol Layer and its Retry buffer is empty of Flits from the Protocol Layer that
is requesting PM (all pending Acks have been received).

. If the Adapter LSM moves to Retrain while waiting for a "PM Response" sideband message, it must
wait for the response. Once the response is received, it must transition back to Active before
requesting a new PM entry. Note that the transition to Active requires Active Entry handshake
with the remote Link partner, and that will cause the remote partner to exit PM. If the Adapter
LSM receives a "PM Request" sideband message after it has transitioned to Retrain, it must
immediately respond with {LinkMgmt.Adapter0.Rsp.PMNAK}.

Note:
The precise timing of the remote Link partner that is observing Link Retrain is
unknown; thus, the safer thing to do is to go to Active and redo the PM handshake
when necessary for this scenario. There is a small probability that there might be an
exit from PM and re-entry back in PM under certain scenarios.

. Once the Adapter receives a "PM request" sideband message, it must respond to it within 2 us
(the time is only counted during the Adapter LSM being in Active state):

\- if its local Protocol Layer is requesting PM, it must respond with the corresponding "PM
Response" sideband message after finishing the StallReq/Ack handshake with its Protocol
Layer and its Retry buffer being empty. If the current status is not PM, it must transition
pl_state_sts to PM after responding to the sideband message.

\- If the current pl_state_sts = PM, it must respond with "PM Response" sideband message.

\- If pl_state_sts = Active and 1p_state_req = Active and it remains this way for 1us after
receiving the "PM Request" sideband message, it must respond with
{LinkMgmt.Adapter0.Rsp.PMNAK} sideband message. The time is only counted during all the
relevant state machines being in Active state.

. If the Adapter receives a "PM Response" sideband message in response to a "PM Request"
sideband message, it must transition pl_state_sts on its local FDI to PM (if it is currently in
Active state).

· If the Adapter receives a {LinkMgmt.Adapter0.Rsp.PMNAK} sideband message in response to a
"PM Request" sideband message, it must transition pl_state_sts on its local FDI to
Active.PMNAK state if it is currently in Active state. If it is not in Active state, no action needs to
be taken. It is permitted to retry PM entry handshake (if all conditions of PM entry are satisfied) at
least 2us after receiving the {LinkMgmt.Adapter0.Rsp.PMNAK} sideband message OR if it
received a corresponding "PM Request" sideband message from the remote Link partner.

· PM exit is initiated by the Protocol Layer requesting Active on FDI. After RDI is in Active, triggers
the Adapter to initiate PM exit by performing the Active Entry handshakes on sideband.
Figure 10-24 shows an example flow of PM exit on FDI when Adapter LSM is exposed.

\- PM exit handshake completion requires both Adapters to send as well as receive a
{LinkMgmt.Adapter0.Rsp.Active} sideband message. Once this has completed, the Adapter is
permitted to transition Adapter LSM to Active.

\- If pl_state_sts = PM and a {LinkMgmt.Adapter0.Req.Active} sideband message is
received, the Adapter must initiate pl_clk_req handshake with the Protocol Layer, and
transition Adapter LSM to Retrain (For L2 exit, the transition is to Reset). This must trigger the
Protocol Layer to request Active on lp_state_req (if not already doing so), and this in turn
triggers the Adapter to send {LinkMgmt.Adapter0.Req.Active} sideband message to the
remote Link partner.

Note that the following figures are examples and do not show the lp_wake_req, pl_clk_req, and/
or pl_rx_active_req handshakes. Implementations must follow the rules outlined for these
handshakes in previous sections.

<figure>
<figcaption>Figure 10-21. PM Entry example for CXL or PCIe protocols</figcaption>

DP Protocol Layer
Die 0

DP Adapter
Die 0

DP Physical layer
Die 0

CHANNEL

UP Physical layer
Die 1

UP Adapter
Die 1

UP Protocol Layer
Die 1

pl_state_sts = Active

pl_state_sts = Active

lp_state_req=L1

Adapter must wait for 1us to
see if Protocol Layer requests
PM

SB MSG {LinkMgmt.Adapter0.Req.L1}-

Adapter must finish the
pl_stallreq/lp_stallack
handshake before sending
side band message

lp_state_req=L1

pl state_sts = L1

SB MSG {LinkMgmt.AdapterO.Rsp.L1}-

Adapter must finish the
pl_stallreq/lp_stallack
handshake before sending
sideband message

pl_state_sts=L1

</figure>

<figure>
<figcaption>Figure 10-22. PM Entry example for symmetric protocol</figcaption>

Protocol Layer
Die 0

Adapter
$D i e \quad 0$

Physical layer
$D i e \quad 0$

CHANNEL

Physical layer
Die 1

Adapter
$D i e \quad 1$

$\begin{array}{} { \text { Protocol Layel } } \\ { \text { Die } 1 } \end{array}$

$p l \_ s t a t e \_ s t s = A c t i v e$

pl_state_sts =Active

$\log = L$

Adapter must wait for 1us to
see if Protocol Layer requests
PM

SB MSG {LinkMgmt.Adapter0.Req.L1

Adapter must finish the
$p ! s \tan / l p _ { - } s t a l l a c k$
handshake before sending
side band message

$p _ { - } \text { state } _ { - } r e q = L 1$

SB MSG {LinkMgmt.Adapter0.Req.L1}
SB MSG {LinkMgmt.Adapter0.Rsp.L1

$p l \_ s t a t e \_ s t s = L 1$

Adapter must
pl_stallreq/lp_stallack
handshake before sending
side band message

SB MSG {LinkMgmt.Adapter0.Rsp.L1}

$p l \_ s t a t e \_ s t s = L 1$

</figure>

<figure>
<figcaption>Figure 10-23. PM Abort Example</figcaption>

DP Protocol Layer
Die 0

DP Adapter
$D i e \quad 0$

DP Physical layer
Die 0

CHANNEL

UP Physical layer
Die 1

UP Adapter
$D i e \quad 1$

UP Protocol Layer
Die 1

$p l \_ s t a t e \_ s t s = A c t i v e$

pl_state_sts = Active

lp_state_req=Active

$l p \_ s t a t e \_ r e q = L 1 -$

Adapter must wait for 1us to
see if Protocol Layer requests
PM

SB MSG {LinkMgmt.Adapter0.Req.L1}.

Adapter must finish the
pl_stallreq/lp_stallack
handshake before sending
side band message

SB MSG {LinkMgmt.Adapter0.Rsp.PMNAK}

pl_state_sts = Active. PM NAK

lp_state_req=Active

pl_state_sts $= A c t i v e$

</figure>

<figure>
<figcaption>Figure 10-24. PM Exit Example</figcaption>

Protocol Layer
Die 0

Adapter
Die 0

Physical layer
Die 0

CHANNEL

Physical layer
Die 1

Adapter
Die 1

Protocol Layer
$D i e \quad 1$

pl_state_sts = L1

pl_state_sts =L1

$l p \_ s t a t e \_ r e q = A c t i v e$

SB MSG {LinkMgmt.Adapter0.Req.Active}

-pl_state_sts = Retrain

$p l _ { - } r x _ { - } \text { active } _ { - } r e q = 0 - > 1 -$
$P _ { - } r x _ { - } a c t i v e _ { - } s t s = 0 - > 1$

SB MSG {LinkMgmt.AdapterO.Rsp.Active}

lp_state_req=Active

SB MSG {LinkMgmt.Adapter0.Req.Active}

$p l \_ s t a t e \_ s t s = R e t r a i n -$

pl_rx_active_req=0->1-
lp_rx_active_sts $= 0 - > 1$

SB MSG {LinkMgmt.Adapter0.Rsp.Active}

$p l \_ s t a t e \_ s t s = A c t i v e -$

pl_state sts = Active

Adapter opens TX and
moves to Active status once
it has sent and received an
Active Status

Adapter opens TX and
moves to Active status once
it has sent and received an
Active Status

If ARB/MUX exits, it performs the ALMP exchanges with remote ARB/MUX
before moving pl_state_sts to Active for the Protocol Layer

</figure>

# 10.3 Common rules for FDI and RDI

This section covers common set of rules applicable to FDI and RDI and cross-interactions between
them. Any applicable differences are called out as well. To have common terminology for the common
set of rules, Upper Layer is used to refer to Adapter for RDI, and Protocol Layer for FDI. Lower Layer
is used to refer to Physical Layer for RDI and Adapter for FDI.

Because Active.PMNAK is a sub-state of Active, all rules that apply for Active are also applicable for
Active.PMNAK; however the state status cannot move from Active. PMNAK directly to L1 or L2 due to
the rules requiring the Upper Layer to request a transition to Active before requesting PM again.

## 10.3.1 Byte Mapping for FDI and RDI

The Flit Format figures in Chapter 3.0 show examples of how a Flit is laid out on a 64B datapath when
sent over FDI or RDI. Figure 10-25 shows an example of a CXL.io Standard 256B Start Header Flit for
reference. Each Flit takes four data transfers across FDI or RDI when the data width is 64 Bytes. Each
data transfer is referred to a Flit Chunk, numbered in increasing order within an entire Flit transfer.

For every data transfer, the Least Significant Byte from the corresponding Flit Chunk is mapped to
Byte 0 on FDI (or RDI), the next Byte from the Flit is mapped to Byte 1 on FDI (or RDI), and so on.
Within each Byte, bit 0 of the Byte from the Flit maps to bit 0 of the corresponding Byte on FDI (or
RDI), and so on. The same mapping applies for both transmit and receive directions.

For example, in Transfer 0, Byte 0 of the Flit is mapped to Byte 0 of FDI (or RDI), Byte 1 of the Flit is
mapped to Byte 1, and so on. In transfer 1, Byte 64 of the Flit is mapped to Byte 0 of FDI (or RDI),
Byte 65 of the Flit is mapped to Byte 1 of FDI (or RDI) and so on. This example is illustrated in
Figure 10-26. Data transfers follow the rules outlined in Section 10.1.4 for RDI and Section 10.2.4 for
FDI and hence do not necessarily correspond to consecutive clock cycles.

<figure>
<figcaption>Figure 10-25. CXL.io Standard 256B Start Header Flit Format Exampleª</figcaption>

+0

+1

+2

+45

+46

+49

+50

+59

$\frac { 8 } { 4 }$

$+ 6 3$

Byte 0

FH B0b

FH B1b

62B of Flit Chunk 0 (from Protocol Layer)

Byte 64

Flit Chunk 1 64B (from Protocol Layer)

Byte 128

Flit Chunk 2 64B (from Protocol Layer)

Byte 192

46B of Flit Chunk 3 (from Protocol Layer)

DLP B2C

DLP B3c

DLP B4c

DLP B5c

10B
Reserved

C0 B0d

C0 B1d

C1 B0d

C1 B1d

</figure>

a. See Figure 2-1 for color mapping.

b. Flit Header Byte 0 and Byte 1, respectively.

c. DLP Byte 2, Byte 3, Byte 4, and Byte 5, respectively.

d. CRC0 Byte 0, CRC0 Byte 1, CRC1 Byte 0, and CRC1 Byte 1, respectively.

<table>
<caption>Figure 10-26. FDI (or RDI) Byte Mapping for 64B Datapath to 256B Flits</caption>
<tr>
<th rowspan="2">Transfer (Rows)</th>
<th colspan="8">$F D I \left( o r \quad R D I \right) B y t e s$</th>
</tr>
<tr>
<th>0</th>
<th>1</th>
<th>2</th>
<th>...</th>
<th>60</th>
<th>61</th>
<th>62</th>
<th>63</th>
</tr>
<tr>
<td>0</td>
<td>Flit Byte 0</td>
<td>Flit Byte 1</td>
<td>Flit Byte 2</td>
<td>...</td>
<td>Flit Byte 60</td>
<td>Flit Byte 61</td>
<td>Flit Byte 62</td>
<td>Flit Byte 63</td>
</tr>
<tr>
<td>1</td>
<td>Flit Byte 64</td>
<td>Flit Byte 65</td>
<td>Flit Byte 66</td>
<td>...</td>
<td>Flit Byte 124</td>
<td>Flit Byte 125</td>
<td>Flit Byte 126</td>
<td>Flit Byte 127</td>
</tr>
<tr>
<td>2</td>
<td>Flit Byte 128</td>
<td>Flit Byte 129</td>
<td>Flit Byte 130</td>
<td>...</td>
<td>Flit Byte 188</td>
<td>Flit Byte 189</td>
<td>Flit Byte 190</td>
<td>Flit Byte 191</td>
</tr>
<tr>
<td>3</td>
<td>Flit Byte 192</td>
<td>Flit Byte 193</td>
<td>Flit Byte 194</td>
<td>...</td>
<td>Flit Byte 252</td>
<td>Flit Byte 253</td>
<td>$F l i t \quad B y t e \quad 2 5 4$</td>
<td>Flit Byte 255</td>
</tr>
</table>

If the FDI or RDI datapath width is increased (or decreased), the Byte mapping follows the same
convention of increasing order of Flit bytes mapped to increasing order of FDI (or RDI) bytes.
Figure 10-27 shows an illustration of a 128B data path.

<table>
<caption>Figure 10-27. FDI (or RDI) Byte Mapping for 128B Datapath to 256B Flits</caption>
<tr>
<th rowspan="2">Transfer (Rows)</th>
<th colspan="12">FDI (or RDI) Bytes (Columns)</th>
</tr>
<tr>
<th>0</th>
<th>1</th>
<th>2</th>
<th>...</th>
<th>62</th>
<th>63</th>
<th>64</th>
<th>65</th>
<th>...</th>
<th>125</th>
<th>126</th>
<th>127</th>
</tr>
<tr>
<td>0</td>
<td>$\mathrm { F l i t B y t e }$ 0</td>
<td>Flit Byte 1</td>
<td>Flit Byte 2</td>
<td>...</td>
<td>Flit Byte 62</td>
<td>Flit Byte 63</td>
<td>Flit Byte 64</td>
<td>Flit Byte 65</td>
<td>...</td>
<td>Flit Byte 125</td>
<td>Flit Byte 126</td>
<td>Flit Byte 127</td>
</tr>
<tr>
<td>1</td>
<td>$\mathrm { F l i t B y t e }$ 128</td>
<td>$\mathrm { F l i t B y t e }$ 129</td>
<td>$\mathrm { F I i t B y t e }$ 130</td>
<td>...</td>
<td>Flit Byte 190</td>
<td>Flit Byte 191</td>
<td>Flit Byte 192</td>
<td>Flit Byte 193</td>
<td>...</td>
<td>Flit Byte 253</td>
<td>Flit Byte 254</td>
<td>Flit Byte 255</td>
</tr>
</table>

For 68B Flit Formats, the Protocol Layer transfers only 64B of payload information from the Flit over
FDI (the Flit Header and CRC are inserted by the Adapter). Thus, if the datapath is 128B wide, two
such transfers will happen at a given clock cycle as shown in Figure 10-28. The numbering in the
figure still uses the Byte positions relative to the overall Flit, hence Byte 0 corresponds to Flit 0 Byte
2, etc. On the Transmit path, the Protocol Layer inserts empty slots (i.e., bytes with a value of 00h) to
populate the entire width of the bus if the interface width is greater than 64B and there is insufficient
payload information to transmit. The Adapter does the same on the Receive path.

<table>
<caption>Figure 10-28. FDI Byte Mapping for 128B Datapath for 68B Flit Format</caption>
<tr>
<th rowspan="2">Transfer (Rows)</th>
<th colspan="12">FDI Bytes (Columns)</th>
</tr>
<tr>
<th>0</th>
<th>1</th>
<th>2</th>
<th>...</th>
<th>62</th>
<th>63</th>
<th>64</th>
<th>65</th>
<th>…</th>
<th>125</th>
<th>126</th>
<th>127</th>
</tr>
<tr>
<td>0</td>
<td>Flit 0 Byte 2</td>
<td>Flit 0 Byte 3</td>
<td>Flit 0 Byte 4</td>
<td>...</td>
<td>Flit 0 Byte 64</td>
<td>Flit 0 Byte 65</td>
<td>Flit 1 Byte 2</td>
<td>Flit 1 Byte 3</td>
<td>...</td>
<td>Flit 1 Byte 63</td>
<td>Flit 1 Byte 64</td>
<td>Flit 1 Byte 65</td>
</tr>
</table>

For 68B Flit Formats, Adapter inserts the Flit Header and CRC bytes, and performs the necessary
shifting before transferring the bytes over RDI. Thus, if the data path is 128B wide, the byte mapping
will follow as shown in Figure 10-29. The remainder of Flit 1 continues on the next transfer, etc. Given
that the Adapter must insert PDS bytes before pausing the data stream, which makes the transfer a
multiple of 256B, the transfer naturally aligns when the width of RDI is 64B, 128B, or 256B on both
the Transmit and Receive directions. For wider than 256B interfaces, see the Implementation Note
below.

<table>
<caption>Figure 10-29. RDI Byte Mapping for 128B Datapath for 68B Flit Format</caption>
<tr>
<th rowspan="2">Transfer (Rows)</th>
<th colspan="12">RDI Bytes (Columns)</th>
</tr>
<tr>
<th>0</th>
<th>1</th>
<th>2</th>
<th>...</th>
<th>65</th>
<th>66</th>
<th>67</th>
<th>68</th>
<th>...</th>
<th>125</th>
<th>126</th>
<th>127</th>
</tr>
<tr>
<td>0</td>
<td>Flit 0 Byte 0</td>
<td>$F l i t \quad 0$ Byte 1</td>
<td>$F l i t \quad 0$ Byte 2</td>
<td>...</td>
<td>Flit 0 $B y t e \quad 6 5$</td>
<td>Flit 0 Byte 66</td>
<td>Flit 0 Byte 67</td>
<td>Flit 1 Byte 0</td>
<td>...</td>
<td>Flit 1 $B y t e \quad 5 7$</td>
<td>Flit 1 Byte 58</td>
<td>Flit 1 Byte 59</td>
</tr>
<tr>
<td>1</td>
<td>Flit 1 Byte 60</td>
<td>Flit 1 Byte 61</td>
<td>Flit 1 Byte 62</td>
<td></td>
<td></td>
<td>...</td>
<td>...</td>
<td></td>
<td>...</td>
<td>...</td>
<td></td>
<td></td>
</tr>
</table>

The frequency of operation of the interfaces along with the data width determines the maximum
bandwidth that can be sustained across the FDI (or RDI) interface. For example, a 64B datapath at 2
GHz of clock frequency is required to sustain a 16 GT/s Link for an Advanced Package configuration
with a single module. Similarly, to scale to 32 GT/s of Link speed operation for Advanced Package
configuration with a single module, a 128B datapath running at 2 GHz would be required to support
the maximum Link bandwidth.

The FDI (or RDI) byte mapping for the transmit or receive direction does not change for multi-module
configurations. The MMPL logic within the Physical Layer is responsible for ensuring that the bytes are
transmitted in the correct order to the correct module. Any byte swizzling or rearrangement to resolve
module naming conventions, etc., is thus the responsibility of the MMPL logic.

Note that for PCIe and CXL protocols, the 8b/10b or 128b/130b encodings defined in the PCIe Base
Specification are not used when transporting over UCIe.

### IMPLEMENTATION NOTE

#### NBYTES

For Raw Format, the value of NBYTES is vendor-defined. This Implementation Note is for UCIe Flit
mode.

It is strongly recommended that when operating in UCIe Flit mode, NBYTES is chosen to be one of
64, 128, 256, or 512 and is selected to get the best KPI (e.g., latency, area, etc.) for the desired
bandwidth from the UCIe Link. If NBYTES is chosen to be larger than or equal to 512, it is strongly
recommended that it is a multiple of 256 and is only done for the case of a four module Advanced
Package Link designed for 16 GT/s or higher. Data transfer over the Link for all Flit formats defined
in UCIe Flit mode are in a granularity of 256B, so aligning to a multiple of that avoids unnecessary
shifting and corresponding tracking.

For situations in which the RDI or FDI data path is wider than 256B, the following considerations
apply for interoperability:

. On the Transmit side, it is required to send valid data corresponding to the full width of the
interface. For FDI, this would mean the Protocol Layer might need to pack a Protocol Flit with
empty slots. For RDI, this would mean the Adapter might need to insert NOP Flits (for 68B Flit
Format, PDS bytes are also included as valid data for this purpose).

· On the Receive side, for RDI:

It is possible that the Physical Layer has to wait to accumulate sufficient bytes before
transmitting over RDI. The Physical Layer must accumulate data in multiples of 256B and if the
accumulated data is less than the RDI width, it must wait for a sufficient gap in valid data
transfer on the Physical Link (at least 16 UI for differential clock and 32 UI for quadrature clock)
before transmitting this data on RDI. In this scenario, the accumulated data is sent on the lower
significant bytes of the RDI, and any remaining bytes on the interface are assigned to all 0s.
For 256B Flit Formats, a Flit Header which is 0000h with a CRC of 0000h is silently discarded by
the Adapter. It is also not included for the purposes of Runtime Link Testing.

For 68B Flit Formats, the Adapter is expected to keep track of the PDS bytes (because these are
included in Runtime Link Testing). Any extra padding beyond that is silently discarded and not
included for the purposes of Runtime Link Testing.

· On the Receive side, for FDI:

The Adapter must accumulate data in multiples of 256B before forwarding to the Protocol Layer.
If the accumulated data is less than the FDI width, it gets sent on the lower significant bytes of
the FDI, and any remaining bytes on the interface are assigned to 0b.

For 256B Flit Formats, a Flit Header of 0000h is a NOP for the Protocol Layer and is discarded.
For 68B Flit Formats, 00h are IDLE symbols for PCIe/CXL.io or Empty slots for CXL.cachemem,
both of which get discarded by the Protocol Layer. For Streaming protocols that use 68B Flit
Formats, it is recommended to use the same approach.

· lp_corrupt_crc, pl_flit_cancel, and pl_error apply to all the Flits that are transferred
at the corresponding clock cycle. If applicable, it is recommended to set NDLLP to 32 for these
applications and limit the DLLP throughput to be 1 per clock cycle on FDI.

## 10.3.2 Stallreq/Ack Mechanism

The Stallreq/Ack mechanism is used by the Lower Layer to interrupt the Flit transfers by the Upper
Layer at a Flit boundary. On RDI, the Stallreq/Ack mechanism must be used when exiting Active state
to Retrain, PM, LinkReset or Disabled states. On FDI, for UCIe Raw Format, the Stallreq/Ack
mechanism must be used when exiting Active state to Retrain, PM, LinkReset or Disabled states. On
FDI, for UCIe Flit Mode, the Stallreq/Ack mechanism must only be used when exiting Active State to a
PM state. For other scenarios that exit Active state for UCIe Flit mode, the Adapter must simply de-
assert pl_trdy at a Flit boundary before state transition.

The Stallreq/Ack mechanism is mandatory for all FDI and RDI implementations. lp_stallack
assertion implies that Upper Layer has stalled its pipeline at a Flit aligned boundary.

The pl_stallreq/lp_stallack handshake is a four-phase sequence that follows the rules below:

1\. The pl_stallreq and lp_stallack must be de-asserted before domain reset exit.

2\. A rising edge on pl_stallreq must only occur when lp_stallack is de-asserted.

3\. A falling edge on pl_stallreq must only occur when lp_stallack is asserted or when the
domain is in reset.

4\. A rising edge on lp_stallack must only occur when pl_stallreq is asserted. lp_stallack
must only be asserted after the data stream reaches a clean boundary. For the case of the
Adapter asserting lp_stallack to the Physical Layer for 68B Flit Formats, this requires that
PDS, as well as the corresponding padding of Os and any parity bytes injected, has been
transmitted. For 256B Flit Formats, the clean boundary aligns with a Flit boundary.

5\. A falling edge on lp_stallack must only occur when pl_stallreq is de-asserted or when
domain is in reset.

6\. When lp_stallack is asserted lp_valid and lp_irdy must both be de-asserted.

7\. While pl_stallreq is asserted, any data presented on the interface must be accepted by the
physical layer until the rising edge of lp_stallack. pl_trdy is not required to be asserted
consecutively.

8\. The logic path between pl_stallreq and lp_stallack must contain at least one flip-flop to
prevent a combinatorial loop.

9\. A complete stallreq/stallack handshake is defined as the completion of all four phases: Rising
edge on pl_stallreq, rising edge on lp_stallack, falling edge on pl_stallreq, falling
edge on lp_stallack.

10\. It is strongly recommended that Upper Layer implements providing lp_stallack on a global
free running clock so that it can finish the handshake even if the rest of its logic is clock gated.

To avoid performance penalties, it is recommended that this handshake be completed as quickly as
possible while satisfying the above rules.

### IMPLEMENTATION NOTE

In multiple places within this specification, for state transitions, it is referring to
completing the Stallreq/Ack handshake before the state transition. In the context of
state transitions, there are two acceptable ways to implement this from the lower
layer:

· One implementation from the lower layer would follow the sequence:

i. Assert pl_stallreq.

ii. After lp_stallack is asserted, perform the necessary actions for state
transition (including deassertion of pl_trdy and the update of
pl_state_sts).

iii. De-assert pl_stallreq. Once lp_stallack de-asserts, the state
transition is considered complete.

· The alternate implementation from the lower layer would follow the sequence:

i. Assert pl_stallreq.

ii. After lp_stallack is asserted, de-assert pl_trdy.

iii. De-assert pl_stallreq and subsequently perform the necessary
actions for state transition and the update of pl_state_sts.

State transition is considered complete after pl_state_sts update and
lp_stallack de-assertion.

## 10.3.3 State Request and Status

Table 10-4 describes the Requests considered by the Lower layer in each of the interface states. The
Upper layer must take into account the interface state status and make the necessary request
modifications.

The requests are listed on the Row and the state status is listed in the Column.

The entries in Table 10-4 denote the following:

. Yes: Indicates that the request is considered for next state transition by the lower layer.

· N/A: Not Applicable

. Ignore: Indicates that the request is ignored and has no effect on the next state transition.

<table>
<caption>Table 10-4. Requests Considered in Each State by Lower Layer</caption>
<tr>
<th>Request (Row) Versus Status (Column)</th>
<th>Reset</th>
<th>Active</th>
<th>L1</th>
<th>LinkReset</th>
<th>Retrain</th>
<th>Disable</th>
<th>L2</th>
<th>LinkError</th>
</tr>
<tr>
<td>NOP</td>
<td>Yes</td>
<td>Ignore</td>
<td>Ignore</td>
<td>Ignore</td>
<td>Ignore</td>
<td>Ignore</td>
<td>Ignore</td>
<td>Ignore</td>
</tr>
<tr>
<td>Active</td>
<td>$\mathrm { Y e s } ^ { \mathrm { a } }$</td>
<td>Ignoreb</td>
<td>Yes</td>
<td>Yes</td>
<td>Yes</td>
<td>Yes</td>
<td>Yes</td>
<td>Yes</td>
</tr>
<tr>
<td>L1</td>
<td>Ignore</td>
<td>Yes</td>
<td>Ignore</td>
<td>Ignore</td>
<td>Ignore</td>
<td>Ignore</td>
<td>Ignore</td>
<td>Ignore</td>
</tr>
<tr>
<td>LinkReset</td>
<td>Yesª</td>
<td>Yes</td>
<td>Yes</td>
<td>Ignore</td>
<td>Yes</td>
<td>Ignore</td>
<td>Yes</td>
<td>Ignore</td>
</tr>
<tr>
<td>Retrain</td>
<td>Ignore</td>
<td>Yes</td>
<td>Ignore</td>
<td>Ignore</td>
<td>Ignore</td>
<td>Ignore</td>
<td>Ignore</td>
<td>Ignore</td>
</tr>
<tr>
<td>Disable</td>
<td>Yesª</td>
<td>Yes</td>
<td>Yes</td>
<td>Yes</td>
<td>Yes</td>
<td>Ignore</td>
<td>Yes</td>
<td>Ignore</td>
</tr>
<tr>
<td>L2</td>
<td>Ignore</td>
<td>Yes</td>
<td>Ignore</td>
<td>Ignore</td>
<td>Ignore</td>
<td>Ignore</td>
<td>Ignore</td>
<td>Ignore</td>
</tr>
<tr>
<td>$\begin{array}{} { \text { LinkError } } \\ { \text { \left(sideband wire\right) } } \end{array}$</td>
<td>Yes</td>
<td>Yes</td>
<td>Yes</td>
<td>Yes</td>
<td>Yes</td>
<td>Yes</td>
<td>Yes</td>
<td>Yes</td>
</tr>
</table>

a. Requires request transition from NOP

b. If the Status is Active. PMNAK, then the Lower Layer transitions to Active upon sampling the Active Request.

### 10.3.3.1 Reset State rules

The Reset State can be entered on de-assertion of interface reset signal or from LinkReset/Disable/
LinkError/L2 states. In Reset state, the physical layer is permitted to begin its initialization/training
process.

The pl_state_sts is not permitted to exit Reset state until requested by the upper layer. The exit
from Reset state is requested by the upper layer by changing the Ip_state_req signal from NOP
encoding value to the permitted next state encoding value.

The rules for Reset state transition are as follows:

1\. Reset->Active: The lower layer triggers transitions to the Active state upon observing
lp_state_req == Reset (NOP) for at least one clock while pl_state_sts is indicating Reset
followed by observing lp_state_req == Active. The transition to Active is only completed once
the corresponding Active Entry handshakes have completed on the Link. For RDI, it is when the
Physical Layer has sent and received an Active Response sideband message to and from the
remote Physical Layer respectively. For the Adapter LSM, it is when the Adapter has sent and
received an Active Status sideband message to and from the remote Adapter respectively. For the
ARB/MUX vLSM, it is when the ARB/MUX has sent and received an Active Status ALMP to and from
the remote ARB/MUX respectively.

2\. Reset->LinkReset: The lower layer transitions to the LinkReset state upon observing
lp_state_req == Reset (NOP) for at least one clock while pl_state_sts is indicating Reset
followed by observing lp_state_req = = LinkReset OR when requested by remote Link partner
through the relevant sideband message. The lower layer is permitted to transition through Active
State, and when it does, Active state exit conditions apply.

3\. Reset->Disabled: The lower layer transitions to the Disabled state upon observing 1p_state_req
== Reset (NOP) for at least one clock while pl_state_sts is indicating Reset followed by
observing lp_state_req == Disabled OR when requested by the remote Link partner through
the relevant sideband message. The lower layer is permitted to transition through Active State,
and when it does, Active state exit conditions apply.

4\. Reset->LinkError: The lower layer transitions to LinkError based on observing an internal request
to move to the LinkError or lp_linkerror assertion. For RDI, this transition is permitted if
requested by the remote Link partner through the relevant sideband message.

### 10.3.3.2 Active State rules

The Active state to next state transitions are described below.

The rules for Active State transition are as follows:

1\. Active->Retrain: The Lower layer transitions to the Retrain state upon observing 1p_state_req
== Retrain or due to an internal request to retrain the Link while pl_state_sts == Active. This
arc is not applicable for CXL vLSMs exposed on FDI (CXL Flit Mode with Retry in the Adapter).

2\. Active->L1: The physical layer transitions to L1 based on observing 1p_state_req == L1 while
in the Active state, if other conditions of PM entry have also been satisfied.

3\. Active->L2: The physical layer transitions to L2 based on observing 1p_state_req == L2 while
in the Active state, if other conditions of PM entry have also been satisfied.

It is permitted to have an Active.PMNAK to Retrain/LinkReset/Disable/LinkError transition for cases
where Lower Layer is waiting for the Upper Layer to change the request to Active and the
corresponding Link event triggers it. There is no scenario where there is a transition from
Active. PMNAK to L1 or L2.

Section 10.3.3.8 describes the transition from Active or Active.PMNAK to LinkReset, Disable, or
LinkError states.

### 10.3.3.3 PM Entry/Exit Rules

See the PM entry and exit sequences in the RDI and FDI sections.

### 10.3.3.4 Retrain State Rules

Adapter requests Retrain on RDI if any of the following events occur:

· Software writes to the Retrain bit and the Link is in Active state.

· Number of CRC or parity errors detected crosses a threshold. The specific algorithm for
determining this is implementation specific.

· Protocol Layer requests Retrain (only applicable for UCIe Raw Format).

· any other implementation specific condition (if applicable).

Physical Layer triggers a Retrain transition on RDI if:

· Valid framing errors are observed

· Remote Physical Layer requests Retrain entry

· Adapter requests Retrain

Protocol Layer must not request Retrain on FDI, unless UCIe is operating in UCIe Raw Format.

A Retrain transition on RDI must always be propagated to Adapter LSMs that are in Active. Retrain
transitions of the UCIe Link are not propagated to CXL vLSMs. Upon Retrain entry, the credit counter
for UCIe Retimer (if present) must be reset to the value advertised during initial Link bring up (the
value is given by the "Retimer_Credits" Parameter in the {AdvCap.Adapter} sideband message during
initial Link bring up). The Retimer must drain or dump any Flits in flight or its internal transport
buffers upon entry to Retrain. Additionally, the Retimer must trigger Retrain of the remote UCIe Link
(across the Off-Package Interconnect).

Entry into Retrain state resets power management state for the corresponding state machine, and
power management entry if required must be re-initiated after the interface enters Active state. If

there was an outstanding PM request that returns PM Response, the corresponding state machine
must perform Active Entry handshakes to bring that state machine back to Active.

The rules for Retrain state transition are as follows:

1\. Retrain->Active: If Retrain was entered from L1, the lower layer begins Active Entry handshakes
upon observing lp_state_req == Active while the pl_state_sts == Retrain or L1. If Retrain
was entered from Active, the lower layer begins Active Entry handshakes only after observing a
NOP-> Active transition on lp_state_req. Lower layer transitions to Active once the
corresponding Active Entry handshakes have completed. Exit from Retrain on RDI requires the
Active Entry handshakes to have completed between Physical Layers. Exit from Retrain on FDI
must ensure that RDI has moved back to Active, and Active Entry handshakes have successfully
completed between Adapters (for the Adapter LSM).

2\. Transitional state: The lower layer is permitted to transition to the Active state upon observing
lp_state_req == LinkReset or Disabled while the pl_state_sts == Retrain. Following the
entry into Active the lower layer is permitted to make a transition to the requested state.

Section 10.3.3.8 describes Retrain exit to LinkReset, Disable, or LinkError states.

Note:
The requirement to wait for NOP->Active transition ensures that the Upper Layer has a
way to delay Active transition in case it is waiting for any relevant sideband handshakes
to complete (for example the Parity Feature handshake).

## 10.3.3.5 LinkReset State Rules

LinkReset is used for reset flows (HotReset equivalent in PCIe, Protocol Layer must use this to
propagate SBR to the device as well) to convey device and/or Link Reset across the UCIe Link.

Adapter triggers LinkReset transition upon observing a LinkReset request from the Protocol Layer, OR
on receiving a sideband message requesting LinkReset entry from the remote Link partner OR an
implementation specific internal condition (if applicable). Implementations must make best efforts to
gracefully drain the Retry buffers when transitioning to LinkReset, however, entry to LinkReset must
not timeout on waiting for the Retry buffer to drain. The Protocol Layer and Adapter must drain/flush
their pipelines and retry buffer of the Flits for the corresponding Protocol Stack once the FDI state
machines have entered LinkReset.

If all the FDI state machines and Adapter LSMs are in LinkReset, the Adapter triggers RDI to enter
LinkReset as well.

The rules for LinkReset State transitions are as follows:

1\. LinkReset->Reset: The lower layer transitions to the Reset state due to an internal request to
move to Reset (example reset pin trigger) or lp_state_req == Active while pl_state_sts
== LinkReset and all necessary actions with respect to LinkReset have been completed.

2\. LinkReset->Disabled: The lower layer transitions to Disabled based on observing 1p_state_req
== Disabled or due to an internal request to move to Disabled while pl_state_sts ==
LinkReset.

3\. Transitional State: The PHY is permitted to transition through Reset State, and when it does,
Reset state exit conditions apply.

4\. LinkReset->LinkError: The lower layer transitions to LinkError due to an internal request to move
to LinkError or lp_linkerror assertion while pl_state_sts == LinkReset.

## 10.3.3.6 Disabled State Rules

Adapter triggers Disabled entry when any of the following events occur:

· Protocol Layer requests entry to Disabled state

· Software writes to the Link Disable bit corresponding to the underlying Protocol (e.g., the Link
Disable bit in the Link Control register in PCIe)

· Remote Link partner requests entry to Disabled state through the relevant sideband message

· An implementation specific internal condition (if applicable)

Implementations must make best efforts to gracefully drain the Retry buffers when transitioning to
Disabled, however, entry to Disabled must not timeout on waiting for the Retry buffer to drain. The
Protocol Layer and Adapter must drain/flush their pipelines and retry buffer of the Flits for the
corresponding Protocol Stack once the FDI state machines have entered Disabled.

If all the FDI state machines and Adapter LSMs are in Disabled, the Adapter triggers RDI to enter
Disabled as well.

The rules for Disabled State are as follows:

· Disabled->Reset: The lower layer transitions to the Reset state due to an internal request to move
to Reset (example reset pin trigger) or lp_state_req == Active while pl_state_sts ==
Disabled and all necessary actions with respect to Disabled transition have completed.

· Disabled->LinkError: The lower layer transitions to LinkError due to an internal request to move to
LinkError or lp_linkerror assertion while pl_state_sts == Disabled.

## 10.3.3.7 LinkError State Rules

The lower layer enters LinkError state when directed by an lp_linkerror signal or due to Internal
LinkError conditions. For RDI, the entry is also triggered if the remote Link partner requested
LinkError entry through the relevant sideband message. It is not required to complete the stallreq/ack
handshake before entering this state. However, for implementations where LinkError state is not a
terminal state (terminal implies SoC needs to go through reset flow after reaching LinkError state), it
is expected that software can come and retrain the Link after clearing error status registers, etc., and
the following rules should be followed:

. If the lower layer decides to perform a pl_stallreq/lp_stallack handshake, it must provide
pl_trdy to the upper layer to drain the packets. In cases where there is an uncorrectable
internal error in the lower layer, these packets could be dropped and not transmitted on the Link.

. It is required for the upper layer to internally clean up the data path, even if pl_trdy is not
asserted and it has sampled LinkError on pl_state_sts for at least one clock cycle.

The lower layer may enter LinkError state due to Internal LinkError requests such as when:

· Encountering uncorrectable errors due to hardware failure or directed by Upper Layer

· Remote Link partner requests entry into LinkError (RDI only)

The rules for LinkError state are as follows:

· LinkError->Reset: The lower layer transitions to Reset due to an internal request to move to Reset
(e.g., reset pin assertion, or software clearing the error status bits that triggered the error) OR
(lp_state_req == Active and lp_linkerror = 0, while pl_state_sts == LinkError AND
minimum residency requirements are met AND no internal condition such as an error state
requires the lower layer to remain in LinkError). Lower Layer must implement a minimum
residency time in LinkError of 16 ms to ensure that the remote Link partner will be forced to enter
LinkError due to timeouts (to cover for cases where the LinkError transition happened and
sideband was not functional).

## 10.3.3.8 Common State Rules

This section covers some of the common conditions for exit from Active, Retrain, L1, and L2 to
LinkReset, Disable and LinkError states. For RDI, PM encoding and rules correspond to L1 in the text
below.

The rules are as follows:

· [Active, Retrain, L1, L2]->LinkReset: The lower layer transitions to LinkReset based on observing
lp_state_req == LinkReset or due to an internal request to move to LinkReset or the remote
Link partner requesting LinkReset over sideband.

· [Active, Retrain, L1, L2]->Disabled: The lower layer transitions to Disabled based on observing
lp_state_req == Disabled or due to an internal request to move to Disabled while
pl_state_sts == Active, or the remote Link partner requesting Disabled over sideband.

· [Active, Retrain, L1, L2]->LinkError: The lower layer transitions to LinkError based on observing
an internal request to move to the LinkError or lp_linkerror assertion, or the remote Link
partner requesting LinkError over sideband. RDI must move to LinkError before propagating
LinkError to all Adapter LSMs.

From a state machine hierarchy perspective, it is required for Adapter LSM to move to LinkReset,
Disabled or LinkError before propagating this to CXL vLSMs. This ensures CXL rules are followed
where these states are "non-virtual" from the perspective of CXL vLSMs.

Adapter LSM can transition to LinkReset or Disabled without RDI transitioning to these states. In the
case of multi-protocol stacks over the same Physical Link/Adapter, each Protocol can independently
enter these states without affecting the other protocol stack on the RDI.

If all the Adapter LSMs have moved to a common state of LinkReset/Disabled or LinkError, then RDI is
taken to the corresponding state. If however, the Adapter LSMs are in different state combinations of
LinkError, Disabled or LinkReset, the RDI is moved to the highest priority state. The priority order
from highest to lowest is LinkError, Disabled, LinkReset. For a LinkError/LinkReset/Disabled transition
on RDI, Physical Layer must initiate the corresponding sideband handshake to transition remote Link
partner to the required state. If no response is received from remote Link partner for this message
after 8ms, RDI transitions to LinkError.

If RDI moves to a state that is of a higher priority order than the current Adapter LSM, it is required
for the Adapter to propagate that to the Adapter LSM using sideband handshakes to ensure the
transition with the remote Link partner.

After transition from LinkError/LinkReset/Disable to Reset on RDI, the Physical Layer must not begin
training unless the Physical Layer observes a NOP->Active transition on lp_state_req from the
Adapter or observes one of the Link Training triggers defined in Chapter 4.0. The Adapter should not
trigger NOP->Active unless it receives this transition from the Protocol Layer or has internally decided
to bring the Link Up. The Adapter must trigger this on RDI if the Protocol Layer has triggered this

even if pl_inband_pres = 0. Thus, if the Protocol Layer is waiting for software intervention and
wants to hold back the Link from training, it can delay the NOP->Active trigger on FDI. Upper Layers
are permitted to transition lp_state_req back to NOP after giving the NOP->Active trigger in order
to clock gate while waiting for pl_inband pres to assert.

If RDI transitions to L2, the exit is through Reset, and complete Link Initialization and Training flow
will occur (including a fresh Parameter Exchange for the Adapter). After transition from L2 to Reset on
RDI, the LTSM will begin the Link PM exit and retraining flow when a {LinkMgmt.RDI.Req.Active}
sideband message is received or when the Adapter requests Active on RDI or it observes one of the
Link Training triggers defined in Chapter 4.0.

If the Adapter LSM transitions to L2, but RDI does not go to a Link down state (i.e. Reset, LinkReset,
Disabled, LinkError), then this is a "virtual" L2 state. The exit from L2 for the Adapter LSM in this case
will go through Reset for the Adapter LSM, but it does not result in a fresh Parameter Exchange for
the Adapter, and the protocol parameters and the Flit Formats remain the same as prior to L2 entry.
An example of this is if there are multiple stacks on the same Adapter, and only one of the FDIs
transitions to L2.

# IMPLEMENTATION NOTE

## LinkReset/Disabled

LinkReset and Disabled flows are primarily provided as a means to notify the remote Link partner
that the corresponding Protocol Layer intends to trigger the set of actions defined for these by the
underlying protocol (e.g., in the case of PCIe and CXL, both of these result in a Conventional Reset
on the Upstream Port as defined in the PCIe Base Specification). These are typically controlled and
co-ordinated through software/firmware. Note that regardless of protocol, there is no hardware
mechanism from the UCIe Adapter or Physical Layer to guarantee quiescence or graceful draining of
transactions for the LinkReset or Disabled transitions. If this is required by the underlying protocol,
it must be handled through software/firmware or other implementation-specific mechanisms outside
the UCIe Adapter and Physical Layer.

If the RDI state is already in a Link down state (i.e., Reset, LinkReset, Disabled, LinkError) and the
Link is not currently training (Adapter can infer this from pl_phyinrecenter), then there is no
need to notify the remote Link partner. Adapter or Physical Layer can complete the state transitions
locally for this case. If RDI is in RESET and the Link is training, it is recommended to wait for
training to complete before triggering a state transition with the remote Link partner to LinkReset or
Disabled.

The following is written for Disabled state, but applies to both Disabled and LinkReset states.

. For PCIe or CXL protocols, the Downstream Port initiates the transition to Disabled. Because the
Upstream Port goes through a Conventional Reset after transitioning to Disabled, the Upstream
Port waits for Downstream Port to re-initiate Link Training once the corresponding SoC reset
flow has finished.

· For Streaming protocols,

\- The initiating Protocol Layer transitions lp_state_req to Disabled. If the necessary
conditions are met from the Adapter perspective (for example, attempting to drain the Retry
buffer etc.), it forwards the request using the corresponding sideband message to the
remote Link partner's Adapter.

\- On the remote Link partner, the Adapter transitions pl_state_sts to the requested state
once the necessary conditions are met from the Adapter perspective (for example,
attempting to drain the Retry buffer etc.). It also sends the corresponding sideband
message response.

If the Adapter needs to take the RDI to Disabled state, it is recommended to keep FDI
pl_state_sts in Disabled state until that flow has completed. Otherwise, if the exit
conditions for Disabled are met, it is permitted to transition to Reset state on FDI.

Following this, the Protocol Layer on the remote Link partner in turn is permitted bring the
FDI state back to Disabled if required by the underlying protocol. The Adapter must not
trigger another sideband handshake for this scenario.

\- The initiating Adapter transitions pl_state_sts to Disabled upon receiving the sideband
message response.

\- The Protocol Layers on either side of the Link can initiate an exit flow by requesting Active
when pl_state_sts is Disabled, followed by a NOP->Active transition after the
pl_state_sts is Reset.

· For configurations in which the Adapter is servicing multiple Protocol Layers, the Disabled or
LinkReset handshakes are independent per Protocol Layer. In case the Adapter LSM has
transitioned to Reset from Disabled or LinkReset for a given Protocol Layer, the Adapter must
keep track of the most-recent previous state to determine the correct resolution for RDI state
request.

### 10.3.4 Vendor-defined Signals

Optional Vendor-defined signals are provided for implementations.

One use case for such signals is when protocols mapped to UCIe Raw Format would benefit from
repurposing the Retimer credit encodings transmitted over the TXVLD/RXVLD pair of bumps on a UCIe
Link to transmit an additional bit of vendor-defined information for every 8 UI of transfer per module.
This information could be used for synchronization markers, ECC, etc .; the mapping of protocol-
specific information to these encodings and when they are used is beyond the scope of this
specification. Table 10-5 lists the TXVLD/RXVLD encodings and associated bit encodings.

<table>
<caption>Table 10-5. Mapping of Vendor-defined Bits that Use TXVLD/RXVLD Encodings</caption>
<tr>
<th>TXVLD/RXVLD Encoding</th>
<th>lp_vendor_defined/ pl_vendor_defined Bit Encoding</th>
<th>lp_valid/pl_valid Bit Encoding</th>
</tr>
<tr>
<td>0000 0000b</td>
<td>0</td>
<td>0</td>
</tr>
<tr>
<td>0000 1111b</td>
<td>0</td>
<td>1</td>
</tr>
<tr>
<td>1111 1111b</td>
<td>1</td>
<td>1</td>
</tr>
</table>

Similar to Retimer encodings, receivers are permitted to correct for single-bit errors on the received
RXVLD encoding.

To enable interoperability, implementations that target applications such as mapping protocols like
JESD204E over UCIe Raw Format are strongly recommended to follow these rules:

· The lp_vendor_defined and pl_vendor_defined signals are only relevant when 1p_valid
and pl_valid are asserted, respectively (see Table 10-5 for the encodings and Figure 10-30 for
an example).

· The lp_vendor_defined and pl_vendor_defined signals are pipeline matched with
lp_data and pl_data, respectively, such that they convey the encoding transmitted over
TXVLD/RXVLD for the corresponding 8 UI of data.

· In a multi-module Link, each module independently transmits or receives information using these
encodings over its TXVLD/RXVLD pair of bumps.

\- The lp_vendor_defined and pl_vendor_defined signals provide one bit for every 8 UI
on the TXVLD and RXVLD bumps for every module that is part of the UCIe Link. Thus, the
value of the "VS" parameter (i.e., the width of the 1p_vendor_defined or
pl_vendor_defined signals) is a function of the number of modules in the Link as well as
the width of the corresponding lp_data or pl_data signals, respectively (see Table 10-6 for
examples of different configurations).

. The lp_retimer_crd and pl_retimer_crd signals are not applicable in this mode of operation
and will never assert for this application.

<table>
<caption>Table 10-6. Example Configurations and Widthsª</caption>
<tr>
<th>Number of Modules in Link and Per-module Width</th>
<th>RDI or FDI Width</th>
<th>"VS" Parameter</th>
<th>Description</th>
</tr>
<tr>
<td>$4 \times 1 6$</td>
<td>$6 4 B$</td>
<td>4 (num modules)</td>
<td>· Bit 0 is for Module 0 · Bit 1 is for Module 1 · Bit 2 is for Module 2 · Bit 3 is for Module 3</td>
</tr>
<tr>
<td>$4 \times 1 6$</td>
<td>128B</td>
<td>$8 \left( n u m \quad m o d u l e s * 2 \right)$</td>
<td>· Bits 0, 4 are for Module 0 · Bits 1, 5 are for Module 1 · Bits 2, 6 are for Module 2 · $B i t s \quad 3 , 7 \quad a r e \quad f o r \quad M o d u l e \quad 3$ · For each module: - The lower index bit is for alternate valid frames starting from the first valid frame after reaching Active state - The higher index is for alternate valid frames starting from the second valid frame after reaching Active</td>
</tr>
</table>

a. The examples provided in this table are for UCIe-S; however, UCIe-A configurations are also permitted.

Figure 10-30 illustrates an example of byte transfer on the Rx for one Lane of a Module. The same
can be extended to multiple Lanes for each Module, and in the case of multiple modules, each Module
interprets the received encoding and drives that encoding on the corresponding

pl_vendor_defined signal. In the figure, during UCIe Link Clock 0 through 7, Byte 0 (B0) and Byte
1 (B1) are received on UCIe Data Lane 0. The encodings received on RXVLD indicate that both of
those bytes are valid. The encodings received on RXVLD also indicate that the vendor-defined data
received has a value of 0 corresponding to B0, followed by a value of 1 for B1. As shown in
Figure 10-30, the Physical Layer presents the de-serialized data bytes on pl_data_byte0 and the
vendor-defined data on pl_vendor_defined[0] signals on RDI at the corresponding lclk cycles.
The latency from data received until the data appears on the RDI interface, as well as the Iclk to UCIe
Link clock ratio, might differ from the example shown in Figure 10-30, depending on implementation
details.

Figure 10-30. Example of Byte Transfer on the Rx for One Lane of a Module

<figure>

x

0

1

2

3

4

5

UCle Link Clock

6

7

8

x
☒

x
☒

x
☒

x
☒

x
☒

UCle RXVLD

UCle Data Lane 0

BO[0]

BO[1]

BO[2]

BO[3]

BO[4]

BO[5]

BO[6]

BO[7]

B1[0]

B1[1]

B1[2]

B1[3]

B1[4]

B1[5]

B1[6]

B1[7]

0

Iclk RDI

pl_data byte0[7:0]

00h

BO[7:0]

00h

B1[7:0]

$\mathrm { p l } \_ \mathrm { v a l i d }$

00h

pl_vendor_defined[0]

</figure>

#### 10.3.5 Example Flow Diagrams

##### 10.3.5.1 LinkReset Entry and Exit

Figure 10-31 shows an example flow for LinkReset entry and exit. In the multi-protocol stack
scenario, it is permitted for each protocol stack to independently transition to LinkReset. RDI is only
transitioned to LinkReset if all the corresponding Adapter LSMs are in LinkReset. For the Link Down
Event box, it is expected that SoC does not trigger the overall reset flow until the Physical Layer has
completed all the relevant sideband handshakes with the remote Link partner that ensure the LTSM is
also in Reset state.

Figure 10-31 also shows the link reset flow for a PCIe/CXL.io protocol. If Management Transport
protocol is supported and negotiated on the same stack as PCIe/CXL.io protocol, the Management
Port Gateway must still follow the LinkReset flow and reset requirements that correspond to PCIe/
CXL.io.

<figure>
<figcaption>Figure 10-31. LinkReset Example</figcaption>

DP Protocol Layer
Die 0

DP Adapter
Die 0

DP Physical layer
Die 0

CHANNEL UP Physical layer

UP Adapter
Die 1

Die 1

UP Protocol Layer
Die 1

pl_state_sts = Active

$p l _ { - }$ = Active

Software set SBR = 1

Ip_state_req=LinkReset-

SB

3MSG {LinkMgmt.Adapter0.Req.LinkReset}

SB MSG {LinkMgmt.Adapter0.Rsp.LinkReset}

pl_state_sts = LinkReset-

Link Down Event, Protocol
$L a y e r \quad i s \quad p e r m i t t e d \quad t o \quad r e s e t$
upper layers

$p l \_ s t a t e \_ s t s = L i n k \quad R e s e t$

Ip_state_req=LinkReset

SB MSG {LinkMgmt.RDI.Req.LinkReset}

pl_state_sts=LinkReset]

$p l \_ s t a t e \_ s t s = L i n k R e s e t$

SB MSG {LinkMgmt.RDI.Rsp.LinkReset}

Link Down Event, resets
device

pl_state_sts=Reset

Software clear SBR = 1

Ip_state_req=Active

lp_state_req=Active-

Reset flow completed, Link Training State Machine is in Reset waiting for
sideband init pattern from DP

$p l \_ s t a t e \_ s t s = R e s e t -$

pl_state_sts = Reset-

Ip_state_req=NOP->Active]

lp_state_req=NOP->Activel

Start Link Training

</figure>

##### 10.3.5.2 LinkError

Figure 10-32 shows an example of LinkError entry and exit when the Protocol Layer detected an
uncorrectable internal error.

<figure>
<figcaption>Figure 10-32. LinkError example</figcaption>

DP Protocol Layer
Die 0

DP Adapter
$D i e \quad 0$

DP Physical layer
$\mathrm { D i e } 0$

CHANNEL

UP Physical layer
Die 1

UP Adapter
Die 1

UP Protocol Layer
Die 1

pl_state_sts = Active

pl_state_sts = Active

Protocol Layer detected UIE
It keeps the Link in LinkError
as long as required. For
example, in the case of
Downstream Port
Containment (DPC), it is as
long as the DPC Status is not
cleared by software.

Ip_linkerror=1

Ip_linkerror=1

SB MSG {LinkMgmt.RDI.Req.LinkError}

SB MSG {LinkMgmt.RDI.Rsp.LinkError}

pl_state_sts = LinkError]

pl_state_sts = Linkerror

pl_state_sts = Link Error

pl_state_sts = LinkError

Link Down Event, resets
device

pl_state_sts=Reset

pl_state_sts=Reset

Any transition from Link
Disable to Link Enable or Link
SBR asserted to deasserted
should trigger Protocol Layer
to perform Link bring up
sequence.

$I p \_ s t a t e \_ r e q = A c t i v e$
$I p \_ l i n k e r r o r = 0$

Reset flow completed, Link Training State Machine is in Reset
waiting for sideband init pattern from DP

$1 0$ Ip_state_req=Active-

$p l \_ s t a t e \_ s t s = R e s e t$

pl_state_sts = Reset-

Ip_state_req=NOP->Active

Ip_state_req=NOP->Active

Start Link Training

</figure>

##### 10.3.5.3 Example of L2 Cross Product with Retrain on RDI

Figure 10-33 shows an example of L2 entry cross product with Retrain transition on RDI (i.e., both
flows happen to overlap in a meaningful way) and the corresponding events to resolve the state on
either side of the Link.

<figure>
<figcaption>Figure 10-33. Example of L2 Cross Product with Retrain on RDI</figcaption>

Protocol Layer
Die 0

Adapter
Die 0

Physical layer
Die 0

CHANNEL

Physical layer
$D i e \quad 1$

Adapter
Die 1

Protocol Layer
$D i e \quad 1$

pl_state_sts =
Active

pl_state_sts =
Active

lp_state_req=L2

$l p \_ s t a t e \_ r e q = L 2 -$

SB MSG {LinkMgmt.Adapter0.Req.L2

pl_state_sts =
Retrain

Adapter LSM is L2

SB MSG {LinkMgmt.Adapter0.Rsp.L2}

Adapter LSM is Retrain

Adapter LSM is L2

pl_state_sts =
Retrain

SB MSG {LinkMgmt.Adapter0.Req.L2}

SB MSG {LinkMgmt.Adapter0.Rsp.PMNAK}

RDI Retrain exit flow

pl_state_sts =
Active

pl_state_sts =
Active

lp_state_req=NOP->Active

Adapter LSM is Retrain

Adapter LSM is Reset

SB MSG {LinkMgmt.Adapter0.Req.Active}

$l p \_ s t a t e \_ r e q = N O P - > A c t i v e$

SB MSG {LinkMgmt.AdapterO.Rsp.Active}

SB MSG {LinkMgmt.Adapter0.Req.Active}

SB MSG {LinkMgmt.Adapter0.Rsp.Active}

Adapter LSM is Active

Adapter LSM is Active

Regular L2 entry flow can begin if L2 entry conditions are met

</figure>

##### 10.3.5.4 L2 Exit Example for RDI

<figure>
<figcaption>Figure 10-34. L2 Exit Example for RDI</figcaption>

Adapter
Die 0

Physical layer
Die 0

CHANNEL

Physical layer
Die 1

Adapter
Die 1

pl_state_sts = L2

$p l \_ s t a t e \_ s t s = L 2$

lp_state_req=Active

SB MSG {LinkMgmt. RDI. Req.Active}

$p ! \text { state } _ { - } s t s = \text { Reset }$
$p l _ { - }$

pl_inband_pres = 0b

LTSM is in LinkInit

LTSM is in LinkInit

pl_inband_pres = 1b

SB MSG {LinkMgmt. RDI.Req.Active}

lp_state_req=NOP->Active

$p l \_ s t a t e \_ s t s = R e s e t -$

$p l \_ i n b a n d \_ p r e s = 1 b$

Ip_state_req=NOP->Active

SB MSG {LinkMi ~+ RDI. Rs p. Active }
{LinkMgmt.RDI. $\left. . \mathrm { R s } \mathrm { p } . \mathrm { A c t i v e } \right\}$

Ti

LTSM is in Active

LTSM is in Active

$p l \_ s t a t e \_ s t s = A c t i v e$

pl_state_sts = Active

☐
$| \begin{array}{} { - 1 } \\ { 1 } \end{array} |$

</figure>

§ §

# 11.0 Compliance

The goal of Compliance testing is to validate the mainband supported features of a Device Under Test
(DUT) against a known good reference UCIe implementation. Device support for Compliance Testing
is optional, however a device that does not support capabilities listed in this chapter may not be able
to participate in the Compliance program. Different layers of UCIe (Physical, Adapter, Protocol) will be
checked independently with a suite of tests for compliance testing.

The system setup for compliance testing is composed of the following:

· Reference UCIe design (Golden Die): This is a known good UCIe implementation across all layers
of the UCIe stack.

· DUT: One or more DUTs that will be tested with the reference design. It is required that these
have cleared the testing requirements of die sort/pre-bond before they are brought for
compliance testing.

. In the case of Advanced Package configuration, a known good silicon bridge or interposer that
connects the Golden Die with the DUT. In the case of Standard Package configuration, a known
good package for connecting the Golden Die to the DUT.

UCIe implementations that support compliance testing must implement the Compliance/Test Register
Block as outlined in Chapter 9.0 and adhere to the requirements outlined in this chapter.

The above components are integrated together in a test package (see Figure 11-1), which is then
used for running Compliance and Interoperability tests.

UCIe sideband plays a critical role for enabling compliance testing by allowing compliance software to
access registers from different UCIe components (e.g., Physical Layer, D2D Adapter, etc.) for setting
up tests as well as monitoring status. It is expected that UCIe sideband comes up without requiring
any FW initialization.

This specification defines the required hardware capabilities of the UCIe stack in the DUT. A separate
document will be published later to describe the following:

· Compliance test setup, including the channel model and package level details

· Test details

· Golden Die details including form factor and system-level behavior.

This chapter uses the terms 'software' and 'compliance software' interchangeably. Any use of the term
`software' in this chapter means compliance software that is either running on the Golden Die, or on
an external controller that is connected to the Golden Die via test/JTAG port.

Software, prior to testing compliance for any optional UCIe capability, must read the corresponding
Capability register (e.g., PHY Capability register described in Section 9.5.3.22) to ensure that the DUT
implements the capability.

<figure>
<figcaption>Figure 11-1. Examples of Standard and Advanced Package setups for DUT and Golden Die Compliance Testing</figcaption>

DUT Die

Golden Die

DUT Die

Golden Die

Inter poser (e.g., CoWoS)

Package Substrate

Package Substrate

Reference Known Good Package
(Standard Laminate)

Reference Known Good Package
(Si Interposer, Si Bridge, FO/RDL, etc .. )

UCle PHY Modules

Si interposer

DUT Die

Reference
channels
embedded

DUT Die

Golden Die

DUT logic

Golden Die
logic

Test Port/JTAG

DUT logic

Golden Die
logic

Golden Die
Test Port/JTAG

UCle PHY
Modules

Reference
channels
embedded

</figure>

## 11.1 Protocol Layer Compliance

Protocol Layer Compliance testing seeks to test the UCIe protocol stack for compliance to the
associated protocol layer specification.

For PCIe and CXL Protocol Layers, UCIe leverages the protocol compliance defined in those
specifications for the respective transaction layers. Implementations must follow the requirements
and capabilities outlined in PCIe Base Specification and CXL Specification, respectively.

For Streaming protocols, because Protocol Layer interoperability is specific to the protocol being
streamed, compliance testing of the Protocol Layer is beyond the scope of this specification.

## 11.2 Adapter Compliance

This Specification defines the hardware capabilities that are required in the DUT for exercising and
testing the different functionalities of the Adapter. The Golden Die Adapter must have all the
capabilities of the DUT, support all the Flit Formats from Chapter 3.0, and must have the capability to
inject both consistent and inconsistent sideband messages (for Parameter exchanges, Register
accesses and state transitions) to test DUT behavior for various error scenarios (e.g., timeouts, etc.).

The capabilities listed in this section must be supported by the Adapter in the DUT if the Adapter
supports any of the Flit Formats defined in Chapter 3.0. These capabilities are applicable to Adapters
of all UCIe device types (including Retimers). Each of the capabilities also have their respective

Control and Status registers, which are used to enable software to test various combinations of flows
and test criteria.

. Ability to Inject Test or NOP Flits: On the Transmitter, the injection behavior is defined by the Flit
Tx Injection Control register (see Table 9-73). For all injected Flits, CRC is computed, and if CRC
error injection is enabled, CRC errors are injected accordingly. It is allowed for the Adapter to be
set up to inject NOP Flits or Test Flits. NOP Flit follows the identical layout as defined in
Chapter 3.0. Test Flits carry a special encoding of 01b in bits [7:6] of Byte 1 of the Flit Header
that is applicable for all Flit Formats that the Adapter supports. Unlike NOP Flits, Test Flits go
through the Tx Retry buffer if Retry is enabled. One of the purposes of defining the Test Flits is to
test the Retry Flows independently, regardless of whether the Protocol Layer is enabled. The
Payload in these Flits carry specific patterns that are determined by the fields in the Flit Tx
Injection Control register. Software is permitted to enable flit injection in mission mode as well
while interleaving with regular Protocol Flits using the appropriate programming (see the register
fields in Table 9-73). At the Receiver, these Flits are not forwarded to the Protocol Layer. The
Receiver cancels these using the pl_flit_cancel signal on FDI or any other mechanism;
however, CRC must be checked the same as with regular Flits, and any errors must trigger the
Retry Flows as applicable.

· Injection of Link State Request or Response sideband messages. This is controlled using the Link
State Injection registers defined in the Link State Injection Control Stack 0 and Link State
Injection Control Stack 1 registers (see Table 9-75 and Table 9-76, respectively). Single Protocol
stack implementations use the Stack 0 register. Software must place the Adapter in Compliance
mode (by writing 10b to the 'Compliance Mode' field in the Adapter Compliance Control register).

· Retry injection control as defined in the Retry Injection Control register (see Table 9-77).

## 11.3 PHY Compliance

This specification defines the hardware capabilities that are required in the Device Under Test (DUT)
for exercising and testing the different functionalities of the Physical Layer. The Golden Die must
support capabilities to force timeouts on all applicable sideband messages as well as state residence
timers.

The registers and associated functionality defined in Section 9.5.4 and the UHM DVSEC Capability
defined in Section 9.5.3.36 are used for Compliance testing. These registers provide the following
functionality:

· Timing margining

· Voltage margining, when supported

· BER measurement

· Lane-to-Lane skew for a given module at both the Receiver and Transmitter

· TX Equalization (EQ) as defined in Section 5.3.3

§ §

# Appendix A CXL/PCIe Register applicability to UCIe

## A.1 CXL Registers applicability to UCIe

All CXL-defined DVSECs fully apply in the context of UCIe when operating in Raw Format. When
operating in non-Raw Format, a few register definitions need to be reinterpreted in the context of
UCIe. See below for details. Note that regardless of the Raw Format or non-Raw Format, device/port
configurations with CXL 1.1 compliance is not permitted as was discussed in Chapter 9.0.

<table>
<caption>Table A-1. CXL Registers for UCIe devices</caption>
<tr>
<th>Register Block</th>
<th>Register</th>
<th>Bits</th>
<th>Comments</th>
</tr>
<tr>
<td rowspan="4">DVSEC Capability</td>
<td>DVSEC Flex Bus Port Control</td>
<td>3,4</td>
<td>See next row for how these bits are handled</td>
</tr>
<tr>
<td rowspan="2">DVSEC Flex Bus Port Status</td>
<td>3, 4</td>
<td>This bit just mirrors bits 3, 4 in Flex bus port control register, to mimic legacy behavior.</td>
</tr>
<tr>
<td>11, 12</td>
<td>Hardwired to 0</td>
</tr>
<tr>
<td>$F r o m \quad 1 4 h - 1 F h$</td>
<td></td>
<td>N/A</td>
</tr>
</table>

## A.2 PCIe Register applicability to UCIe

All PCIe specifications defined DVSEC apply in the context of UCIe as well. There are a few Link and
PHY layer registers/bits though that are N/A or need to be reinterpreted in the context of UCIe. They
are listed below.

<table>
<caption>Table A-2. PCIe Registers for UCIe devices</caption>
<tr>
<th>Register Block</th>
<th>Register</th>
<th>Bits</th>
<th>Comments</th>
</tr>
<tr>
<td rowspan="18">$P C I e$ capability</td>
<td>PCI Express Capabilities Register</td>
<td>8</td>
<td>Slot implemented - set to 0. And hence follow rules for implementing other slot related registers/bits at various locations in the PCIe capability register set.</td>
</tr>
<tr>
<td>Device capabilities Register</td>
<td>8:6</td>
<td>N/A and can be set to any value</td>
</tr>
<tr>
<td rowspan="6">Link Capabilities Register</td>
<td>3:0</td>
<td>Max Link Speed: Set to 0011b indicating 8GT/s</td>
</tr>
<tr>
<td>9:4</td>
<td>Max Link Width: 01 0000b, indicating x16</td>
</tr>
<tr>
<td>11:10</td>
<td>ASPM support: 01b/11b encodings disallowed</td>
</tr>
<tr>
<td>14:12</td>
<td>N/A</td>
</tr>
<tr>
<td>17:15</td>
<td>L1 Exit Latency: Devices/Ports must set this bit based on whether they are connected to a retimer or not, and also the retimer based exit latency might not be known at design time as well. To assist with this, these bits need to be made HWInit from a device/port perspective so system FW can set this at boot time based on the specific retimer based latencies.</td>
</tr>
<tr>
<td>18</td>
<td>N/A and hardwired to 0</td>
</tr>
<tr>
<td rowspan="5">Link Control Register</td>
<td>6</td>
<td>HW ignores what is written here but follow any base spec rules for bit attributes.</td>
</tr>
<tr>
<td>7</td>
<td>HW ignores what is written here but follow any base spec rules for bit attributes.</td>
</tr>
<tr>
<td>8</td>
<td>$S e t \quad t o \quad R O \quad 0$</td>
</tr>
<tr>
<td>9</td>
<td>Set to RO 0</td>
</tr>
<tr>
<td>10, 11, 12</td>
<td>HW ignores what is written in these bits but follows any base spec rules for bit attributes.</td>
</tr>
<tr>
<td rowspan="3">Link Status Register</td>
<td>3:0</td>
<td>Current Link speed: Set to 0011b indicating 8GT/s</td>
</tr>
<tr>
<td>9:4</td>
<td>Negotiated Link width: x16</td>
</tr>
<tr>
<td>15</td>
<td>Hardwired to 0</td>
</tr>
<tr>
<td rowspan="2">Link Capabilities 2 Register</td>
<td>7:1</td>
<td>Set to 000 0111b</td>
</tr>
<tr>
<td>15:9</td>
<td>Set to 00h</td>
</tr>
<tr>
<td rowspan="7">PCIe Capability</td>
<td rowspan="2">Link Capabilities 2 Register</td>
<td>22:16</td>
<td>Set to 00h</td>
</tr>
<tr>
<td>24:23</td>
<td>Set to 00b just to appear compliant</td>
</tr>
<tr>
<td rowspan="4">Link Control 2 Register</td>
<td>3:0</td>
<td>Target Link speed: Writes to this register are ignored by UCIe hardware, but HW follows the base spec rules for bit attributes</td>
</tr>
<tr>
<td>4</td>
<td>HW ignores what is written in this bit but follows any base spec rules for bit attributes.</td>
</tr>
<tr>
<td>5</td>
<td>HW autonomous speed disable - Set to RO 0</td>
</tr>
<tr>
<td>15:6</td>
<td>N/A for UCIe. HW should follow base spec rules for register bit attributes.</td>
</tr>
<tr>
<td>Link Status 2 Register</td>
<td>9:0</td>
<td>Set to RO 0</td>
</tr>
<tr>
<td>PCIe Extended Capability</td>
<td>Secondary PCI Express Extended Capability</td>
<td>All</td>
<td>Implement per the base spec, but HW ignores all commands from SW and also sets all equalization control registry entries to 0.</td>
</tr>
</table>

## A.3 PCIe/CXL registers that need to be part of D2D

· PCIe Link Control Register

\- Bits 13, 5, 4, and 1:0 are relevant for D2D operation

· CXL DVSEC Flex Bus Port Received Modified TS Data Phase1 Register

· CXL DVSEC Flex Bus Port Control

· CXL DVSEC Flex Bus Port Status

· CXL ARB/MUX registers

§ §

# Appendix B AIB Interoperability

Implementations are permitted to design a superset stack to be interoperable with UCIe/AIB PHY.
This section details the UCIe interoperability criteria with AIB.

## B.1 AIB Signal Mapping

### B.1.1 Data path

Data path signal mapping for AIB 2.0 and AIB 1.0 are shown in Table B-1 and Table B-2 respectively.
AIB sideband is sent over an asynchronous path on UCIe main band.

### B.1.2 Always high Valid

Always high Valid is an optional feature that is only applicable to AIB interoperability applications. This
must be negotiated prior to main band Link training through parameter exchange. Raw mode must be
used in such applications.

### B.1.3 Sideband

AIB sideband is sent using UCIe main band signals. UCIe sideband is not required in AIB
interoperability mode and it is disabled (Transmitters are Hi-Z and Receivers are disabled).

<figure>
<figcaption>Figure B-1. AIB interoperability</figcaption>

Die-to-Die Adapter (Raw Mode)

Logic Clock

Raw D2D interface

PHY Logic (AIB)

Logic Clock

Sideband

Electrical/ AFE

IO Clock

Sideband
$\left( x 4 \right)$

FW-CLK

Data x64

$\mathrm { T r a c k } \left( \text { Not required } \right)$

Disabled

</figure>

### B.1.4 Raw Die-to-Die interface

AIB Phy logic block shown in Figure B-1 presents a subset of RDI to next layer up.

Note:
More details will be shown in a later revision of this specification

<table>
<caption>Table B-1. AIB 2.0 Datapath mapping for Advanced Package</caption>
<tr>
<th>UCIe Interface</th>
<th>AIB 2.0</th>
<th>Note</th>
</tr>
<tr>
<td>TXDATA [ 39 : 0]</td>
<td>$T X \left[ 3 9 : 0 \right]$</td>
<td></td>
</tr>
<tr>
<td>TXDATA [ 47: 40]</td>
<td>AIB Sideband Tx</td>
<td>Asynchronous path</td>
</tr>
<tr>
<td>TXDATA [63: 48]</td>
<td>N/A</td>
<td>Disabled (Hi-Z)</td>
</tr>
<tr>
<td>RXDATA [ 39 : 0]</td>
<td>RX [39 : 0]</td>
<td></td>
</tr>
<tr>
<td>RXDATA [ 47: 40]</td>
<td>$A I B \quad S i d e b a n d \quad R x$</td>
<td>Asynchronous path</td>
</tr>
<tr>
<td>RXDATA [ 63 : 48]</td>
<td>N/A</td>
<td></td>
</tr>
<tr>
<td>TXDATASB</td>
<td rowspan="6">N/A</td>
<td rowspan="6">Disabled (Hi-Z)</td>
</tr>
<tr>
<td>RXDATASB</td>
</tr>
<tr>
<td>TXCKSB</td>
</tr>
<tr>
<td>RXCKSB</td>
</tr>
<tr>
<td>TXDATASBRD</td>
</tr>
<tr>
<td>RXDATASBRD</td>
</tr>
</table>

<table>
<caption>Table B-2. AIB 1.0 Datapath mapping for Advanced Package</caption>
<tr>
<th>UCIe Interface</th>
<th>AIB 1.0</th>
<th>Note</th>
</tr>
<tr>
<td>TXDATA [ 19 : 0]</td>
<td>$T X \left[ 1 9 : 0 \right]$</td>
<td></td>
</tr>
<tr>
<td>TXDATA [ 42 : 20]</td>
<td>AIB Sideband Tx</td>
<td>Asynchronous path</td>
</tr>
<tr>
<td>TXDATA [63: 43]</td>
<td>N/A</td>
<td>Disabled $\left( H i - Z \right)$</td>
</tr>
<tr>
<td>RXDATA [19 : 0]</td>
<td>$2 \times \left[ 1 9 : 0 \right]$</td>
<td></td>
</tr>
<tr>
<td>RXDATA [ 42 : 20]</td>
<td>$\mathrm { A I B } \mathrm { S i d e b a n d } R x$</td>
<td>Asynchronous path</td>
</tr>
<tr>
<td>RXDATA [63: 43]</td>
<td>N/A</td>
<td></td>
</tr>
<tr>
<td>TXDATASB</td>
<td rowspan="6">$N / A$</td>
<td rowspan="6">Disabled (Hi-Z)</td>
</tr>
<tr>
<td>RXDATASB</td>
</tr>
<tr>
<td>TXCKSB</td>
</tr>
<tr>
<td>RXCKSB</td>
</tr>
<tr>
<td>TXDATASBRD</td>
</tr>
<tr>
<td>RXDATASBRD</td>
</tr>
</table>

## B.2 Initialization

AIB Phy logic block shown in Figure B-1 contains all the AIB Link logic and state machines. Please see
AIB specification (Section 2 and Section 3) for initialization flow.

<table>
<tr>
<td>B.3</td>
<td>Bump Map</td>
</tr>
<tr>
<td>Note:</td>
<td>More details will be shown in a future revision this specification</td>
</tr>
</table>

§ §

