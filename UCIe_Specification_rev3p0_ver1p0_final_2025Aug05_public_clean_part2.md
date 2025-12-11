

<figure>
<figcaption>Figure 4-6. Valid framing example</figcaption>

Clock

Valid

Data[N-1:0][7:0]

Data Byte [N-1:0] Transfer 1

Data Byte [N-1:0] Transfer 2

8 UI

8 UI

</figure>

# 4.1.2.1 Valid Framing for Retimers

The UCIe Retimer releases credits to its local UCIe die using the Valid wire, as described in Table 4-1.
Each credit tracks 256 Bytes of data (including any FEC, CRC, etc.). The Valid Framing encodings
ensure triple bit flip detection guarantee.

If the operating speed is <= 48 GT/s, it is permitted for receiver implementations to:

· Trigger Retrain on any bit error (using the triple bit flip detection guarantee)

. Use the encodings listed in Table 4-1 to correct single bit errors (with the understanding that
three bit error detection is lost, and its contribution to overall FIT is negligible)

If the operating speed is > 48 GT/s, receiver implementations must use the encodings listed in
Table 4-1 to correct single-bit errors (three-bit error detection is not possible).

<table>
<caption>Table 4-1. Valid framing for Retimers</caption>
<tr>
<th>8-UI Valida</th>
<th>Encoding</th>
</tr>
<tr>
<td>00000000b</td>
<td>No Flit data transfer + no credit release</td>
</tr>
<tr>
<td>00001111b</td>
<td>Flit data transfer valid + no credit release</td>
</tr>
<tr>
<td>11110000b</td>
<td>No Flit data transfer + 1 credit release</td>
</tr>
<tr>
<td>11111111b</td>
<td>Flit data transfer valid + 1 Credit release</td>
</tr>
</table>

a. Note that the bits above are transmitted on the Link in order from right to left (i.e., bit 0 is transmitted on the
Link first, followed by bit 1 and so on until bit 7).

# 4.1.3 Clock Gating

Forwarded mainband clocks on the UCIe Link must be gated when Valid signal is low after providing
fixed 16 UI (8 cycles) of postamble clock for half-rate clocking and 32 UI (8 cycles) of postamble clock
for quarter-rate clocking, unless free running clock mode is negotiated or Runtime Recalibration has
been requested by the remote Link partner. Data and Clock signal parking levels when clocks are
gated are described in Section 5.11.

Note that the clock postamble is required any time that the clock can toggle with Valid assertion, and
the clock needs to stop toggling, regardless of LTSM state.

# 4.1.4 Free Running Clock Mode

Free running clock mode is defined as the mode where the forwarded clock remains toggling even
when the Transmitter for Valid is held low and there is no data transfer on the interface. This mode
must be supported to allow disabling dynamic clock gating for normal operation or debug. This must
be negotiated prior to mainband Link training through parameter exchange.

## 4.1.5 Sideband transmission

Each module supports a sideband interface with a serial data and clock pin pair. Sideband packet
formats and encodings are shown in Chapter 7.0 and the electrical characteristics are shown in
Section 5.13.

As shown in Section 7.1.2, the sideband message formats are defined as a 64-bit header with no
data, with 32 bits or 64 bits of data. A 64-bit serial packet is defined on the I/O interface to the
remote die as shown in Figure 4-7. 32-bit data is sent using the 64-bit serial packet with MSBs
padded with 0b. Two sideband serial packets on the I/O interface are separated by a minimum of 32
bits low as shown in Figure 4-8. A sideband message with data would be transferred as a 64-bit
header followed by 32 bits of low followed by 64-bit data followed by 32 bits of low.

<figure>
<figcaption>Figure 4-7. Example 64-bit Sideband Serial Packet Transfer</figcaption>

64 UI

$> = 3 2 \quad U I$

SB Clock

SB Message

D0

D1

D62

D63

</figure>

<figure>
<figcaption>Figure 4-8. Sideband Packet Transmission: Back-to-Back</figcaption>

64 UI

\>=32 UI

64 UI

\>=32 UI

SB Clock

SB Message

Sideband Packet 1

Sideband Packet 2

</figure>

### 4.1.5.1 Sideband Performant Mode Operation (PMO)

Sideband designs can negotiate support for 'Sideband Performant Mode Operation (PMO)' by way of
the Sideband Feature Extensions (SBFE) mechanism defined in Section 4.5.3.3.1.1. The Sideband
PMO bit of the {MBINIT.PARAM SBFE req/resp} sideband message (bit 1) is defined for negotiating
this operation (see Table 7-11). When supporting this feature, a UCIe Link must support this
capability on both its transmit and receive direction or not support the capability at all. In a multi-
module Link, all modules must advertise the same capability. A UCIe Link must set the Sideband PMO
bit to 1 on the {MBINIT.PARAM SBFE resp} sideband message that the UCIe Link transmits, but only
if the corresponding Req message also has that bit set to 1 and its receiver is capable of Sideband
PMO. Otherwise, the Sideband PMO bit must be cleared to 0.

When Sideband PMO capability is enabled, the 32-UI dead time between the 64-UI data transfers on
the sideband is no longer applicable and the sideband can transmit 64-UI data back-to-back with no
gaps. See Figure 4-9 and Figure 4-10 for illustration. The transmitter must follow this new mode after
the transmitter has sent and received the {MBINIT.PARAM SBFE resp} sideband message with the
Sideband PMO bit set to 1, across all modules. The receiver must be ready to accept packets in this
mode after the receiver has transmitted the {MBINIT.PARAM SBFE resp} sideband message with the
Sideband PMO bit set to 1. After Sideband PMO is enabled, the transmitter operates in Performant
Mode in all states until entry into the RESET state with the SB_MGMT_UP flag cleared to 0.
Additionally, PMO can then only be renegotiated on a training sequence with the SB_MGMT_UP flag
cleared to 0. Note that from a receiver perspective, due to timing differences, packets might be
received without the Sideband Performant Mode even after the chiplet has transmitted an

{MBINIT.PARAM SBFE resp} sideband message with the PMO bit set to 1. The sideband receiver must
be backward compatible and be able to handle 32 UI of gaps between consecutive 64-UI transfers
over the sideband Link.

<figure>
<figcaption>Figure 4-9. Example 64-bit Sideband Serial Packet Transfer in Sideband Performant Mode</figcaption>

64 UI

SB Clock

SB Message

D0

D1

D62

D63

</figure>

<figure>
<figcaption>Figure 4-10. Sideband Packet Transmission: Back-to-Back in Sideband Performant Mode</figcaption>

64 UI

64 UI

SB Clock

SB Message

Sideband Packet 1

Sideband Packet 2

</figure>

### 4.1.5.2 Priority Sideband Packet Transfer

Implementations are permitted to optionally support Priority Sideband Packet Transfers (PSPT). This
capability is negotiated as a Sideband Feature Extension. If PSPT is supported, PMO must be
supported. When supporting the PSPT capability, an implementation must support the PSPT capability
in both the transmit and receive directions. In a multi-module Link, all the modules must advertise
the same PSPT capability value. See Table 7-11 for the PSPT capability bit assignment during
negotiation in the {MBINIT.PARAM SBFE req/resp} sideband messages. The PSPT bit is set to 1 in the
{MBINIT.PARAM SBFE req} sideband message if the PSPT capability is supported by hardware and
enabled through the corresponding bit in UCIe Link Control register; otherwise, the bit is cleared to 0.
The PSPT bit is set to 1 in the {MBINIT.PARAM SBFE resp} sideband message if the PSPT capability
was advertised in the transmitted, as well as the received, {MBINIT.PARAM SBFE req} sideband
messages; otherwise, the PSPT bit is cleared to 0. The sideband receiver must be enabled to detect
and parse the priority sideband packets before the {MBINIT.PARAM SBFE resp} sideband message
with the PSPT bit set to 1 is transmitted. PMO and PSPT are negotiated as part of the same
handshake, and both must be enabled at the same time at the sideband transmitter. After PSPT is
enabled, PSPT remains enabled until entry into RESET state with the SB_MGMT_UP flag cleared to 0.

### 4.1.5.2.1 PSPT Rules

A priority traffic packet is defined in Section 7.1.2.6. In PSPT rules, all other sideband packets
(including MTP) are referred to as "normal traffic packets". Also, in this section, "idle" inserted by the
transmitter refers to both the sideband clock and data being 0 at the sideband transmitter.

The following rules are applicable when PSPT is enabled:

. A sideband transmitter will not insert any idle UI during a normal traffic packet, except when
inserting a priority traffic packet. A sideband transmitter is permitted to insert idle UI after a
normal packet has been fully transmitted.

. If a sideband transmitter has a priority traffic packet pending while transmitting a normal traffic
packet:

1\. The sideband transmitter must interrupt the normal traffic packet at an 8-UI multiple of the
transfer.

2\. To insert a priority traffic packet during a normal traffic packet transfer, the sideband
transmitter inserts idle for a time equivalent to 8 UI followed by a priority traffic packet. An
example of this is shown in Figure 4-11.

3\. The opcode field in the priority packet can be 11111b or 11110b.

. If the opcode is 11111b, the normal traffic packet resumes immediately after the priority
traffic packet without any idle time.

. If the opcode is 11110b, then another priority traffic packet is transmitted immediately
without any idle insertion.

4\. Rule 3 above applies to all subsequent priority traffic packets that are inserted by interrupting
a normal traffic packet. Thus, the opcode 11110b allows for chaining together of multiple
priority traffic packets with the opcode 11111b ending the chain.

. If the sideband Link is idle, a sideband transmitter is permitted to transmit a priority traffic packet
without any additional idle insertions. This priority packet carries an opcode of 11111b if there is
no subsequent priority packet, and an opcode of 11110b if there is another priority packet
transmitted subsequently and immediately without any idle insertion.

· The sideband receiver must keep track of whether a normal traffic packet was interrupted by a
priority traffic packet and interpret the opcode field in the priority packets accordingly.

# IMPLEMENTATION NOTE

Future ECN(s) will define additional details for priority packets. Implementations are
permitted to instantiate another instance of the RDI configuration bus (\*cfg\* signals)
to route these packets to/from the UCIe Physical Layer.

<figure>
<figcaption>Figure 4-11. Example of a Normal Traffic Packet Interrupted by a Single Priority Traffic Packet</figcaption>

-1

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

15

16

17

18

n

48

47

48

49

n

UCle SB Clock

UCle Data

NTO

NT1

NT2

NT3

NT4

NT5

NT6

NT7

PTO

PT1

PT2

PT30

PT31

NT8

$N / A$

$N T = N o r m a l$ Traffic packet, $P T = P r i o r i t y$ Traffic Packet

</figure>

## 4.2 Lane Reversal

In Section 4.2, Section 4.3, and Section 4.5, the following nomenclature is used:

· TD_P: Physical Lane for Data Transmitter

· RD_P: Physical Lane for Data Receiver

. TRD_P: Physical Lane for Redundant Data Transmitter

· RRD_P: Physical Lane for Redundant Data Receiver

. TD_L: Logical Lane for Data Transmit

· RD_L: Logical Lane for Data Receive

· TCKP_P, TCKN_P and TTRK P: Physical Lane for Clock and Track Transmitter

· TCKP_L, TCKN_L and TTRK L: Logical Lane for Clock and Track Transmitter

· RCKP_P, RCKN_P and RTRK_P: Physical Lane for Clock and Track Receiver

. RCKP_L, RCKN_L and RTRK_L: Logical Lane for Clock and Track Receiver

. TRDCK_P: Physical Lane for Redundant Clock/Track Transmitter

· RRDCK_P: Physical Lane for Redundant Clock/Track Receiver

. TRDCK_L: Logical Lane for Redundant Clock/Track Transmitter

. RRDCK_L: Logical Lane for Redundant Clock/Track Receiver

· TVLD_P, RVLD_P: Physical Lane for Valid Transmitter and Receiver

. TRDVLD_P, RRDVLD_P: Physical Lane for Redundant Valid Transmitter and Receiver

· TVLD_L, RVLD_L: Logical Lane for Valid Transmitter and Receiver

. TRDVLD_L, RRDVLD_L: Logical Lane for Redundant Valid Transmitter and Receiver

Devices must support Lane reversal of data Lanes within a Module. An example of Lane reversal is
when physical Data Lane 0 on local die is connected to physical Data Lane (N-1) on the remote die
(physical Data Lane 1 is connected to physical Data Lane N-2 and so on) where $N = 8$ for $a \times 8$
Standard Package, $N = 1 6$ for a x16 Standard Package, $N = 3 2$ for a x32 Advanced Package, and $N =$
64 for a x64 Advanced Package. Redundant Lanes, in case of Advanced Package, are also reversed.
Lane reversal must be implemented on the Transmitter only. The Transmitter reverses the logical Lane
order on Data and Redundant Lanes.

Track, Valid, Clock, and sideband signals must not be reversed.

Lane reversal is discovered and applied during initialization and training (see Section 4.5.3.3.5).

### 4.2.1 Lane ID

To allow Lane reversal discovery, each logical Data and redundant Lane within a module is assigned a
unique Lane ID. The assigned Lane IDs are shown in Table 4-2 and Table 4-3 for Advanced and
Standard Package modules, respectively. Note that logical Lane numbers in Table 4-2 and Table 4-3
represent the logical Transmitter and Receiver Lanes. For example, Logical Lane Number = 0
represents TD_L [0] /RD_L [0] and so on.

In Table 4-2, for a x64 Advanced Package module, logical Lane numbers 64, 65, 66, and 67 represent
Logical redundant Lanes TRD_L [0] /RRD_L [0], TRD_L [1] /RRD_L [1], TRD_L [2] /RRD_L [2],
TRD_L [3]/RRD_L [3], respectively. For a x32 Advanced Package module, the Lane ID for
TD_L [0 : 31] /RD_L [0 :31], TRD_L [0]/RRD_L [0] and TRD_L [1] /RRD_L [1] will be represented
by the set of Lane ID {0 ... 31, 64, 65} respectively.

In Table 4-3, for a x16 Standard Package module, the Lane ID for TD_L [ 0 : 15] /RD_L [0 : 15] will be
represented by the set of Lane ID {0 ... 15} respectively. For a x8 Standard Package module, the Lane
ID for TD_L [0 : 7] /RD_L [0: 7] will be represented by the set of Lane ID {0 ... 7} respectively.

<table>
<caption>Table 4-2. Lane ID: Advanced Package module (Sheet 1 of 2)</caption>
<tr>
<th>Logical Lane Number</th>
<th>Lane ID</th>
<th>Logical Lane Number</th>
<th>Lane ID</th>
</tr>
<tr>
<td>0</td>
<td>00000000b</td>
<td>34</td>
<td>00100010b</td>
</tr>
<tr>
<td>1</td>
<td>00000001b</td>
<td>35</td>
<td>00100011b</td>
</tr>
<tr>
<td>2</td>
<td>00000010b</td>
<td>36</td>
<td>00100100b</td>
</tr>
<tr>
<td>3</td>
<td>00000011b</td>
<td>37</td>
<td>00100101b</td>
</tr>
<tr>
<td>4</td>
<td>00000100b</td>
<td>38</td>
<td>00100110b</td>
</tr>
</table>

<table>
<caption>Table 4-2. Lane ID: Advanced Package module (Sheet 2 of 2)</caption>
<tr>
<th>Logical Lane Number</th>
<th>Lane ID</th>
<th>Logical Lane Number</th>
<th>Lane ID</th>
</tr>
<tr>
<td>5</td>
<td>00000101b</td>
<td>39</td>
<td>00100111b</td>
</tr>
<tr>
<td>6</td>
<td>00000110b</td>
<td>40</td>
<td>00101000b</td>
</tr>
<tr>
<td>7</td>
<td>00000111b</td>
<td>41</td>
<td>00101001b</td>
</tr>
<tr>
<td>8</td>
<td>00001000b</td>
<td>42</td>
<td>00101010b</td>
</tr>
<tr>
<td>9</td>
<td>00001001b</td>
<td>43</td>
<td>00101011b</td>
</tr>
<tr>
<td>10</td>
<td>00001010b</td>
<td>44</td>
<td>00101100b</td>
</tr>
<tr>
<td>11</td>
<td>00001011b</td>
<td>45</td>
<td>00101101b</td>
</tr>
<tr>
<td>12</td>
<td>00001100b</td>
<td>46</td>
<td>00101110b</td>
</tr>
<tr>
<td>13</td>
<td>00001101b</td>
<td>47</td>
<td>00101111b</td>
</tr>
<tr>
<td>14</td>
<td>00001110b</td>
<td>48</td>
<td>00110000b</td>
</tr>
<tr>
<td>15</td>
<td>00001111b</td>
<td>49</td>
<td>00110001b</td>
</tr>
<tr>
<td>16</td>
<td>00010000b</td>
<td>50</td>
<td>00110010b</td>
</tr>
<tr>
<td>17</td>
<td>00010001b</td>
<td>51</td>
<td>00110011b</td>
</tr>
<tr>
<td>18</td>
<td>00010010b</td>
<td>52</td>
<td>00110100b</td>
</tr>
<tr>
<td>19</td>
<td>00010011b</td>
<td>53</td>
<td>00110101b</td>
</tr>
<tr>
<td>20</td>
<td>00010100b</td>
<td>54</td>
<td>00110110b</td>
</tr>
<tr>
<td>21</td>
<td>00010101b</td>
<td>55</td>
<td>00110111b</td>
</tr>
<tr>
<td>22</td>
<td>00010110b</td>
<td>56</td>
<td>00111000b</td>
</tr>
<tr>
<td>23</td>
<td>00010111b</td>
<td>57</td>
<td>$0 0 1 1 1 0 0 1 b$</td>
</tr>
<tr>
<td>24</td>
<td>00011000b</td>
<td>58</td>
<td>00111010b</td>
</tr>
<tr>
<td>25</td>
<td>00011001b</td>
<td>59</td>
<td>00111011b</td>
</tr>
<tr>
<td>26</td>
<td>$0 0 0 1 1 0 1 0 b$</td>
<td>60</td>
<td>00111100b</td>
</tr>
<tr>
<td>27</td>
<td>00011011b</td>
<td>61</td>
<td>00111101b</td>
</tr>
<tr>
<td>28</td>
<td>00011100b</td>
<td>62</td>
<td>00111110b</td>
</tr>
<tr>
<td>29</td>
<td>00011101b</td>
<td>63</td>
<td>00111111b</td>
</tr>
<tr>
<td>30</td>
<td>00011110b</td>
<td>64</td>
<td>01000000b</td>
</tr>
<tr>
<td>31</td>
<td>00011111b</td>
<td>65</td>
<td>01000001b</td>
</tr>
<tr>
<td>32</td>
<td>00100000b</td>
<td>66</td>
<td>01000010b</td>
</tr>
<tr>
<td>33</td>
<td>00100001b</td>
<td>67</td>
<td>01000011b</td>
</tr>
</table>

<table>
<caption>Table 4-3. Lane ID: Standard Package Module</caption>
<tr>
<th>Logical Lane Number</th>
<th>Lane ID</th>
<th>Logical Lane Number</th>
<th>Lane ID</th>
</tr>
<tr>
<td>0</td>
<td>00000000b</td>
<td>8</td>
<td>00001000b</td>
</tr>
<tr>
<td>1</td>
<td>00000001b</td>
<td>9</td>
<td>00001001b</td>
</tr>
<tr>
<td>2</td>
<td>00000010b</td>
<td>10</td>
<td>00001010b</td>
</tr>
<tr>
<td>3</td>
<td>00000011b</td>
<td>11</td>
<td>00001011b</td>
</tr>
<tr>
<td>4</td>
<td>00000100b</td>
<td>12</td>
<td>00001100b</td>
</tr>
<tr>
<td>5</td>
<td>00000101b</td>
<td>13</td>
<td>00001101b</td>
</tr>
<tr>
<td>6</td>
<td>00000110b</td>
<td>14</td>
<td>00001110b</td>
</tr>
<tr>
<td>7</td>
<td>00000111b</td>
<td>15</td>
<td>00001111b</td>
</tr>
</table>

## 4.3 Interconnect redundancy remapping

As discussed in Section 5.9, Advanced Package modules require redundancy remapping to recover
from faulty Lanes. This section provides the details of remapping. After a successful remapping/repair,
any unused repair Lanes must have their Transmitters tri-stated and Receivers disabled.

### 4.3.1 Data Lane repair

The specification supports remapping (repair) of up to two data Lanes for each group of 32 data
Lanes. TD_P[31: 0] (RD_P[31 : 0] ) and TD_P[63: 32] (RD_P[63: 32] ) are treated as two
separate groups of 32 Lanes that can be independently repaired using redundant Lanes,
TRD_P [1 : 0] (RRD_P [1 : 0] ) and TRD_P [3 : 2] (RRD_P[3 : 2] ), respectively. TD_P [63: 32]
(RD_P[63: 32]) and hence TRD_P[3 :2] (RRD_P[3:2]) do not apply to x32 Advanced Package Link.

Lane remapping is accomplished by "shift left" or "shift right" operation. A "shift left" is when data
traffic of logical Lane TD_L [n] on TD_P[n] is multiplexed onto TD_P [n-1] . A shift left puts TD_L[0]
onto TRD _ P0 or TD_L[32] onto TRD _ P2. A shift right operation is when data traffic TD _ L[n] is
multiplexed onto TD_P [n+1] . A shift right puts TD_L [31] onto TRD_P1 or TD_L [ 63] onto TRD_P3.
See the pseudo codes in Section 4.3.3.1 and Section 4.3.3.2 that show the changes in mapping post
repair.

Note:
If the lower index redundant Lane (TRD_P[0] or TRD_P[2]) is faulty, no data lanes
can be repaired for its group. Note that if the higher index redundant lane (TRD_P [1]
or TRD_P [3]) is faulty, one data lane can be repaired for its group.

After a data Lane is remapped, the Transmitter associated with the faulty physical Lane is tri-stated
and the Receiver is disabled. The Transmitter and the Receiver of the redundant Lane used for the
repair are enabled.

Figure 4-12 shows transmit bump side of data Lane remapping for the first group of 32 Lanes. Both
"shift left" and "shift right" remapping is needed to optimally repair up to any two Lanes within the
group. Figure 4-13 shows details of the mux structure used for data Lane repair.

Note:
Example repair implementations are shown for TD_P [31 : 0] for clarity. It should be
noted that the same schemes are also applicable to TD_P [63 : 32] .

<figure>
<figcaption>Figure 4-12. Data Lane remapping possibilities to fix potential defects</figcaption>

TD_P2

TD_P9

TD_P16

TD_P23

TD_P30

$T D \_ P 3$

TD_P10

TD_P17

TD_P24

TD_P31

$T D _ { - } P 1$

TD_P8

$T D _ { - } P 1 5$

TD_P22

TD_P29

$T D \_ P 4$

TD_P11

TD_P18

TD_P25

$T R D \_ P 1$

TD_P0

TD_P7

TD_P14

TD_P21

TD_P28

TD_P5

$T D _ { - } P 1 2$

TD_P19

TD_P26

TRD_P0

TD_P6

TD_P13

TD_P20

TD_P27

</figure>

<figure>
<figcaption>Figure 4-13. Data Lane remapping: Mux chain</figcaption>

TD_L[n-1]

$\frac { E } { e }$

TD_L[n+1]

$\frac { 8 } { 8 }$

Shift_right

Shift_left

Lane Repair
Mux

Lan e Repair
Mux

Lane Repair
Mux

Lan e Repair
Mux

$\mathrm { T x }$

$\mathrm { T x }$

$T x$

$T x$

$D i e - 1$

$T D _ { - } P \left[ n _ { 1 } \right]$

$T D \_ P \left[ n \right]$

$P \left[ n + 1 \right]$

$T D _ { - } P \left[ n + 2 \right]$

RD_P[nl1]

RD_P[n]

$P \left[ n + 1 \right]$

$R D _ { - } P \left[ n + 2 \right]$

Rx

Rx

$R x$

Rx

Die-2

Lan e Repair
Mux

Lan e Repair
Mux

Lan e Repair
Mux

Lane Repair
Mux

RD_L[n-1]

RD_L[n]

RD_L[n+1]

RD_L[n+2]

</figure>

### 4.3.2 Data Lane repair with Lane reversal

If Lanes are reversed, physical Lane 0 of Transmitter (TD_P [0]) is connected to physical Lane N-1 of
the Receiver (RD_P [N-1] ). N is 64 or 32 for x64 or x32 Advanced Package modules, respectively.
See the pseudo codes in Section 4.3.3.3 and Section 4.3.3.4 that show the changes in mapping post
repair.

### 4.3.3 Data Lane repair implementation

#### 4.3.3.1 Single Lane repair

TRD_P[0] (RRD_P[0]) must be used as the redundant Lane to remap any single physical Lane
failure for TD_P [31 : 0] (RD_P[31 : 0] ) . TRD [2] (RRD [2] ) must be used as the redundant Lane to
remap any single Lane failure for TD_P [63: 32] (RD_P[63: 32] ) .

Pseudo code for repair in TD_P[31: 0] $\left( R D \_ P \left[ 3 1 : 0 \right] \right)$ $\left( 0 < = x < = 3 1 \right) :$

IF failure occurs in TD_P[x] :
IF x > 0 :

FOR 0 <= i < x:
TD_P [x-i-1] = TD_L [x-i]
$R D _ { - } L \left[ x - i \right] = R D _ { - } P \left[ x - i - 1 \right]$
TRD_P[0] = TD_L [0]
RD_L[0] = RRD_P[0]

Pseudo code for repair in TD_P [63 : 32] (RD_P[63: 32] ) $\left( 3 2 < = x < = 6 3 \right)$ (this does not apply to $x 3 2$
Advanced Package Link):

<figure>

IF failure occurs in TD_P[x] :
IF x > 32 :

FOR 0 <= i < x-32:
TD_P [x-i-1] = TD_L [x-i]
RD_L [x-i] = RD_P[x-i-1]
$I R D _ { - } P \left[ 2 \right] = I D _ { - } L \left[ 3 2 \right]$
RD_L [32] = RRD_P[2]

</figure>

As shown in Figure 4-14 TD_P [29] is remapped in the direction to use TRD_P $\left[ 0 \right]$ as the repair
resource. Figure 4-15 shows the circuit implementation.

<figure>
<figcaption>Figure 4-14. Example of Single Lane failure remapping</figcaption>

$T D \_ P 2$

TD_P9

TD_P16

$T D _ { - } P 2 3$

$T D _ { - } P 3 0$

$T D _ { - } P 3$

TD_P10

TD_P17

$T D _ { - } P 2 4$

TD_P31

TD_P1

TD_P8

TD_P15

TD_P22

TD

29

TD_P4

TD_P11

TD_P18

TD_P25

TRD_P1

$T D _ { - } P C$

$T D _ { - } P 7$

$T D _ { - } P 1 4$

TD_P21

TD_P28

TD_P5

TD_P12

TD_P19

TD_P26

$T R D \_ P O$

TD_P6

TD_P13

TD_P20

TD_P27

</figure>

<figure>
<figcaption>Figure 4-15. Example of Single Lane remapping implementation</figcaption>

$\frac { 8 } { 8 }$

$\frac { E } { e }$

$\frac { 8 } { 8 }$

$\frac { 8 } { 8 }$

Lan Repair
Mux

Lane Repair
Mu

Lane Repair
Mux

Lane Repair
Mux

$\bar { I } \mathrm { x }$

T

‹

$T x$

$\mathrm { T x }$

$D i e - 1$

$T D _ { - } P \left[ n - 1 \right]$

$T D _ { - } P \left[ n \right]$

$r D _ { - } P \left[ n + 1 \right]$

$T D _ { - } P \left[ n + 2 \right]$

BAD
LANE

$\left. R D \_ P \left[ n \right] - 1 \right]$

$R D \_ P \left[ n \right]$

$R D \_ P \left[ n + 1 \right]$

$R D _ { - } P \left[ n + 2 \right]$

$R x$

R

‹

$R x$

$R x$

Die-2

Lan e Repair
Mux

Lan e Repair
Mux

Lan e Repair
Mux

Lane Repair
Mux

$\frac { 8 } { 8 }$

$\frac { 5 } { 8 }$

RD_L[n+1]

RD_L[n+2]

</figure>

#### 4.3.3.2 Two Lane repair

Any two Lanes within a group of 32 can be repaired using the two redundant bumps. For any two
physical Lane failures in TD_P [31 : 0] (RD_P[31 : 0]), the lower Lane must be remapped to
TRD_P [0] (RRD_P[0]) and the upper Lane is remapped to TRD_P [1] (RRD_P [1]) . For any two
physical Lane failures in TD_P [63 : 32] (RD_P[63: 31] ), the lower Lane must be remapped to
TRD_P [2] (RRD_P[2]) and the upper Lane is remapped to TRD_P [3] (RRD_P [3]).

Pseudo code for two Lane repair in TD_P[31: 0] (RD_P[31: 0]) $\left( 0 < = x , y < = 3 1 \right) :$

<figure>

IF failure occurs in TD_P[x], TD_P[y] AND $\left( x < y \right)$ :
IF x > 0 :
FOR 0 <= i < x:
TD_P [x-i-1] = TD_L [x-i]
RD_L [x-i] = RD_P[x-i-1]
TRD_P[0] = TD_L [0]
$R D \_ L \left[ 0 \right] = R R D \_ P \left[ 0 \right]$
IF y < 31:
FOR 0 <= j < (31-y) :
TD_P[y+j+1] = TD_L[y+j]
$R D \left[ L \left[ y + j \right] = R D _ { - } P \left[ y + j + 1 \right] \right.$
$T R D \_ P \left[ 1 \right] = T D \_ L \left[ 3 1 \right]$
RD_L $I \left[ 3 1 \right] = R R D _ { - } \left[ 1 \right]$

</figure>

Pseudo code for two Lane repair in TD_P[63: 32] (RD_P[63: 32]) $\left( 3 2 < = x , y < = 6 3 \right)$ (this does not
apply to x32 Advanced Package Link):

$$\mathrm { R D } L \left[ x - i \right] = R D \quad P \left[ x - i - 1 \right]$$

<figure>

IF failure occurs in TD_P[x], $\mathbb{P} \left[ \mathrm { y } \right]$ AND $\left( x < y \right)$ :
IF $x > 3 2$ :

FOR $0 < = i < x - 3 2 :$
$T D \_ P \left[ x - i - 1 \right] = T D \_ L \left[ x - i \right]$

_
$T R D \_ P \left[ 2 \right] = T D \_ L \left[ 3 2 \right]$
$\mathrm { r i } \left[ 3 2 \right] = \mathrm { R R D } _ { - } \left[ 2 \right]$
IF $y < 6 3 :$
FOR 0 <= j < (63-y) :
$\mathrm { T R D } _ { - } \mathbb{P} \left[ 3 \right] = \mathrm { T D } _ { - } \mathrm { I } \left[ 6 3 \right]$
RD_L[63] = RRD_P[3]

$$T D \_ P \left[ y + j + 1 \right] = T D \_ L \left[ y + j \right]$$
$$R D \_ L \left[ y + j \right] = R D \_ P \left[ y + j + 1 \right]$$

</figure>

Shown in Figure 4-16 is an example of two (physical Lanes 25 and 26) Lane remapping. Figure 4-17
shows the circuit implementation. Both Transmitter and Receiver must apply the required remapping.

<figure>
<figcaption>Figure 4-16. Example of Two Lane failure remapping</figcaption>

TD_P2

$T D \_ P 9$

TD_P16

TD_P23

TD_P30

$T D _ { - } P 3$

$T D _ { - } P 1 0$

TD_P17

TD_P24

TD_P31

$T D \_ P 1$

TD_P8

TD_P15

TD_P22

TD_P29

TD_P4

TD_P11

TD_P18

TD 25

TRD_P1

$T D _ { - } P C$

TD_P7

TD_P14

TD_P21

TD_P28

TD_P5

TD_P12

$T D _ { - } P 1 9$

:

TD 26

TRD_P0

$T D \_ P 6$

TD_P13

$T D _ { - } P 2 0$

TD_P27

</figure>

<figure>
<figcaption>Figure 4-17. Example of Two Lane remapping implementation</figcaption>

TD_L[n-1]

$\frac { 5 } { 8 }$

TD_L[n+1]

$\frac { 8 } { 8 }$

La
e Repair
Mux

Lane Repair
Mux

Lan e Repair
Mux

L

ne Repair
Mux

Tx

$T x$

$T x$

Tx

$\mathrm { D i e - 1 }$

TD_P[n ]1]

$D _ { - }$

TD_F[n+1

]

$T D \_ P \left[ n + 2 \right]$

BAD

LANES

RD_P[nl1]

$R D \_ P \left[ n \right]$

RD_P[n+1]

$R D \_ P \left[ n + 2 \right]$

Rx

Rx

Rx

Rx

Die-2

Lane Repair
Mux

an e Repair
Mux

L
ne Repair
Mux

Lan e Repair
Mux

RD_L[n-1]

$\frac { 5 } { 8 }$

$\frac { 8 } { 8 }$

RD_L[n+2]

</figure>

#### 4.3.3.3 Single Lane repair with Lane reversal

#### 4.3.3.3.1 x64 Advanced Package Pseudo Codes

Pseudo code for one Lane failure in $T D \_ P \left[ 3 1 : 0 \right]$ (RD_P[32: 63]) $\left( 0 < = x < = 3 1 \right) :$

IF failure occurs in TD P[x] :
IF $x > 0$ :
FOR 0 <= i < x:

$$\mathrm { T D } \quad \mathrm { P } \left[ \mathrm { x } - \mathrm { i } - 1 \right] = \mathrm { T D } \mathrm { L } \left[ 6 3 - \mathrm { x } + \mathrm { i } \right]$$
$$R D \_ L \left[ 6 3 - x + i \right] = R D \_ P \left[ 6 3 - x + i + 1 \right]$$
_

_
TRD_P[0] = TD_L [63]
RD_L[63] = RRD_P[3]

Pseudo code for one Lane failure in TD_P[63: 32] $\left( R D \_ P \left[ 0 : 3 1 \right] \right)$ $\left( 3 2 < = x < = 6 3 \right) :$

IF failure occurs in TD_P[x] :
IF x > 32 :
FOR 0 <= i < x-32:
TD_P[x-i-1] = TD_L [63-x+i]
RD_L[63-x+i] = RD_P[63-x+i+1]
TRD_P [2] = TD_L [31]
RD_L [31] = RRD_P [1]

#### 4.3.3.3.2 x32 Advanced Package Pseudo Codes

Pseudo code for one-Lane failure in TD_P[31: 0] (RD_P[0:31]) $\left( 0 < = x < = 3 1 \right) :$

IF failure occurs in $T D \_ P \left[ x \right]$ :
IF $x > 0$ :
FOR 0 <= i < x:
$T R D \_ P \left[ 0 \right] = T D \_ L \left[ 3 1 \right]$
RD_L [31] = RRD_P [1]

$$T D \_ P \left[ x - i - 1 \right] = T D \_ L \left[ 3 1 - x + i \right]$$
$$R D _ { - } L \left[ 3 1 - x + i \right] = R D _ { - } P \left[ 3 1 - x + i + 1 \right]$$

#### 4.3.3.4 Two Lane repair with Lane reversal

#### 4.3.3.4.1 x64 Advanced Package Pseudo Codes

Pseudo code for two Lane failure in TD_P[31: 0] (RD_P[32: 63]) $\left( 0 < = x < = 3 1 \right) :$

<figure>

IF failure occurs in TD_P[x], TD_P[y] AND $\left( x < y \right)$ :
IF x > 0 :

FOR 0 <= i < x:
TD_P[x-i-1] = TD_L [63-x+i]
RD_L[63-x+i] = RD_P[63-x+i+1]
TRD_P[0] = TD_L [63]
RD_L [63] = RRD_P [3]
IF y < 31:
FOR 0 <= j < (31-y) :
TD_P[y+j+1] = TD_L [63-y-j]
RD_L[63-y-j] = RD_P[63-y- (j+1) ]
TRD_P [1] = TD_L [32]
RD_L [32] = RRD_P[2]

</figure>

Pseudo code for two-Lane failure in TD_P[63: 32] (RD_P[0: 31]) $\left( 3 2 < = x < = 6 3 \right) :$

IF failure occurs in TD_P[x], TD_P[y] AND $\left( x < y \right)$ :
IF x > 32 :
FOR 0 <= i < x-32:
TD_P [x-i-1] = TD_L [63-x+i]
RD_L[63-x+i] = RD_P[63-x+ (i+1) ]
TRD_P [2] = TD_L [31]
RD_L [31] = RRD_P [1]
IF y < 63:
FOR 0 <= j < (63-y) :
$\begin{array}{} { \text { TD } - \left[ y + j + 1 \right] = \text { TD } \left[ 6 3 - y - j \right] } \\ { \text { RD } \left[ L \left[ 6 3 - y - j \right] = R D \right] = P \left[ 6 3 - y - \left( j + 1 \right) \right] } \end{array}$
TRD_P [3] = TD_L
$R D \_ L \left[ 0 \right] = R R D \_ P \left[ 0 \right]$

#### 4.3.3.4.2 x32 Advanced Package Pseudo Codes

Pseudo code for two-Lane failure in TD_P[31: 0] (RD_P[0: 31]) (0 <= x <= 31):

<figure>

IF failure occurs in TD_P[x], $\mathbb{P} \left[ \mathrm { y } \right]$ AND $\left( x < y \right)$ :
IF x > 0 :

FOR 0 <= i < x:

$$T D \_ P \left[ x - i - 1 \right] = T D \_ L \left[ 3 1 - x + i \right]$$

_

$$R D \_ L \left[ 3 1 - x + i \right] = R D \_ P \left[ 3 1 - x + i + 1 \right]$$

_
TRD_P[0] = TD_L [31]
RD_L [31] = RRD_P [1]
IF $y < 3 1$ :
FOR 0 <= j < (31-y) :

$$T D \_ P \left[ y + j + 1 \right] = T D \_ L \left[ 3 1 - y - j \right]$$
$$R D _ { - } L \left[ 3 1 - y - j \right] = R D _ { - } P \left[ 3 1 - y - \left( j + 1 \right) \right]$$

TRD_P $\left[ 1 \right] = T D \_ L \left[ 0 \right]$
$L \left[ 0 \right] = R R D _ { - } P \left[ 0 \right]$

</figure>

### 4.3.4 Clock and Track Lane remapping

The specification supports remapping of one broken Lane for TCKP_P/RCKP_P, TCKN_P/RCKN_P and
TTRK_P/RTRK_P physical Lanes. The repair scheme is shown in Figure 4-18. Clock Lane remapping
allows repair of single Lane failure for both differential and pseudo-differential implementation of the
clock Receiver. The circuit details are shown in Figure 4-19 and Figure 4-20 for differential and
pseudo-differential clock Receivers respectively.

After a Lane is remapped, the Transmitter is tri-stated. The Receiver of the physical redundant
(RRDCK_P) Lane is disabled.

<figure>
<figcaption>Figure 4-18. Clock and Track repair</figcaption>

TCKP_P

TCKN_P

TRDCK_P

TTRK_P

</figure>

<figure>
<figcaption>Figure 4-19. Clock and track repair: Differential Rx</figcaption>

Clock $R x$ (Differential)

$\mathrm { T C K P } _ { - } \mathrm { L }$

Normal Path

TCKP_P

RCKP_P

Repair Path

☒

☒

Normal Path P

Repair P

TCKN_L

Normal Path

TCKN_P

RCKN P

Repair Path

☒

☒

Normal Path N

RX Diff

RCK_L

Repair N

Repair Path clock

TRDCK_L

No Repair

TRDCK_P

RRDCK P

Repair Path track

☒

☒

Normal Path RD

RX

RRDCK_L

Repair Path

TTRK_L

Normal Path

TTRK_P

RTRK P

Repair TRK

Normal Path TRK

RX

RTRK_L

Repair Path

☒

☒

</figure>

<figure>
<figcaption>Figure 4-20. Clock and track repair: Pseudo Differential Rx</figcaption>

Clock Rx (Pseudo Differential)

TCKP_P

TxCLKP

Normal Path

RCKP_P

Repair Path

☒

☒

Normal Path P

Rx

RCKP_L

Normal Path

TCKN_P

RCKN P

Repair P

TxCLKN

Repair Path

☒

☒

Normal Path N

Rx

RCKN_L

Repair Path clock

Repair N

No Repair

TRDCK_P

RRDCK_P

TRDCK_L

Normal Path RD

Repair Path track

☒

☒

Repair Path

RX

RRDCK_L

Normal Path

TTRK_P

RTRK_P

Repair TRK

TTRK_L

Repair Path

☒

☒

Normal Path TRK

RX

$\mathrm { R T R K } _ { - } !$

</figure>

### 4.3.5 Clock and Track Lane repair implementation

Pseudo code for Clock and Track Lane repair:

<figure>

IF failure occurs in TCKP_P:

TCKN P = TCKP L AND TRDCK_P = TCKN_L
RCKP_L = RCKN P AND RCKN_L = RRDCK_P

ELSE IF failure occurs on TCKN_P:
TRDCK P = TCKN L
RCKN L = RRDCK P
_
_

_

_

ELSE IF failure occurs in TTRK P:
TRDCK P = TTRK L
RTRK L = RRDCK P
_
_
_

_

</figure>

The implementation of Clock and Track Lane remapping is shown in Figure 4-21(a), $F i g u r e \quad 4 - 2 1 \left( b \right)$
and Figure 4-21(c) respectively. The corresponding circuit level details of remapping implementation
are shown in Figure 4-22, Figure 4-23 and Figure 4-24.

Note that the both Transmitter and Receiver on CKRD Lane are required during detection phase and
can be tri-stated and turned off if not used for repair.

<figure>
<figcaption>Figure 4-21. Clock and Track Lane repair scheme</figcaption>

TCKP_P

TCKP_P

TCKP_P

TCKN_P

TCKN_P

TCKN_P

TRDCK_P

TRDCK_P

TRDCK_P

TTRK_P

TTRK_P

TTRK_P

(a)

(b)

(c)

</figure>

<figure>
<figcaption>Figure 4-22. Clock and track repair: CKP repair</figcaption>

Clock Rx (Pseudo Differential)

TCKP_L

Normal Path

TCKP_P

RCKP P

Repair Path

☒

☒

Normal Path P

$R x$

$\mathrm { R C K P } _ { - }$

$\mathrm { T C K N } _ { - } \mathrm { L }$

Normal Path

TCKN P

RCKN P

Normal Path N

Repair Path

Donair N

$R v$

RCKN_L

Repair Path clock

No Repair

TRDCK_P

RRDCK_P

TRDCK_L

Normal Path RD

Repair Path track

Repair Path

RX

RRDCK_L

TTRK_L

Normal Path

TTRK P

RTRK P

Repair TRK

☒

Normal Path TRK

RX

RTRK_L

nepal Fall

☒

</figure>

<figure>
<figcaption>Figure 4-23. Clock and track repair: CKN repair</figcaption>

Clock Rx (Pseudo Differential)

TCKP_L

Normal Path

TCKP_P

RCKP_P

nepal Patlı

Normal Dath D

Repair P

RX

RCKP_L

TCKN_L

Normal Path

TCKN_P

RCKN P

Repair Path

☒

☒

☒

Normal Path N

Danair N

Rv

RCKN_L

Repair Path clock

TRDCK_L

No Repair

TRDCK_P

RRDCK P
☒

lormal Path RD

Repair Path track

RRDCK_L

Repair Path

RX

TTRK_L

Normal Path

TTRK P

RTRK P

Repair TRK

Normal Path TRK

Rx

$\mathrm { R T R K } _ { - }$

Repair Path

</figure>

<figure>
<figcaption>Figure 4-24. Clock and track repair: Track repair</figcaption>

Clock Rx (Pseudo Differential)

TCKP_L

Normal Path

TCKP_P

RCKP_P

Repair Path

Normal Dath D

Repair P

RX

RCKP_L

TCKN_L

Normal Path

TCKN_P

RCKN P

Normal Path N

Repair Path

Repair N

Rx

RCKN_L

Repair Path clock

No Repair

TRDCK_P

RRDCK_P

TRDCK

Normal Path RD

Repair Path track

Repair Path

RX

RRDCK_L

TTRK_L

Normal Path
Repair Path

TTRK_P

RTRK P

Repair TRK

Normal Path TRK

RX

RTRK_L

</figure>

### 4.3.6 Valid Repair and implementation

Valid Lane has a dedicated redundant Lane. If a failure is detected on the Valid physical Lane,
redundant Valid physical Lane is used to send Valid. Valid failure detection and repair is performed
during Link initialization and Training (Section 4.5.3.3.4).

Figure 4-25 shows the normal path for Valid and redundant valid Lanes. Figure 4-26 shows the repair
path for Valid Lane failure.

<figure>
<figcaption>Figure 4-25. Valid repair: Normal Path</figcaption>

Die-1

$D i e - 2$

TVLD_L

e Repair

TVLD_P

RVLD_P

e Repair

RVLD_L

Lane

Mux

Rx

$1$

Mux

La

TRDVLD_L

an e Repair

TRDVLD_P

RRDVLD_P

Mux

Rx

RRDVLD_L

Tx
Tx

ne Repair

Lane

Mux

</figure>

<figure>
<figcaption>Figure 4-26. Valid Repair: Repair Path</figcaption>

$D i e - 1$

$D i e - 2$

TVLD_L

Lane Repair

TVLD_P

RVLD_P

Mux

$\sharp$

Rx

an e Repair

Mux

RVLD_L

TRDVLD_L

Repair

TRDVLD_P

RRDVLD_P

Aux

Tx

Rx

Lan e Repair

RRDVLD_L

Mux

Lan

</figure>

### 4.3.7 Width Degrade in Standard Package Interfaces

In the case of x16 Standard Package modules where Lane repair is not supported, resilience against
faulty Lanes is provided by configuring the Link to a x8 width (Logical Lanes 0 to 7 or Logical Lanes 8
to 15, which exclude the faulty Lanes). For example, if one or more faulty Lanes are in logical Lane 0

to 7, the Link is configured to x8 width using logical Lanes 8 to 15. The configuration is done during
Link initialization or retraining. Transmitters of the disabled Lanes are tri-stated and Receivers are
disabled.

In the case of x8 Standard Package modules, resilience against faulty Lanes is provided by
configuring the Link to a x4 width (Logical Lanes 0 to 3 or Logical Lanes 4 to 7, which exclude the
faulty Lanes). The configuration is done during Link initialization or retraining. Transmitters of the
disabled Lanes are tri-stated and Receivers are disabled.

Figure 4-5 shows the byte to Lane mapping for a width degraded x8 interface

## 4.4 Data to Clock Training and Test Modes

Note:
Sideband commands will be identified as {SB command}.

Figure 4-27 shows the infrastructure for interface training and testing. The Transmit Die and Receive
Die implement the same Linear Feedback Shift Register (LFSR) described in Section 4.4.1. The
pattern sent from the Transmitter along with forwarded clock and Valid is compared with locally
generated reference pattern. Both transmit and receive pattern generators must start and advance in
sync. The compare circuitry checks for matching data each UI. Any mismatch between the received
pattern and pattern predicted by the local pattern generator is detected as an error.

<figure>
<figcaption>Figure 4-27. Test and training logic</figcaption>

Ref Pattern
Gen

Clock

Valid

Pattern
Gen

Error
Detect

Pattern

Rx

Pattern

Vajid

Transmit Die

Receive Die

</figure>

The receive die must implement two types of comparison schemes

. Per-Lane comparison: Per-Lane comparison is used to identify the number of failing Lanes
between the two dies. Any mismatch, above the set threshold between the received pattern and
the expected pattern on each Lane, will set an internal error detect bit for each Lane. Once a
pattern mismatch on a particular Lane is found, this error bit is set for the remainder of the test.
Figure 4-28 illustrates Per-Lane comparison mode. This mode will indicate per-Lane errors within
the module $\left( N = 6 8 \left( 6 4 + 4 \quad R D \right) \right.$ for a x64 Advanced Package Module, $N = 3 4$ (32 + 2 RD) for a
x32 Advanced Package Module, $N = 1 6$ for a x16 Standard Package Module, and $N = 8$ for a x8
Standard Package Module, respectively). The per-Lane comparison results can be read via
sideband.

· Aggregate comparison: In this mode, pattern mismatches each UI on any Lane within the
module are accumulated into a 16-bit error counter. The Lane errors are ORed to generate a
module-level error and counted as shown in Figure 4-29. This scheme can be used for module
level margin and BER.

<figure>
<figcaption>Figure 4-28. Lane failure detection</figcaption>

Error bits

Remote pattern

Lane 0

D

☐

Lane 1

D

☐

Lane 2

☐

Lane 3

☐

☐
Lane (N-1)

☐

Local pattern

Lane N

</figure>

<figure>
<figcaption>Figure 4-29. All Lane error detection</figcaption>

Remote pattern

Lane 0

Lane 1

Lane 2

Lane 3

Error
Counter

Lane (N-1)

Local pattern

Lane N

</figure>

### 4.4.1 Scrambling and training pattern generation

A Linear feedback shift register (LFSR) is defined for scrambling and test pattern generation.

The LFSR uses the same polynomial as PCIe: $G \left( X \right) = X ^ { 2 3 } + X ^ { 2 1 } + X ^ { 1 6 } + X ^ { 8 } + X ^ { 5 } + X ^ { 2 } + 1 .$ Each
☒ ☒ ☒

☒ ☒ ☒ ☒
Transmitter is permitted to implement a separate LFSR for scrambling and pattern generation. Each
Receiver is permitted to implement a separate LFSR using the same polynomial for de-scrambling and
pattern comparison. The implementation is shown in Figure 4-30. The seed of the LFSR is Lane
dependent, and based on the Logical Lane number and the seed value for Lane number is modulo 8
as shown in Table 4-4.

Alternatively, implementations can choose to implement one LFSR with different tap points for
multiple Lanes as shown in Figure 4-31. This is equivalent to individual LFSR per-Lane with different
seeds.

<table>
<caption>Table 4-4. LFSR seed values</caption>
<tr>
<th>Lane</th>
<th>Seed</th>
</tr>
<tr>
<td>0</td>
<td>23'h1DBFBC</td>
</tr>
<tr>
<td>1</td>
<td>23'h 0607BB</td>
</tr>
<tr>
<td>2</td>
<td>23'h1EC760</td>
</tr>
<tr>
<td>3</td>
<td>23'h18C0DB</td>
</tr>
<tr>
<td>4</td>
<td>23'h010F12</td>
</tr>
<tr>
<td>5</td>
<td>23'h19CFC9</td>
</tr>
<tr>
<td>6</td>
<td>23'h0277CE</td>
</tr>
<tr>
<td>7</td>
<td>23'h1BB807</td>
</tr>
<tr>
<td>RDO, RD2ª</td>
<td>23'h18C0DB</td>
</tr>
<tr>
<td>RD1, RD3b</td>
<td>23'h010F12</td>
</tr>
</table>

a. Same as Lane 3. These are not currently used.

b. Same as Lane 4. These are not currently used.

Figure 4-30. LFSR implementation

<figure>

Data_Out

D0

D1

D2

D3

D4

D5

D6

D7

$D 8$

D9

$D 1 0$

D11

D12

D13

D14

D15

D16

D17

D18

D19

D20

D21

D22

\+

</figure>

<table>
<tr>
<th>Seed</th>
<th>Seed</th>
<th>Seed</th>
<th>Seed</th>
<th>Se ed</th>
<th></th>
<th>Seed</th>
<th>Seed</th>
<th>Seed</th>
<th>Seed</th>
<th>Seed</th>
<th>Se ed</th>
<th>Seed</th>
<th>Seed</th>
<th>Se ed</th>
<th>Seed</th>
<th>Seed</th>
<th>Seed</th>
<th>Seed</th>
<th>Se ed</th>
<th>Seed</th>
<th>Seed</th>
<th>$\begin{array}{} { \text { Seed } } \\ { \text { na } } \end{array}$</th>
</tr>
<tr>
<td>D0</td>
<td>$D 1$</td>
<td>D2</td>
<td>D3</td>
<td>D4</td>
<td>$D 5$</td>
<td>D6</td>
<td>D7</td>
<td>D8</td>
<td>D9</td>
<td>D10</td>
<td>D11</td>
<td>D12</td>
<td>D13</td>
<td>D14</td>
<td>D15</td>
<td>D16</td>
<td>D17</td>
<td>D18</td>
<td>D19</td>
<td>D20</td>
<td>D21</td>
<td>Data_In</td>
</tr>
</table>

Figure 4-31. LFSR alternate implementation

<figure>
</figure>

<table>
<tr>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th colspan="2" rowspan="2">D10</th>
<th colspan="2" rowspan="2">D11</th>
<th rowspan="2">D12</th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
</tr>
<tr>
<th>D0</th>
<th></th>
<th>D1</th>
<th></th>
<th>$D 2$</th>
<th></th>
<th>D3</th>
<th></th>
<th>D4</th>
<th></th>
<th>D5</th>
<th></th>
<th>D6</th>
<th></th>
<th>D7</th>
<th></th>
<th>D8</th>
<th></th>
<th>D9</th>
<th></th>
<th></th>
<th>D13</th>
<th></th>
<th>D14</th>
<th></th>
<th>D15</th>
<th></th>
<th>D16</th>
<th></th>
<th>D17</th>
<th></th>
<th>D18</th>
<th></th>
<th>D19</th>
<th></th>
<th>D20</th>
<th></th>
<th>D21</th>
<th></th>
<th>D22</th>
<th></th>
</tr>
<tr>
<th>Seed</th>
<th></th>
<th>Seed</th>
<th></th>
<th>Seed</th>
<th></th>
<th>Seed</th>
<th></th>
<th>Seed</th>
<th></th>
<th>Seed</th>
<th></th>
<th>Seed</th>
<th></th>
<th>Seed</th>
<th></th>
<th>Seed</th>
<th></th>
<th>Seed</th>
<th></th>
<th>Seed</th>
<th></th>
<th>Seed</th>
<th></th>
<th>Seed</th>
<th></th>
<th>Seed</th>
<th></th>
<th>Seed</th>
<th></th>
<th>Seed</th>
<th></th>
<th>Seed</th>
<th></th>
<th>Seed</th>
<th></th>
<th>Seed</th>
<th></th>
<th>Seed</th>
<th></th>
<th>Seed</th>
<th></th>
<th>Seed</th>
<th></th>
<th>Seed</th>
<th></th>
</tr>
<tr>
<td>D0</td>
<td></td>
<td>D1</td>
<td></td>
<td>D2</td>
<td></td>
<td>D3</td>
<td></td>
<td>D4</td>
<td></td>
<td>D5</td>
<td></td>
<td>D6</td>
<td></td>
<td>D7</td>
<td></td>
<td>D8</td>
<td></td>
<td>$D 9$</td>
<td></td>
<td>D10</td>
<td></td>
<td>D11</td>
<td></td>
<td>D12</td>
<td></td>
<td>D13</td>
<td></td>
<td>D14</td>
<td></td>
<td>D15</td>
<td></td>
<td>D16</td>
<td></td>
<td>D17</td>
<td></td>
<td>D18</td>
<td></td>
<td>D19</td>
<td></td>
<td>D20</td>
<td></td>
<td>D21</td>
<td></td>
<td>D22</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td rowspan="2"></td>
<td rowspan="2">For i = For i =</td>
<td rowspan="2">For i =</td>
<td>For i</td>
<td rowspan="2">For i = For i =</td>
<td>For i</td>
<td>For i Reset</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td rowspan="2"></td>
<td rowspan="2"></td>
<td rowspan="2"></td>
<td></td>
<td rowspan="2"></td>
<td rowspan="2"></td>
<td rowspan="2"></td>
<td rowspan="2"></td>
<td rowspan="2"></td>
<td rowspan="2"></td>
<td rowspan="2"></td>
<td rowspan="2"></td>
<td rowspan="2"></td>
<td rowspan="2"></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>=</td>
<td>=</td>
<td>=</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>7, 6,</td>
<td>5,</td>
<td>4,</td>
<td>3, 2,</td>
<td>1,</td>
<td>0, Value</td>
<td></td>
<td>Tap_Eqn_Lane_i Data_In_Lane_i</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>9,</td>
<td>8,</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>15, 14,</td>
<td>13,</td>
<td>12,</td>
<td>11, 10,</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>17,</td>
<td>16, =</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>23, 22,</td>
<td>21,</td>
<td>20,</td>
<td>19, 18,</td>
<td></td>
<td>'1</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>25,</td>
<td>24,</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>31, 30,</td>
<td>29,</td>
<td>28,</td>
<td>27, 26,</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>39, 38,</td>
<td>37,</td>
<td>36,</td>
<td>35, 34,</td>
<td>33,</td>
<td>32,</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>47, 46,</td>
<td>45,</td>
<td>44,</td>
<td>43, 42,</td>
<td>41,</td>
<td>40,</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>49,</td>
<td>48,</td>
<td></td>
<td>+</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>55, 54,</td>
<td>53,</td>
<td>52,</td>
<td>51, 50,</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>57:</td>
<td>56: Tap_Eqn_Lane_i</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>63: 62:</td>
<td>61:</td>
<td>60:</td>
<td>59: 58:</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>Tap_Eqn_Lane_i</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td rowspan="2"></td>
<td rowspan="2">Tap_Eqn_Lane_i = Tap_Eqn_Lane_i =</td>
<td rowspan="2">Tap_Eqn_Lane_i =</td>
<td rowspan="2">Tap_Eqn_Lane_i =</td>
<td rowspan="2">Tap_Eqn_Lane_i = Tap_Eqn_Lane_i =</td>
<td rowspan="2">=</td>
<td rowspan="2">=</td>
<td></td>
<td>Data_Out_Lane_i</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td rowspan="2"></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>D1^D9 D3^D9</td>
<td>D1^D3</td>
<td>D3^D22</td>
<td>D1^D22 D13^22</td>
<td>D1^D13</td>
<td>D9^D13</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td colspan="2"></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
</table>

## 4.5 Link Initialization and Training

Link initialization and training are described at a Module level. The description of terms are used in
this section are as follows:

. UCIe Module Partner: A UCIe Module Partner is the corresponding UCIe Module on the remote
UCIe Die to which the UCIe Module connects. For example, if two UCIe Dies A and B are
connected in the standard Die rotate configuration by a 2-module UCIe Link, Modules 0 and 1;
UCIe Die A's Module 0 (UCIe Module A0) is connected to UCIe Die B's Module 1 (UCIe Module B1);
then A0 is the UCIe Module Partner of B1 and vice-versa.

· Phase Interpolator (PI) in this specification is used to refer any method of generating and
selecting sampling clock phase.

· Timeout: Every state except RESET, Active, L1/L2, and TRAINERROR in the Link Training State
Machine has a residency timeout of 8 ms. For states with sub-states, the timeout is per sub-state
(i.e., if Physical Layer is in a state for greater than 8 ms, then it transitions to TRAINERROR and
eventually to RESET). Physical Layer sideband handshakes for RDI state transitions with remote
Link partner also timeout after 8 ms. The timeout counters must be reset if a sideband message
with "Stall" encoding is received. All timeout values specified are -0% and +50% unless explicitly
stated otherwise. All timeout values must be set to the specified values after Domain Reset exit.
All counter values must be set to the specified values after Domain Reset.

· Electrical idle is described in Section 5.12.

· When Management Transport protocol is supported over the sideband, the term SB_MGMT_UP
refers to an internally maintained flag in the PHY that indicates whether the Management
Transport path has been successfully initialized with the partner chiplet. If the flag is cleared to 0,
the Management Transport path is not up. If the flag is set to 1, the Management Transport path
is up. The flag is cleared on a Management Reset or when a Heartbeat timeout is detected (see
Section 8.2.5.1.3). The flag is set after successful completion of the initialization phase of
Management Transport path setup as described in Section 8.2.3.1.2.

When training during Link Initialization (i.e., Physical Layer transitions out of RESET state), hardware
is permitted to attempt training multiple times:

· Triggers for initiating Link Training for Management Transport path setup on the sideband are:

\- Software writes 1 to the Retrain Link bit in the Sideband Management Port Structure register
(see Section 8.1.3.6.2.1)

\- HW-autonomous trigger by the Management Port Gateway to automatically train the
Management Transport path on the sideband without SW intervention, as occurs after
Management Reset

\- SBINIT pattern (two consecutive iterations of 64-UI clock pattern and 32-UI low) is observed
on any sideband Receiver clock/data pair, when the SB_MGMT_UP flag is cleared to 0

· The triggers for initiating Link Training for the mainband are:

\- Software writes 1 to Start UCIe Link Training bit in UCIe Link Control register in the UCIe Link
DVSEC (see Section 9.5.1.5)

\- When Management Transport protocol is supported on the UCIe link, software writes 1 to the
Retrain Link bit in the Management Port Structure register of either the Sideband or Mainband
Management Port that is associated with the UCIe link (see Section 8.1.3.6.2.1)

\- Adapter triggers Link Training on the RDI (RDI status is Reset and there is a NOP to Active
transition on the state request)

\- If [Management Transport protocol is not supported] OR [the SB_MGMT_UP flag is cleared to
0], the SBINIT pattern (two consecutive iterations of 64-UI clock pattern and 32-UI low) is
observed on any sideband Receiver clock/data pair

\- If [Management Transport protocol is supported] AND [the SB_MGMT_UP flag is set to 1], the
{SBINIT done req} sideband message was received from the module partner

If hardware fails training after an implementation-specific number of attempts, the hardware must
transition to RESET and wait for a subsequent Link Training trigger. Physical Layer must escalate a
fatal error to the D2D Adapter on the RDI if mainband Software-triggered or RDI-triggered Link
training fails or there is a Link-up-to-Link-down transition due to a Physical Layer timeout.

Throughout this section, references to mainband transmitter and receiver behavior are called out in
various state machine states. These references do not apply when the port does not have a mainband
(i.e., the port is a sideband-only port without a physically present mainband, or the port is a UCIe-S
port with only the sideband used. In the latter scenario, the mainband transmitters are held in tri-
state throughout and the mainband receivers are disabled.

### 4.5.1 Link Training Basic Operations

Some basic operations in Link training are defined in this section. These will be used in mainband
initialization, training and margining.

#### 4.5.1.1 Transmitter initiated Data to Clock Point Test

In this mode, the Transmitter initiates the data to clock training on all Lanes in the module at a single
PI phase. When not performing the actions relevant to this state:

· Data, Valid, and Track Transmitters drive low

· Clock Transmitters are held differential low (for differential clocking) or simultaneous low (for
Quadrature clocking)

· Data, Valid, and Clock Receivers are enabled

· Track Receiver is permitted to be disabled

The sequence of steps for this test are as follows for each UCIe Module of the UCIe Link:

1\. The UCIe Module sets up the Transmitter parameters (shown in Table 4-5), sends a {Start Tx Init
D to C point test req} sideband message to its UCIe Module Partner, and waits for a response. The
data field of this message includes the required parameters, shown in Table 4-5. The Receiver on
the UCIe Module Partner must enable the pattern comparison circuits to compare incoming
mainband data to the locally generated expected pattern. Once the data to clock training
parameters for its Receiver are setup, the UCIe Module Partner responds with a {Start Tx Init D to
C point test resp} sideband message.

2\. The UCIe Module resets the LFSR (scrambler) on its mainband Transmitters and sends the {LFSR
clear error req} sideband message. The UCIe Module Partner resets the LFSR and clears any prior
compare results on its mainband Receivers and responds with {LFSR clear error resp} sideband
message.

3\. The UCIe Module sends the pattern (selected through "Tx Pattern Generator Setup") for the
selected number of cycles ("Tx Pattern Mode Setup") on its mainband Transmitter.

4\. The UCIe Module Partner performs the comparison on its Receivers for each UI during the pattern
transmission based on "Rx Compare Setup" and logs the results.

5\. The UCIe Module requests its UCIe Module Partner for the logged results in Step 4 by sending
{Tx Init D to C results req} sideband message. The UCIe Module Partner stops comparison on its
mainband Receivers and responds with the logged results $\left\{ \mathrm { T x } \right.$ Init D to C results resp} sideband
message.

6\. The UCIe Module stops sending the pattern on its Transmitters and sends the {End Tx Init D to $\mathrm { C }$
point test req} sideband message and the UCIe Module Partner responds with { End Tx Init D to C
point test resp}. When a UCIe Module has received the {End Tx Init D to $\mathrm { C }$ point test resp}
sideband message, the corresponding sequence has completed.

<table>
<caption>Table 4-5. Data-to-Clock Training Parametersª</caption>
<tr>
<th>Parameter</th>
<th>Sideband Message Field</th>
<th>Options</th>
</tr>
<tr>
<td rowspan="3">Clock sampling/PI phase control</td>
<td rowspan="3">Clock Phase control at Transmitter</td>
<td>Eye Center found by training</td>
</tr>
<tr>
<td>Eye Left Edge found by training</td>
</tr>
<tr>
<td>Eye Right Edge found by training</td>
</tr>
<tr>
<td rowspan="3">Tx Pattern Generator Setup</td>
<td rowspan="2">Data Pattern (for Data Lanes)</td>
<td>LFSR Pattern for Data Lanes</td>
</tr>
<tr>
<td>Per-Lane ID pattern for Data Lanes as defined in Table 4-7</td>
</tr>
<tr>
<td>Valid Pattern (for Valid Lanes)</td>
<td>VALTRAIN pattern four 1s followed by four 0s</td>
</tr>
<tr>
<td rowspan="2">Tx Pattern Mode Setup</td>
<td rowspan="2">Pattern Mode</td>
<td>Burst Mode: Uses Burst Count/Idle Count/Iteration Count</td>
</tr>
<tr>
<td>Continuous Mode: Uses Burst count to indicate the number of UI of transmission. Idle Count = 0, Iteration Count = 1</td>
</tr>
<tr>
<td rowspan="2">Rx Compare Setup</td>
<td>Maximum Comparison error threshold</td>
<td>Maximum comparison error threshold</td>
</tr>
<tr>
<td>Comparison Mode</td>
<td>Per-Lane or aggregate error compare</td>
</tr>
</table>

a. See Table 7-11 for the encodings. See also the registers in Section 9.5.3.26 and Section 9.5.3.27. See also the Implementation
Note below this table.

##### IMPLEMENTATION NOTE

The Training Setup 1 and Training Setup 2 registers (see Section 9.5.3.26 and Section 9.5.3.27,
respectively) are applicable for compliance or debug. For regular operation, implementations must
follow the iteration or UI count specified in the corresponding states (for example, Section 4.5.3.4.8
specifies 4K UI of continuous mode LFSR pattern; and because these patterns are fixed, Rx is
permitted to ignore Burst Count/Idle Count/Iteration Count values in the sideband messages for
regular operation. Training Setup 3 and Training Setup 4 registers (see Section 9.5.3.28 and
Section 9.5.3.29, respectively) are applicable for regular operation as well as compliance and
debug.

Additionally, implementation notes for the parameters in Table 4-5:

· Clock sampling/PI phase control: For Tx-initiated Data to Clock point tests, this parameter is for
informational purposes only. For Rx-initiated Data to Clock point tests, the Transmitter sets the
PI phase for the requested setting (Eye Left edge, Eye Right edge or Eye Center) based on the
best known values from the most recent training for the corresponding speed. For the states of
MBTRAIN. VALVREF and MBTRAIN.DATAVREF, this would be the best known values at the
Transmitter at 4 GT/s. This field is not applicable and is ignored for Data to Clock eye sweep
tests.

· Tx Pattern Generator Setup and Tx Pattern Mode Setup:

\- For Continuous mode LFSR pattern, "Burst Count" indicates the number of UI of
transmission (for example, it is 4096 (or 4K) in Section 4.5.3.4.8). "Idle Count" is always 0
and "Iteration Count" is always 1.

\- For Continuous mode Per-Lane ID pattern, "Burst Count" indicates the number of UI of
transmission (e.g., it is 2048 for 128 iterations of the 16 bit pattern). "Idle Count" is always
0 and "Iteration Count" is always 1.

\- For Burst mode, the transmission is a "Burst Count" number of UI followed by an "Idle
Count" number of UI of 0 repeating for an "Iteration Count" number of times. In the case of
Per-Lane ID pattern, the "Burst Count" must be a multiple of the pattern size in UI. Burst
mode is currently not used for regular operation of Link Training.

\- VALTRAIN pattern is used for training of the Valid lane. In Continuous mode, "Burst Count"
indicates the number of UI of transmission (for example, it is 1024 for 128 iterations of the
8-bit pattern); "Idle Count" is always 0 and "Iteration Count" is always 1. In Burst mode,
the transmission is a "Burst Count" number of UI followed by an "Idle Count" number of UI
of 0 repeating for an "Iteration Count" number of times; the "Burst Count" must be a
multiple of the pattern size in UI.

#### 4.5.1.2 Transmitter initiated Data to Clock Eye Width Sweep

In this mode, the Transmitter initiates the data to clock training on all Lanes in the module and
sweeps through the sampling PI phases. This mode can also be used to check system margin. When
not performing the actions relevant to this state:

· Data, Valid, and Track Transmitters drive low

· Clock Transmitters are held differential low (for differential clocking) or simultaneous low (for
Quadrature clocking)

· Data, Valid, and Clock Receivers are enabled

· Track Receiver is permitted to be disabled

The sequence of steps for this test are as follows:

1\. The UCIe Module sets up the Transmitter parameters (shown in Table 4-5), sends a {Start Tx Init
D to C eye sweep req} sideband message to its UCIe Module Partner, and then waits for a
response. The data field of this message includes the required parameters, shown in Table 4-5.
The Receiver on the UCIe Module Partner must enable the pattern comparison circuits to compare
incoming mainband data to the locally generated expected pattern. Once the data to clock
training parameters for its Receiver are setup, the UCIe Module Partner responds with a {Start Tx
Init D to C eye sweep resp} sideband message.

2\. The UCIe Module resets the LFSR (scrambler) on its mainband Transmitters and sends the {LFSR
clear error req} sideband message. The UCIe Module Partner resets the LFSR and clears any prior
compare results on its mainband Receivers and responds with {LFSR clear error resp} sideband
message.

3\. The UCIe Module sends the pattern (selected through "Tx Pattern Generator Setup") for the
selected number of cycles ("Tx Pattern Mode Setup") on its mainband Transmitter.

4\. The UCIe Module Partner performs comparison on its Receivers for each UI during the pattern
transmission based on "Rx Compare Setup" and logs the results.

5\. The UCIe Module requests its UCIe Module Partner for the logged results in Step 4 by sending
{Tx Init D to C results req} sideband message. The UCIe Module Partner stops comparison on its
mainband Receivers and responds with the logged results {Tx Init D to C results resp} sideband
message.

6\. The UCIe Module sweeps through the PI phases on its forwarded clock Transmitter each time
repeating Step 2 through Step 5 to find the passing PI phase range. The sweep steps and range
are implementation specific.

7\. The UCIe Module stops sending the pattern on its Transmitters and sends the
{End Tx Init D to C eye sweep req} sideband message and the UCIe Module Partner responds
with {End Tx Init D to C eye sweep resp}. When a UCIe Module has received the {End Tx Init D to
C point eye sweep resp} sideband message, the corresponding sequence has completed.

### 4.5.1.3 Receiver initiated Data to Clock point test

In this mode, the Receiver initiates the data to clock training on all Lanes in the module at a single PI
phase. When not performing the actions relevant to this state:

· Data, Valid, and Track Transmitters drive low

· Clock Transmitters are held differential low (for differential clocking) or simultaneous low (for
Quadrature clocking)

· Data, Valid, and Clock Receivers are enabled

· Track Receiver is permitted to be disabled

The sequence of steps for this test are as follows:

1\. The UCIe Module enables the pattern comparison circuits to compare incoming mainband data to
the locally generated expected pattern, sets up the Receiver parameters (shown in Table 4-5),
sends a {Start Rx Init D to C point test req} sideband message to its UCIe Module Partner, and
then waits for a response. The data field of this message includes the required parameters, shown
in Table 4-5. Once the data to clock training parameters for its Transmitter are setup, the UCIe
Module Partner responds with a {Start Rx Init D to C point test resp} sideband message.

2\. The UCIe Module Partner resets the LFSR (scrambler) on its mainband Transmitters and sends
sideband message {LFSR clear error req}. The UCIe Module resets the LFSR and clears any prior
compare results on its mainband Receivers and responds with {LFSR clear error resp} sideband
message.

3\. The UCIe Module Partner sends the pattern (selected through "Tx Pattern Generator Setup") for
the selected number of cycles ("Tx Pattern Mode Setup") on its mainband Transmitter.

4\. The UCIe Module performs the comparison on its mainband Receivers for each UI during the
pattern transmission based on "Rx Compare Setup" and logs the results.

5\. The UCIe Module Partner sends a sideband message {Rx Init D to C Tx count done req} sideband
message once the pattern count is complete. The UCIe Module, stops comparison and responds
with the sideband message {Rx Init D to C Tx count done resp}. The UCIe Module can now use
the logged data for its Receiver Lanes.

6\. The UCIe Module sends an {End Rx Init D to C point test req} sideband message and the UCIe
Module Partner responds with an {End Rx Init D to C point test resp} sideband message. When a
UCIe Module has received the {End Rx Init D to C point test resp} sideband message, the
corresponding sequence has completed.

### 4.5.1.4 Receiver initiated Data to Clock Eye Width Sweep

In this mode, the Receiver initiates the data to clock training on all Lanes in the module at a single PI
phase. When not performing the actions relevant to this state:

· Data, Valid, and Track Transmitters drive low

· Clock Transmitters are held differential low (for differential clocking) or simultaneous low (for
Quadrature clocking)

· Data, Valid, and Clock Receivers are enabled

· Track Receiver is permitted to be disabled

The sequence of steps for this test are as follows:

1\. The UCIe Module enables the pattern comparison circuits to compare incoming mainband data to
the locally generated expected pattern, sets up the Receiver parameters (shown in Table 4-5),
sends a {Start Rx Init D to C eye sweep req} sideband message to its UCIe Module Partner, and
then waits for a response. The data field of this message includes the required parameters, shown
in Table 4-5. The Transmitter on the UCIe Module Partner must be idle. Once the data to clock
training parameters for its Transmitter are setup, the UCIe Module Partner responds with a {Start
Rx Init D to C eye sweep resp} sideband message.

2\. The UCIe Module Partner resets the LFSR (scrambler) on its mainband Transmitters and sends
sideband message {LFSR clear error req}. The UCIe Module resets the LFSR and clears any prior
compare results on its mainband Receivers and responds with an {LFSR clear error resp}
sideband message.

3\. The UCIe Module Partner sends the pattern (selected through "Tx Pattern Generator Setup") for
the selected number of cycles ("Tx Pattern Mode Setup") on its mainband Transmitter.

4\. The UCIe Module performs the comparison on its mainband Receivers for each UI during the
pattern transmission based on "Rx Compare Setup" and logs the results.

5\. The UCIe Module Partner requests the UCIe Module for the logged data to clock test results
through a {Rx Init D to C results req} sideband message. The UCIe Module responds with the
logged results for its mainband Receiver using the {Rx Init D to C results resp} sideband
message. The UCIe Module Partner can determine if the pattern comparison at the PI phase
passed or failed based on the results log.

6\. The UCIe Module Partner sweeps through the PI phases on its forwarded clock each time it
repeats Step 2 through Step 5 to find the passing PI phase range. The sweep pattern and range
are implementation specific.

7\. The UCIe Module Partner sends an {Rx Init D to C sweep done with results} sideband message
with results for its mainband Transmitter. The UCIe Module can use the sweep results for its
mainband Receivers.

8\. The UCIe Module sends an {End Rx Init D to C eye sweep req} sideband message and the UCIe
Module Partner responds with an {End Rx Init D to C eye sweep resp} sideband message. When a
UCIe Module has received the {End Rx Init D to C eye sweep resp} sideband message, the
corresponding sequence has completed.

### 4.5.2 Link Training with Retimer

The following diagram explains the initialization flow with UCIe Retimer. As shown in Figure 4-32,
external and UCIe (UCIe Die to UCIe Retimer) Links are permitted to come up independently. When a
UCIe Link trains up to local data rate and width, the remote UCIe information is requested over the
external Link. If there is a data rate and width difference, each UCIe Link is permitted to be retrained
to achieve a speed (data rate) and width match (if the UCIe Retimer requires this for operation, it
must initiate Retraining from LinkSpeed state). This can happen multiple times during initial Link
bring up or retraining. Once the UCIe Retimer has determined that the UCIe Link configuration is
suitable for successful operation with remote Retimer partner, the UCIe Link proceeds to ACTIVE
through protocol level Link initialization (LINKINIT).

<table>
<caption>Figure 4-32. Example Retimer bring up when performing speed/width match</caption>
<tr>
<th>UCle Die 0 &lt;- - &gt; UCle Retimer</th>
<th>0 External Link</th>
<th></th>
</tr>
<tr>
<td>SBInit</td>
<td rowspan="2">Ext. Link Bring up (independent)</td>
<td>SBInit</td>
</tr>
<tr>
<td rowspan="2">$M B I N I T \left( w / L o c a l \quad P a r a m \right)$</td>
<td rowspan="2">MBINIT (w/Local Param)</td>
</tr>
<tr>
<td></td>
</tr>
<tr>
<td>MBTRAIN (local Data rate)</td>
<td>Ext. $\mathrm { L i n k } \mathrm { U p }$</td>
<td>MBTRAIN (local Data rate)</td>
</tr>
<tr>
<td rowspan="4"></td>
<td>(Can send retimer-retimer messages)</td>
<td rowspan="4"></td>
</tr>
<tr>
<td></td>
</tr>
<tr>
<td>Speed/width resolution</td>
</tr>
<tr>
<td></td>
</tr>
<tr>
<td>Speed/width match check</td>
<td>Message exchange</td>
<td>Speed/width match check</td>
</tr>
<tr>
<td>LINKINIT (protocol)</td>
<td>$\mathbb{V}$</td>
<td>LINKINIT (protocol)</td>
</tr>
<tr>
<td>Active</td>
<td></td>
<td>Active</td>
</tr>
<tr>
<td rowspan="2"></td>
<td>Functional Data</td>
<td rowspan="2"></td>
</tr>
<tr>
<td></td>
</tr>
</table>

<figure>

UCle Retimer 1 < > UCle Die 1

</figure>

### 4.5.3 Link Training State Machine

A high level initialization flow is shown in Figure 4-33. A high level description of each state is shown
in Table 4-6. The details and actions performed in each state are described in the following sections.

<table>
<caption>Table 4-6. State Definitions for Initialization</caption>
<tr>
<th>State</th>
<th>Description</th>
</tr>
<tr>
<td>RESET</td>
<td>This is the state following primary reset or exit from TRAINERROR.</td>
</tr>
<tr>
<td>SBINIT</td>
<td>Sideband initialization state where the sideband is detected, repaired (when applicable) and out of reset message is transmitted.</td>
</tr>
<tr>
<td>MBINIT</td>
<td>Following sideband initialization, Mainband (MB) is initialized at the lowest speed. applicable). Both dies perform on die calibration followed by interconnect repair (when</td>
</tr>
<tr>
<td>MBTRAIN</td>
<td>Mainband (Data, Clock and Valid signals) speed of operation is set to the highest negotiated data rate. Die-to-Die training of mainband is performed to center the clock with respect to Data.</td>
</tr>
<tr>
<td>LINKINIT</td>
<td>This state is used to exchange Adapter and Link management messages.</td>
</tr>
<tr>
<td>ACTIVE</td>
<td>This is the state in which transactions are sent and received.</td>
</tr>
<tr>
<td>L1/L2</td>
<td>Power Management state.</td>
</tr>
<tr>
<td>PHYRETRAIN</td>
<td>This state is used to begin the retrain flow for the Link during runtime.</td>
</tr>
<tr>
<td>TRAINERROR</td>
<td>$S t a t e \quad i s \quad e n t e r e d \quad w h e n$ a fatal or non-fatal event occurs at any point during Link</td>
</tr>
</table>

<figure>
<figcaption>Figure 4-33. Link Training State Machine</figcaption>

RESET

TRAINERROR

Any State
Except RESET

SBINIT

$F r o m \quad L 2$

MBINIT

$F r o m \quad L 1$

$L 1 / L 2$

MBTRAIN

LINKINIT

ACTIVE

PHYRETRAIN

</figure>

#### 4.5.3.1 RESET

Physical Layer must remain in RESET for a minimum of 4 ms upon every entry to RESET, to allow PLLs
to stabilize and any other Link Training initialization requirements to be met. The minimum conditions
necessary to exit RESET are as follows:

· Power supplies are stable

· Sideband clock is available and running at 800 MHZ

· If {

\- Physical Layer and Die to Die Adapter internal clocks are stable and available

\- Mainband clock speed is set to the slowest I/O data rate (2 GHz for 4 GT/s)

\- Local SoC/Firmware not keeping the Physical Layer in RESET

\- Link training trigger for the mainband has occurred (triggers are defined in the beginning of
Section 4.5)

} OR
{
\- Sideband Management Transport protocol is supported

\- SB_MGMT_UP = 0

\- Local SoC/Firmware is not keeping the sideband in RESET

\- Management Port Gateway indicates that it is ready for Management Transport path
initialization

\- Link Training trigger for the Management Transport path has occurred (triggers are defined in
the beginning of Section 4.5)
}

· Data, Valid, Clock, and Track Transmitters are tri-stated

· Data, Valid, Clock, and Track Receivers are permitted to be disabled

· If [Management Transport protocol is not supported] OR [SB_MGMT_UP=0], Sideband
Transmitters are held low

· Sideband Receivers are enabled

If [Management Transport protocol is supported] AND [SB_MGMT_UP=1], the Physical Layer is
available for sideband packet (any sideband packets including Management Port messages)
transmission/reception in the RESET state.

If [Management Transport protocol is not supported] OR [SB_MGMT_UP=0]:

. While the LTSM is in the RESET state, a Physical Layer implementation is permitted to handle any
new or pending untransmitted sideband register access requests as Unsupported Requests, and if
doing so, it must return a corresponding completion as well as end-to-end credit and RDI credit to
the Adapter. Similarly, for register access completions, a Physical Layer implementation is
permitted to discard any new or pending untransmitted completions and because completions do
not consume a credit, there is no credit return back to the Adapter for these. While the LTSM is in
the RESET state, an implementation may handle any new or pending untransmitted Vendor-
defined messages in an implementation dependent manner. This could include dropping the
message and logging an error.

#### 4.5.3.2 Sideband Initialization (SBINIT)

In this state, the sideband (SB) interface is initialized and repaired (when applicable).

If Management Transport is supported AND the SB_MGMT_UP flag is set to 1:

· Initialization and repair of the sideband (Step 1 through Step 9 for Advanced Package and Step 1
through Step 7 for Standard Package as shown later in this section) are skipped, and only an
SBINIT Done Req/Resp handshake is performed in this state (see Step 10 for Advanced Package
flow and Step 8 for Standard Package flow as shown later in this section); otherwise, all the steps
are traversed

· Physical Layer sideband is available for sideband packet (any sideband packets including
Management Port messages) transmission/reception in this state

When not performing the actions relevant to this state:

· Data, Valid, Clock, and Track Transmitters remain tri-stated

· Data, Valid, Clock, and Track Receivers are permitted to be disabled

· If [Management Transport protocol is not supported] OR [the SB_MGMT_UP flag is cleared to 0]
OR [a Sideband Packet is not being sent], SB Transmitters continue to be held Low

· SB Receivers continue to be enabled

The SB initialization procedure is performed at 800 MT/s with 800-MHz sideband clock.

If [Management Transport protocol is not supported] OR [SB_MGMT_UP=0]:

· While the LTSM is in the SBINIT state, a Physical Layer implementation is permitted to wait for an
implementation specific amount of time to see whether SBINIT is progressing or completing, and
subsequently handle any new or pending untransmitted sideband register access requests as
Unsupported Requests, and if treating the request as an Unsupported Request, it must return a
corresponding completion as well as end-to-end credit and RDI credit to the Adapter. Similarly, for
register access completions, a Physical Layer implementation is permitted to wait for an
implementation specific amount of time to see whether SBINIT is progressing or completing, and
subsequently discard any new or pending untransmitted completions and because completions do
not consume a credit, there is no credit return back to the Adapter for these. While the LTSM is in
the SBINIT state, an implementation may handle any new or pending untransmitted Vendor-
defined messages in an implementation dependent manner. This could include dropping the
message and logging an error.

Advanced Package has redundant SB clock and SB data Lanes (DATASBRD, CKSBRD) in addition to
DATASB and CKSB. SBINIT sequence for Advanced Package where interconnect repair may be
needed is as follows:

1\. The UCIe Module must start and continue to send iterations of a 64-UI clock pattern (a clock
pattern is defined as starting with 1 and toggling every UI of transmission, i.e., 1010 ... ) and 32-
UI low on both sideband data Transmitters (TXDATASB and TXDATASBRD). The UCIe Module must
send strobes on both TXCKSB and TXCKSBRD during the 64-UI clock pattern transmission and be
gated (held low) otherwise.

2\. UCIe Module Partner must sample each incoming data patterns on its sideband Receivers with
both incoming sideband clocks (this forms four Receiver/clock combinations).

3\. A sideband data-clock Receiver combination detection is considered successful if 128 UI clock
pattern is detected.

4\. If a UCIe Module Partner detects the pattern successfully on at least one of its sideband data-
clock Receiver combination, it must stop sending data and clock on its sideband Transmitters after
four more iterations of 64-UI clock pattern and 32-UI low. This will allow for any time differences
in both UCIe Module and UCIe Module Partner coming out of RESET state. The sideband
Transmitter and Receiver on the UCIe Module must now be enabled to send and receive sideband
messages

5\. If pattern is not detected on its sideband Receiver, the UCIe Module must continue to alternate
between sending the pattern on its sideband Transmitters for 1 ms, and holding low for 1 ms, for
a total of 8 ms. The sideband Receiver of the UCIe Module must remain enabled during this time.
Timeout occurs after 8 ms. If a timeout occurs, the UCIe Module enters TRAINERROR state.

6\. If detection is successful on more than one sideband data/clock combination, the device can pick
a combination based on a priority order. Pseudocode for sideband assignment:

<table>
<tr>
<td>CKSB sampling DATASB = Result [0] # 1:</td>
<td colspan="3">Detected; 0: Not detected</td>
</tr>
<tr>
<td>CKSBRD sampling DATASB = Result [1] #</td>
<td colspan="3">1: Detected; 0: Not detected</td>
</tr>
<tr>
<td>CKSB sampling DATASBRD = Result [2] #</td>
<td colspan="3">1: Detected; 0: Not detected</td>
</tr>
<tr>
<td>CKSBRD sampling DATASBRD = Result [3]</td>
<td colspan="3"># 1: Detected; 0: Not detected</td>
</tr>
<tr>
<td>IF (Result [3: 0] == XXX1) :</td>
<td colspan="2"></td>
<td></td>
</tr>
<tr>
<td>Sideband = (DATASB/CKSB)</td>
<td colspan="2"></td>
<td></td>
</tr>
<tr>
<td rowspan="2">ELSE IF (Result [3: 0] == XX10) : Sideband = (DATASB/CKSBRD)</td>
<td colspan="2"></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td rowspan="2">ELSE IF (Result [3: 0] == X100) : Sideband = (DATASBRD/CKSB)</td>
<td colspan="2"></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td>ELSE IF (Result [3: 0] == 1000) :</td>
<td colspan="2"></td>
<td></td>
</tr>
<tr>
<td>Sideband = (DATASBRD/CKSBRD)</td>
<td colspan="2"></td>
<td></td>
</tr>
<tr>
<td>Else:</td>
<td colspan="2"></td>
<td></td>
</tr>
<tr>
<td>Sideband is not functional</td>
<td colspan="3"></td>
</tr>
</table>

7\. If the sideband on the UCIe Module is enabled to send and receive sideband messages (Step 4),
the UCIe Module must start and continue to send {SBINIT Out of Reset} sideband message on
both TXDATASB and TXDATASBRD while sending both TXCKSB and TXCKSBRD until it detects the
same message in its sideband Receivers or a timeout occurs at 8 ms.

8\. If {SBINIT Out of Reset} sideband message detection is successful on its sideband Receivers, the
UCIe Module stops sending the sideband message. Before sending any further sideband
messages, both UCIe Module and UCIe Module Partner must apply Sideband Data/Clock
assignment (called the functional sideband) based on the information included in the {SBINIT Out
of Reset} sideband message.

9\. Any further sideband messages must be sent and received on the functional sideband. Any
sideband message exchange can now be performed.

10\. The UCIe Module sends the {SBINIT done req} sideband message and waits for a response. If
this message is received successfully, UCIe Module Partner responds with {SBINIT done resp}
sideband message. When a UCIe Module has sent and received the {SBINIT done resp} sideband
message, the UCIe Module must exit to MBINIT. The following additional rules apply when the
transmitting/receiving chiplet supports Management Transport protocol. These additional rules
are required to initiate mainband link training for the scenario in which the Management Transport
path has already been established prior (i.e., SB_MGMT_UP flag is set to 1) and one of the
mainband link training triggers (see Section 4.5) occurred with the Link Training State Machine in
RESET state.

\- If the Module partner that is receiving the {SBINIT done req} sideband message is in RESET
state and is ready to proceed with mainband initialization, the module partner must transition
to SBINIT state, respond with an {SBINIT done resp} sideband message, and then send a
{SBINIT done req} sideband message.

\- Module partner must ignore a received {SBINIT done req} sideband message if the module
partner is EITHER [in RESET state but not yet ready to proceed with mainband initialization]
OR [in a state machine state other than RESET/SBINIT].

\- UCIe Module that is transmitting the {SBINIT done req} sideband message must transition to
RESET state (by way of TRAINERROR state) if the UCIe Module did not receive a response
within the regular 8-ms time window. In that scenario, the UCIe Module can choose to re-
issue the {SBINIT done req} sideband message after transitioning to SBINIT state again from
RESET state. The UCIe Module can repeat this process N number of times before waiting in
RESET for a new training trigger. (The value of N is implementation-dependent.) The UCIe
Module partner must collapse multiple outstanding {SBINIT done req} sideband messages
and respond only with a single {SBINIT done resp} sideband message.

The next state is mainband initialization (MBINIT) if sideband message exchange is successful.

SBINIT sequence for Standard Package where interconnect Lane redundancy and repair are not
supported is as follows:

1\. The UCIe Module must start and continue to send iterations of 64 UI clock pattern (a clock pattern
is defined as starting with 1b and toggling every UI of transmission, i.e., 1010 ... ) and 32 UI low
on its sideband Transmitter (TXDATASB). The UCIe Module must send strobe on its sideband clock
(TXCKSB) during the 64-UI clock pattern duration and gated (held low) otherwise.

2\. The UCIe Module Partner must sample incoming data pattern with incoming clock.

3\. Sideband pattern detection is considered successful if 128 UI clock pattern is detected.

4\. If the UCIe Module successfully detects the pattern, it stops sending data and clock on its
sideband Transmitters after four more iterations of pattern in Step 1. This will allow for any time
differences in both UCIe Modules coming out of RESET. The UCIe Module sideband Transmitter
and Receiver must now be enabled to send and receive sideband messages, respectively.

5\. If pattern is not detected on its sideband Receiver, the UCIe Module continues to alternate
between sending the pattern on its Transmitters for 1 ms, and holding low for 1 ms, for a total of
8 ms. The sideband Receiver must be enabled during this time. Timeout occurs after 8 ms. If a
timeout occurs, the UCIe Module must exit to TRAINERROR. If a pattern is detected successfully
at any time, as described in Step 3, the UCIe Module enables sideband message transmission as
described in Step 4 and continues to Step 6.

6\. Once sideband detection is successful (Step 5), the UCIe Module must start and continue to send
{SBINIT Out of Reset} sideband message on TXDATASB while sending TXCKSB until it detects the
same message in its sideband Receivers or a timeout occurs.

7\. If {SBINIT Out of Reset} sideband message detection is successful, the UCIe Module must stop
sending the message. Any sideband message exchange can now be performed.

8\. The UCIe Module must send the {SBINIT done req} sideband message. If this message is
received successfully, the UCIe Module Partner responds with the {SBINIT done resp} sideband
message. When the UCIe Module has sent and received the {SBINIT done resp} sideband
message, the UCIe Module must exit to MBINIT. The following additional rules apply when the
transmitting/receiving chiplet supports Management Transport protocol. These additional rules
are required to initiate mainband link training for the scenario in which the Management Transport
path has already been established prior (i.e., SB_MGMT_UP flag is set to 1) and one of the
mainband link training triggers (see Section 4.5) occurred with the Link Training State Machine in
RESET state.

\- If the Module partner that is receiving the {SBINIT done req} sideband message is in RESET
state and is ready to proceed with mainband initialization, the module partner must transition
to SBINIT state, respond with an {SBINIT done resp} sideband message, and then send a
{SBINIT done req} sideband message.

\- Module partner must ignore a received {SBINIT done req} sideband message if the module
partner is EITHER [in RESET state but not yet ready to proceed with mainband initialization]
OR [in a state machine state other than RESET/SBINIT].

\- UCIe Module that is transmitting the {SBINIT done req} sideband message must transition to
RESET state (by way of TRAINERROR state) if the UCIe Module did not receive a response
within the regular 8-ms time window. In that scenario, the UCIe Module can choose to re-
issue the {SBINIT done req} sideband message after transitioning to SBINIT state again from
RESET state. The UCIe Module can repeat this process N number of times before waiting in
RESET for a new training trigger. (The value of N is implementation-dependent.) The UCIe
Module partner must collapse multiple outstanding {SBINIT done req} sideband messages
and respond only with a single {SBINIT done resp} sideband message.

The next state is mainband initialization (MBINIT) if sideband message exchange is successful. For
the remainder of initialization and operations, when not transmitting sideband packets, sideband
Transmitters are held Low and sideband Receivers are enabled.

### 4.5.3.3 MBINIT

In this state, the mainband (MB) interface is initialized and repaired or width degraded (when
applicable). The data rate on the mainband is set to the lowest supported data rate (4 GT/s).

For Advanced Package interconnect repair may be needed. Sub-states in MBINIT allows detection
and repair of data, clock, track and valid Lanes. For Standard Package, where no Lane repair is
needed, sub-states are used to check functionality at lowest data rate and width degrade if needed.

<figure>
<figcaption>Figure 4-34. MBINIT: Mainband Initialization and Repair Flow</figcaption>

From SBINIT

PARAM

Cal

RepairCLK

RepairVAL

ReversalMB

RepairMB

To MBTRAIN

</figure>

#### 4.5.3.3.1 MBINIT.PARAM

This state is used to perform exchange of parameters that are required to set up the maximum
negotiated speed and other PHY settings. Mainband Transmitters remain tri-stated and mainband
Receivers are permitted to be disabled. The following parameters are exchanged over sideband with
UCIe Module Partner:

· "Voltage swing": The five bit value indicates the Transmitter voltage swing to the UCIe Module
Partner. The UCIe Module Partner must use this value and its Receiver termination information to
set the reference voltage (Vref) for its Receivers. The corresponding bits in the {MBINIT.PARAM
configuration resp} sideband message are reserved.

. "Maximum Data Rate": The four bit value indicates the Maximum supported Data rate to the UCIe
Module Partner. This value must take into consideration all the required features at the data rate
(BER, CRC/Retry, quadrature clock phase support etc.). The UCIe Module Partner must compare
this value with its supported maximum data rate and must respond with the maximum common
data rate encoding in the {MBINIT.PARAM configuration resp} sideband message. For example, a
UCIe Module is 8 GT/s capable while the UCIe Module Partner advertises 16 GT/s, the UCIe
Module must pick 8 GT/s and send it back in response.

. "Clock Mode": The one bit value indicates the UCIe Module's request to the UCIe Module Partner
for a strobe or continuous clock for operating speeds <= 32 GT/s. If the operating speed is

\> 32 GT/s, the Link operates with continuous clock and the "Clock Mode" parameter does not
change hardware behavior. If the negotiated maximum data rate is > 32 GT/s but the operating
speed degrades to $< = 3 2 \quad G T / s ,$ this parameter is used by the Transmitter to set up the Clock
Mode on its clock Transmitter. The {MBINIT.PARAM configuration resp} sideband message must
reflect the same value. Continuous clock mode requires the clock to be free running and is
enforced after receiving the {MBTRAIN.RXCLKCAL start req} sideband message from the UCIe
Module Partner. The clock remains free running through the remainder of MBTRAIN (unless
MBTRAIN.LINKSPEED is exited due to errors) and in ACTIVE.

##### IMPLEMENTATION NOTE

Note that the free-running clock (if requested) is enforced from the
MBTRAIN.RXCLKCAL state. The states of MBINIT as well as the states of MBTRAIN
before RXCLKCAL operate in Strobe mode to check Clock and Valid Lanes in a
structured manner. It is permitted for implementations to set an implementation-
specific higher error threshold in these states in case the receiver implementation will
miss sampling around the edges of the transmitted pattern because of a lack of the
free-running clock.

. "Clock Phase": The one bit value indicates the UCIe Module's request to UCIe Module Partner for
the Clock Phase support on UCIe Module's forwarded clock for operating speeds of 24 GT/s and
32 GT/s. This should only be set to 1 if the operation at 24 GT/s or 32 GT/s is supported and the
receiver requires quarter-rate clocking for these data rates (see Table 5-12). If the operating
speed is < 24 GT/s or > 32 GT/s, this parameter does not change hardware behavior. If the
negotiated maximum data rate is > 32 GT/s but the operating speed degrades to 24 GT/s or 32
GT/s, this parameter is used by the Transmitter to set up the Clock Phase. The corresponding bit
in the {MBINIT.PARAM configuration resp} sideband message must be set to 1 if this was
requested and the operational data rate allows it.

. "Module ID": The UCIe Module sends its "Module ID". This can be used by the UCIe Module
Partner if in a multi-module configuration for Byte mapping, Module enable/disable information
etc. The corresponding bits in the {MBINIT.PARAM configuration resp} sideband message are
reserved.

· "UCIe-A x32": This bit is set to 1b when APMW bit in DVSEC UCIe Link Capability register (see
Section 9.5.1.4) is set to 1b (OR) 'Force x32 width mode in x64 Module' in the PHY Control
register (see Section 9.5.3.23) is set; otherwise, the bit is set to 0b. If a x64 Advanced Package
module supports width reduction to interoperate with a x32 Advanced Package Module, it uses
this information from its link partner to condition the results during MBINIT.REVERSALMB. The
corresponding bits in the {MBINIT.PARAM configuration resp} sideband message are reserved.

· "UCIe-S x8": This bit is set to 1 in message {MBINIT.PARAM configuration req} when bit 20,
SPMW, in the DVSEC UCIe Link Capability register (see Section 9.5.1.4) is set to 1 (OR) 'Force x8
Width' bit is set to 1 in the PHY Control register (see Section 9.5.3.23). Otherwise, this bit is set
to 0. See Section 4.5.3.3.6 for how this bit is used. The corresponding bit in the {MBINIT.PARAM
configuration resp} sideband message is reserved.

. "Sideband Feature Extensions": This bit is set to 1 if the transmitter supports sideband feature
extensions (see Section 4.5.3.3.1.1).

· "Tx Adjustment during Runtime Recalibration (TARR)": This bit is set to 1 in the {MBINIT.PARAM
configuration req} sideband message if the UCIe Module supports TARR capability and TARR
capability has been enabled in the corresponding bit in the PHY Control register (see
Section 9.5.3.23). See Section 4.6 for details about the TARR flow. If the sent and received
{MBINIT.PARAM configuration req} sideband messages have this bit set to 1, then the
corresponding bit must be set to 1 in the {MBINIT.PARAM configuration resp} sideband message.

Following is the sequence for parameter exchange:

1\. The UCIe Module sends the {MBINIT.PARAM configuration req} sideband message to exchange
parameters with the UCIe Module Partner.

2\. After the {MBINIT.PARAM configuration req} sideband message is received, the UCIe Module
Partner resolves and responds with the {MBINIT.PARAM configuration resp} sideband message.

3\. After the UCIe Module has sent and received the {MBINIT.PARAM configuration resp} sideband
message, the UCIe Module must exit to MBINIT.CAL.

It is strongly recommended that if interoperable parameters are not negotiated, then hardware maps
this scenario to an Internal Error in the Error Log 1 register and transition the LTSM to TRAINERROR,
RDI to LINKERROR, and assert pl_trainerror on RDI. For a multi-module Link, all the parameters
except "Module ID" must be the same for all the modules, and if this is not the case, it is strongly
recommended that hardware maps this scenario to the same error escalation path.

When management transport is supported, the additional conditions required for the Link training
state machine to exit MBINIT.PARAM state to MBINIT.CAL are:

· Management Transport was not negotiated.

. (OR) Management Transport was negotiated and it was either initialized successfully or an error
was detected during initialization.

· (OR) SB_MGMT_UP flag is already set on entry into MBINIT state

AND

There is no MBINIT Stall condition (see Section 4.5.3.3.1.2)

AND

Port is ready to train mainband.

### 4.5.3.3.1.1 Management Transport Path Negotiation

Management Transport protocol over the sideband is optional and chiplets use the mechanism
described in this section to negotiate support for it. A sample negotiation flow is shown in Figure 4-35
for a single module design. Sideband Feature Extensions Supported (SFES) is bit 14 in the
{MBINIT.PARAM configuration req} sideband message (see Table 7-11). Note that MBINIT.PARAM
state handshake relating to management path negotiation described in this section, is performed on
all transitions through the MBINIT state. If SB_MGMT_UP flag is set (see Section 8.2.3.1.2 for when
this happens) at entry into MBINIT state, management transport traffic continues without interruption
in the MBINIT.PARAM state.

<figure>
<figcaption>Figure 4-35. Example Sideband Management Transport Protocol Negotiation - Single-module Scenario</figcaption>

MBINIT.PARAM Configuration Req[ 14]=1

MBINIT.PARAM Configuration Req[ 14]=1

MBINIT.PARAM Configuration Resp[14]=1

Chiplet 0

MBINIT.PARAM SBFE Req[0]=1

$\frac { 9 } { 8 }$ 1

MBINIT.PARAM SBFE Resp[0]=1

MBINIT.PARAM Configuration Resp[14]=1

MBINIT.PARAM SBFE Req[0]=1

MBINIT.PARAM SBFE Resp[0]=1

Negotiation Phase Complete
(i.e., Chiplet 0 can start
Initialization Phase)

Negotiation Phase Complete
(i.e., Chiplet 1 can start
Initialization Phase)

</figure>

<figure>
<figcaption>Figure 4-36. Example Sideband Management Transport Protocol Negotiation - Two-module Scenarioª</figcaption>

-Chiplet 0

-Chiplet

MBINIT.PARAM Configuration Req[14]=1

-MBINIT.PARAM Configuration Req[ 14]=1

MBINIT.PARAM Configuration Req[ 14]=1

-MBINIT.PARAM Configuration Req[ 14]=1-

-MBINIT.PARAM Configuration Resp[14]=1

MBINIT.PARAM Configuration Resp[14]=1

MBINIT.PARAM Configuration Resp[14]=1-

MBINIT.PARAM SBFE Req[0]=1

-MBINIT.PARAM SBFE Req[0]=1
MBINIT.PARAM SBFE Resp[U]=>

MBINIT.PARAM Configuration Resp[14]=1

-MBINIT. PARAM SBFE Resp[0]=1
MBINIT.PARAM SBFE Req[0]=1
MBINIT.PARAM SBFE Req[0]=1

-MBINIT.PARAM SBFE Resp[0]=1-
MBINIT.PARAM SBFE Resp[0]=1

Negotiation Phase Complete
i.e., Chiplet 0 can start
Initialization Phase

Negotiation Phase Complete
i.e., Chiplet 1 can start
Initialization Phase

</figure>

a. Solid lines are for Module 0. Dashed lines are for Module 1.

. Unless otherwise specified, a chiplet can optionally check for violation of any Negotiation Phase
rules (discussed in the subsequent bullets), and when a violation is detected, the chiplet initiates
a TRAINERROR handshake (see Section 4.5.3.8) to return the LTSM to RESET state.

· Sideband Feature Extensions Supported (SFES) bit in the {MBINIT.PARAM configuration req}
sideband message (see Table 7-11, it is bit [14] in the message) is defined to indicate support for
extended sideband features (of which Management Transport is one), during MBINIT.PARAM state
of link training.

\- 0 => Sideband Feature Extensions are not supported, 1 => Sideband Feature Extensions are
supported.

\- All modules in a multi-module design must have the same value for this bit in the Req
message.

\- After the SB_MGMT_UP flag is set, the value of this bit must remain the same on all
subsequent transitions through the MBINIT.PARAM state, until that flag is cleared.

. If the Remote link partner supports sideband feature extensions and it received the SFES bit set
to 1 in the {MBINIT.PARAM configuration req} sideband message, the Remote link partner will set
SFES bit in the {MBINIT.PARAM configuration resp} sideband message that it sends out;
otherwise, the bit is cleared to 0 in the resp message.

\- All modules in a multi-module design must have the same value for this bit in the resp
message.

. If the SFES bit in the {MBINIT.PARAM configuration resp} sideband message is received as set to
1 across all modules, then the chiplet negotiates the next level of details of extended sideband
features supported with remote link partner. If the SFES bit in the {MBINIT.PARAM configuration
resp} sideband message is received as cleared to 0 in any module, then MBINIT.PARAM state is
exited to MBINIT.CAL.

\- {MBINIT.PARAM SBFE req} sideband message (see Table 7-11) is sent to the remote link
partner on all modules which then sends back an {MBINIT.PARAM SBFE resp} sideband
message on all modules. This handshake happens independently in each direction.

o SBFE Req[0]/Resp[0] (also referred to as the MTP bit) indicates support for transmission/
reception of Management Port Messages. Remote link partner must set the MTP bit in the
{MBINIT.PARAM SBFE resp} sideband message if it was set in the {MBINIT.PARAM SBFE
req} sideband message, and it supports receiving Management Encapsulation messages.

o After the SB_MGMT_UP flag is set to 1, the value of this bit must remain the same on all
subsequent transitions through the MBINIT.PARAM state, until that flag is cleared to 0.

· When negotiating SFES in {MBINIT.PARAM configuration req/resp}, if a chiplet advertised SFES
support in the Req message, the chiplet must also advertise that support in the Resp message
provided the associated Req message had that capability advertised. If the chiplet did not
advertise SFES support in the Req message, then the chiplet must not advertise that support in
the Resp message.

· For a multi-module UCIe Link, the negotiation is performed independently per module.

\- A Physical Layer implementation may advertise MTP bit in the SBFE Req message only on a
subset of the modules.

Note:
A message sent on a given Module ID could be received on a different Module ID on the
partner sideband Receiver. Hence all sideband links in a multi-module design must be
capable of receiving MPMs even if they are limited to only supporting transmit of these
messages on a subset of sideband links. See Figure 4-37 and Figure 4-38 for examples
of multi-module transmit/receive scenarios that illustrate this point.

. After the {MBINIT.PARAM SBFE resp} sideband message has been transmitted to the remote link
partner and {MBINIT.PARAM SBFE resp} sideband message has been received from the remote

link partner are complete (successfully or unsuccessfully) during MBINIT.PARAM across all
modules, the PHY informs the Management Port Gateway of the following:

\- Negotiated link count with management transport support on the transmit side, using the
pm_param_local_count [N-1 : 0] signals (see Section 10.1 for more details) at the end of
the negotiation phase. This is the value RxQ-Local. A link is considered to have negotiated
management transport support on the transmit side if the link transmitted the
{MBINIT.PARAM SBFE req} sideband message with the MTP bit set to 1 and received the
corresponding {MBINIT.PARAM SBFE resp} sideband message with its MTP bit also set to 1.

\- Negotiated link count with management transport support on the receive side, using the
pm_param_remote_count [N-1 : 0] signals (see Section 10.1 for more details). This is the
value RxQ-Remote. A link is considered to have negotiated management transport support on
the receive side if the link received the {MBINIT.PARAM SBFE req} sideband message with the
MTP bit set to 1 and transmitted the corresponding {MBINIT.PARAM SBFE resp} sideband
message with its MTP bit also set to 1.

· A module must be able to receive initialization phase-related messages (see Section 8.2.3.1.2)
once it has transmitted {MBINIT.PARAM SBFE resp}.

· Negotiation phase ends when {MBINIT.PARAM SBFE resp} has been sent and received across all
modules.

. While in SBINIT state, if the SB_MGMT_UP flag transitioned from 1 to 0, the chiplet must move
the LTSM to TRAINERROR state -> RESET state.

. While in MBINIT state, if the SB_MGMT_UP flag transitioned from 1 to 0, the chiplet must perform
a TRAINERROR handshake and move the LTSM to TRAINERROR state -> RESET state.

<figure>
<figcaption>Figure 4-37. Example Sideband MPM Logical Flow with Two Modules and No Module Reversal</figcaption>

Management
Port Gateway

PHY

PHY

Management
Port Gateway

Tx for far-
end RxQ-
ID=0

RxQ-ID=0

Module 0

SB

Module 0

RxQ-ID=

Tx for far-
end Rx Q-
ID=0

Tx for far-
end RxQ-
ID=1

RxQ-ID=1

Module 1

SB

Module 1

RxQ-ID=1

Tx for far-
end Rx Q-
ID=1

Chiplet 0

Chiplet 1

</figure>

<figure>
<figcaption>Figure 4-38. Example Sideband MPM Logical Flow with Two Modules and Module Reversal</figcaption>

Management
Port Gateway

PHY

PHY

Management
Port Gateway

Tx for far-
end RxQ-
ID=0

RxQ-ID=1

Module 0

SB

Module 1

$R \times Q - I D = 0$

Tx for far-
end Rx Q-
ID=1

Tx for far-
end RxQ-
ID=1

$R \times Q - I D = 0$

Module 1

SB

Module 0

$8 \times 0 - 1 0 =$

Tx for far-
end Rx Q-
ID=0

Chiplet 0

Chiplet 1

</figure>

### 4.5.3.3.1.2 MBINIT Stall Capability

To support firmware download and other functionality that might have to be configured before the
mainband link can start training, a capability is provided to "pause" the MBINIT state machine after
the PARAM sub-state has completed.

This is an optional capability that is enabled only when both chiplets have indicated support for
Sideband Feature Extensions as described in Section 4.5.3.3.1.1.

To "pause" link training after MBINIT.PARAM, either side can send a "Stall" encoding of FFFFh in the
MsgInfo field of the {MBINIT.PARAM SBFE resp} sideband message. For example, if a chiplet needs to
download firmware by way of the partner port before the chiplet can bring up the mainband, the
partner port can respond with "stall" encoding as stated above. Stall encoding instructs the other side
to pause and not move beyond the MBINIT.PARAM state. The payload in the {MBINIT.PARAM SBFE
resp} sideband message with stall encoding is still valid and must be accurate to the responder's
capabilities. An {MBINIT.PARAM SBFE resp} sideband message with "Stall" encoded must be sent
once every 4 ms until the sender determines that it no longer needs to stall, at which time the sender
either sends the {MBINIT.PARAM SBFE resp} message without the stall encoding (in which case the
state machine advances to MBINIT.CAL state if other conditions allow (see Section 8.2.3.1.2)), OR the
sender does not send an {MBINIT.PARAM SBFE resp} sideband message, the link times out, and the
link transitions from TRAINERROR state to RESET state and starts over again.

It is legal for one side to indicate a stall and the other side to not indicate a stall. In that case, both
sides are stalled. It is also valid for either side to explicitly request an entry to TRAINERROR state
while in MBINIT.PARAM state. This can occur if either side is not yet ready to train the mainband.

See Section 4.5.3.3.1.3 for details of what happens at the end of MBINIT.PARAM when either end is a
sideband-only port.

Support for receiving an {MBINIT.PARAM SBFE resp} sideband message with "stall" encoding is
required in all ports that advertise the SFES bit set to 1 in the {MBINIT.PARAM configuration req}
sideband message. Support for transmitting the {MBINIT.PARAM SBFE resp} sideband message with
"stall" encoding is implementation-dependent. For example, if a design needs to support the firmware

download feature, the design can support this capability if the design cannot complete firmware
download within 8 ms.

Figure 4-39 shows a scenario in which the link training state machine initially moves through
RESET -> SBINIT -> MBINIT.PARAM with "stall" -> TRAINERROR -> RESET. During this phase, a
chiplet "stalls" in MBINIT.PARAM for additional Init time, such as for downloading chiplet firmware.
When the chiplet Init is complete, the chiplet either initiates entry to TRAINERROR state with a
TRAINERROR handshake message, OR the chiplet can stop sending the {MBINIT.PARAM SBFE resp}
sideband message with "stall" encoding, which would eventually trigger entry to TRAINERROR state
initiated by the partner chiplet. In the second phase, the state machine moves through to SBINIT ->
MBINIT.PARAM without "stall" -> MBINIT.CAL, thus training the mainband. This flow is useful for
scenarios in which a chiplet potentially needs to change the advertised parameters for Link training
after chiplet Init. Note that the transition to TRAINERROR in this case does not escalate to RDI
transitioning to LinkError (or pl_trainerror assertion on RDI).

<figure>
<figcaption>Figure 4-39. MBINIT "Stall" Example 1</figcaption>

Sideband Management path setup occurs first, followed by mainband training but
with an entry to RESET in between.

"Stall" in MBINIT.PARAM is used to gain additional time for chiplet initialization
during the first entry to MBINIT.PARAM.

RESET

TRAIN ERROR

Phase
1

Phase
2

SBINIT

Phase
1

Management Transport path on the
sideband is negotiated/initialized,
chiplet "stalls" in MBINIT. PARAM
for additional "Init" time

MBINIT.PARAM
(MBINIT.Stall
mechanism used
for additional Init
time in Phase 1)

Phase
2

Mainband is trained

MBINIT. CAL

</figure>

Figure 4-40 shows a scenario in which the link training state machine initially moves through
RESET -> SBINIT -> MBINIT.PARAM with "stall". The chiplet "stalls" in MBINIT.PARAM for additional
Init time. After the chiplet Init is complete, the chiplet sends an {MBINIT.PARAM SBFE resp} sideband
message without a "stall" encoding that triggers state machine entry to MBINIT.CAL. Mainband
training resumes from that point.

<figure>
<figcaption>Figure 4-40. MBINIT "Stall" Example 2</figcaption>

Sideband Management path setup occurs first, followed by mainband training
without re-entering RESET state.

"Stall" in MBINIT.PARAM is used to gain additional time for chiplet initialization
before training the mainband.

RESET

TRAIN ERROR

Phase
1

SBINIT

Phase
1

Management Transport path on the
sideband is negotiated/initialized,
chiplet "stalls" in MBINIT.PARAM
for additional "Init" time

MBINIT.PARAM
(MBINIT. Stall
mechanism used
for additional Init
time in Phase 1)

Phase
2

Mainband is trained

Phase
2

MBINIT. CAL

</figure>

### 4.5.3.3.1.3 UCIe-S Sideband Only (SO) Port

A UCIe-S Sideband-only port will advertise the SFES bit in an {MBINIT.PARAM configuration req}
sideband message. If that negotiation is successful, the port advertises bit 2 (SO bit) in an
{MBINIT.PARAM SBFE req} sideband message to indicate that the port is a "Sideband-only port". If
the port receives an {MBINIT.PARAM SBFE resp} sideband message with the SO bit set to 1, training
pauses on both sides at the exit of the MBINIT.PARAM phase until the next Management Reset or a
transition to the TRAINERROR state is triggered (see Section 4.5.3.8). State residency timeout is
disabled in MBINIT.PARAM. If the remote link partner did not set the SO bit in the {MBINIT.PARAM
SBFE resp} sideband message, the link goes to the TRAINERROR state. This is an SiP integration error
and is fatal. All links that support management transport over sideband (i.e., those links that set bit 0
as 1 in the {MBINIT.PARAM SBFE req} sideband message that they transmit) must set the SO bit to 1
in the {MBINIT.PARAM SBFE resp} sideband message that they transmit, provided that the
corresponding bit was set to 1 in the {MBINIT.PARAM SBFE req} sideband message that they
received.

In multi-sideband-only Link configuration (this refers to a multi-module configuration with sideband-
only modules; see Section 8.2.1), the chiplet must advertise the same value for the SO bit in the
{MBINIT.PARAM SBFE req} or {MBINIT.PARAM SBFE resp} sideband message across all links.
Receivers can optionally check for violation of this rule and then trigger a transition to the
TRAINERROR state if the transmitter violates this rule.

### 4.5.3.3.2 MBINIT.CAL

This state is used to perform any calibration needed (e.g., Tx Duty Cycle correction, Receiver offset
and Vref calibration). This state is common for both Advanced Package and Standard Package.

1\. The UCIe Module maintains tri-state on all its mainband Transmitters, and mainband Receivers
are permitted to be disabled in this state. The UCIe Module is permitted to perform
implementation specific steps for Transmitter and Receiver calibration.

2\. The UCIe Module must send the {MBINIT.CAL Done req} sideband message, and then wait for a
response. If this message is received successfully, the UCIe Module Partner responds with the
{MBINIT.CAL Done resp} sideband message. Once the UCIe Module has sent and received
{MBINIT.CAL Done resp}, it must exit to MBINIT.REPAIRCLK.

### 4.5.3.3.3 MBINIT.REPAIRCLK

This sub-state is used to detect and apply repair (if needed) to clock and track Lanes for Advanced
Package and for functional check of clock and track Lanes for Standard Package.

Following is the sequence for Advanced Package:

Clock repair mapping is described in Section 4.3. Each clock, track and their redundant physical Lanes
(TCKP_P/RCKP_P, TCKN_P/RCKN_P, TTRK_P/RTRK_P, and TRDCK_P/RRDCK_P) are independently
checked to detect possible electrical opens or electrical shorts between the two clock pins. Single-
ended clock Receivers or independent detection mechanism is required to ensure clock repair. The
UCIe Module must enable Transmitters and Receivers on Clock, Track and their redundant Lanes. All
other Transmitters are maintained in tri-state and Receivers are permitted to be disabled.

1\. The UCIe Module sends the {MBINIT.REPAIRCLK init req} sideband message and waits for a
response. The UCIe Module Partner when ready to receive pattern on RCKP_L, RCKN_L, RTRK_L,
and RRDCK_L responds with {MBINIT.REPAIRCLK init resp}.

2\. The UCIe Module must now send 128 iterations of clock repair pattern (16 clock cycles followed
by 8 cycles of low) on its TCKP_L only (TCKN_L, TTRK_L, and TRDCK_L are tri-stated). Clock
repair pattern must not be scrambled.

3\. The UCIe Module Partner detects this pattern on RCKP_L, RCKN_L, RTRK_L, and RRDCK_L.
Detection is considered successful if at least 16 consecutive iterations of clock repair pattern are
detected. The UCIe Module Partner logs the detection result for RCKP_L, RCKN_L, RTRK_L, and
RRDCK L.
_

4\. The UCIe Module after completing pattern transmission sends {MBINIT.REPAIRCLK result req}
sideband message to get the logged result and waits for a response.

5\. The UCIe Module Partner responds with {MBINIT.REPAIRCLK result resp} sideband message with
log result of RCKP_L, RCKN_L, RTRK_L, and RRDCK_L. If detection is successful on RCKP_L only
and not on any of RCKN_L, RTRK, and/or RRDCK_L, no repair is needed. Else if detection is
unsuccessful on any of RCKP_L, RCKN_L, RTRK_L, and RRDCK_L, repair is needed on the physical
Lane TCKP_P/RCKP_P. Else an electrical short is implied.

6\. After receiving the {MBINIT.REPAIRCLK result resp} sideband message, the UCIe Module sends
the sideband message {MBINIT.REPAIRCLK init req} and waits for a response. The UCIe Module
Partner when ready to receive pattern on RCKP_L, RCKN_L, RTRK_L, RRDCK_L responds with
{MBINIT.REPAIRCLK init resp}.

7\. After receiving the {MBINIT.REPAIRCLK init resp} sideband message, the UCIe Module must send
128 iterations of clock repair pattern (16 clock cycles followed by 8 cycles of low) on its TCKN_L
only. (TCKP_L, TTRK_L, and TRDCK_L are tri-stated)

8\. The UCIe Module Partner detects this pattern on all RCKP_L, RCKN_L, RTRK_L, and RRDCK_L.
Detection is considered successful if at least 16 consecutive cycles of clock repair pattern are
detected. The UCIe Module Partner logs the detection result for RCKP_L, RCKN_L, RTRK_L, and
RRDCK L.
_

9\. The UCIe Module after completing the pattern transmission, sends {MBINIT.REPAIRCLK result
req} sideband message to get the logged result.

10\. The UCIe Module Partner on receiving it responds with {MBINIT.REPAIRCLK result resp} sideband
message with logged result of RCKP_L, RCKN_L, RTRK_L, and RRDCK_L. If detection is successful
on RCKN_L and not on RCKP_L, RTRK_L, RRDCK_L, no repair is needed. Else if detection is
unsuccessful on any of RCKP_L, RCKN_L, RTRK_L, and RRDCK_L, repair is needed on the physical
Lane TCKN_P/RCKN_P. Else an electrical short is implied.

11\. After receiving the {MBINIT.REPAIRCLK result resp} sideband message, the UCIe Module sends
the sideband message {MBINIT.REPAIRCLK init req}. The UCIe Module Partner when ready to
receive pattern on RCKP_L, RCKN_L, RTRK_L, RRDCK_L responds with {MBINIT.REPAIRCLK init
resp}.

12\. After receiving the {MBINIT.REPAIRCLK init resp} sideband message, the UCIe Module sends 128
iterations of clock repair pattern (16 clock cycles followed by 8 cycles of low) on TRDCK_L only.
(TCKP_L, TTRK_L, and TCKN_L tri-stated)

13\. The UCIe Module Partner detects this pattern on all RCKP_L, RCKN_L, RTRK_L, and RRDCK_L.
Detection is considered successful if at least 16 consecutive cycles of clock repair pattern are
detected. The UCIe Module Partner logs the detection result for RCKP_L, RCKN_L, RTRK_L, and
RRDCK L.
_

14\. The UCIe Module device after completing the pattern transmission sends {MBINIT.REPAIRCLK
result req} sideband message to get the logged result.

15\. The UCIe Module Partner responds with {MBINIT.REPAIRCLK result resp} sideband message with
logged result of RCKP_L, RCKN_L, RTRK_L, and RRDCK_L. If detection is successful only on
RRDCK_L and not on RCKP_L, RTRK_L, RCKN_L, TRDCK_P/RRDCK_P is available as a repair
resource. Else if detection is unsuccessful on any of RCKP_L, RCKN_L, RTRK_L, and RRDCK_L,
the physical Lane TRDCK_P/RRDCK_P is not available as a repair resource. Else an electrical short
is implied.

16\. After receiving the {MBINIT.REPAIRCLK result resp} sideband message, the UCIe Module sends
the sideband message {MBINIT.REPAIRCLK init req} and waits for a response. The UCIe Module
Partner when ready to receive pattern on RCKP_L, RCKN_L, RTRK_L, RRDCK_L responds with
{MBINIT.REPAIRCLK init resp}.

17\. After receiving the {MBINIT.REPAIRCLK init resp} sideband message, the UCIe Module sends 128
iterations of clock repair pattern (16 clock cycles followed by 8 cycles of low) on TTRK_L only.
(TCKP_L, TCKN_L, and TRDCK_L are tri-stated).

18\. The UCIe Module Partner detects this pattern on all RCKP_L, RCKN_L, RTRK_L, and RRDCK_L.
Detection is considered successful if at least 16 consecutive cycles of clock repair pattern are
detected. The UCIe Module Partner logs the detection result for RCKP_L, RCKN_L, RTRK_L, and
RRDCK L.

19\. The UCIe Module after completing pattern transmission sends {MBINIT.REPAIRCLK result req}
sideband message to get the logged result and waits for a response.

20\. The UCIe Module Partner stops comparison and responds with {MBINIT.REPAIRCLK result resp}
sideband message with logged result of RCKP_L, RCKN_L, RTRK_L, and RRDCK_L. If detection is
successful only on RTRK_L and not on RCKP_L, RCKN_L, RRDCK_L, no repair is needed. Else if
detection is unsuccessful on any of RCKP_L, RCKN_L, RTRK_L, and RRDCK_L, repair is needed on
the physical Lane TTRK_P/RTRK_P. Else an electrical short is implied.

21\. Clock or Track is unrepairable if any of the following are true:

\- If repair is needed on any two of RCKP_L, RCKN_L, and RTRK_L

\- Electrical short is detected

\- RRDCK_L is unavailable for repair when repair is needed

If the clock or track is unrepairable, the UCIe Module and UCIe Module Partner must exit to
TRAINERROR after performing TRAINERROR handshake (see Section 4.5.3.8).

If repair is required on only one of the clock or track lanes and a repair resource is available, then
the UCIe Module applies repair on its clock/track Transmitter and sends the {MBINIT.REPAIRCLK
apply repair req} sideband message with repair information. If a repair is needed for one of the
clock or track pins (CKP, CKN, or TRK) and a repair resource is available, repair is applied as
described in Section 4.3. The UCIe Module Partner applies repair and sends {MBINIT.REPAIRCLK
apply repair resp} sideband message.

22\. If a repair is applied, UCIe Module must check the repair success by applying clock repair pattern
and checking on the Receiver.

a. The UCIe Module sends sideband message {MBINIT.REPAIRCLK check repair init req} to
initiate check repair and waits for a response. The UCIe Module Partner responds with sideband
message {MBINIT.REPAIRCLK check repair init resp} and is ready to receive and check clock
repair pattern.

b. After receiving the {MBINIT.REPAIRCLK check repair init resp} sideband message, the UCIe
Module sends 128 iterations of clock repair pattern (16 clock cycles followed by 8 cycles of low)
on TCKP_L. The UCIe Module Partner detects this pattern RCKN_L, RCKP_L, RTRK_L.
Detection is considered successful if at least 16 consecutive cycles of clock repair pattern are
detected. The UCIe Module requests for check result request using the sideband message

{MBINIT.REPAIRCLK check results req} and the UCIe Module Partner responds with the
sideband message {MBINIT.REPAIRCLK check results resp}. Repair is considered successful if
pattern is detected only on RCKP_L. If repair is unsuccessful, the UCIe Module and UCIe
Module Partner must exit to TRAINERROR after performing TRAINERROR handshake (see
Section 4.5.3.8).

c. Step a and Step b are repeated for TCKN_L and TTRK_L.

23\. If repair is successful or repair is not required, the UCIe Module sends {MBINIT.REPAIRCLK done
req} sideband message and the UCIe Module Partner responds with {MBINIT.REPAIRCLK done
resp} sideband message. When the UCIe Module has sent and received {MBINIT.REPAIRCLK done
resp}, it must exit to REPAIRVAL.

For Standard Package, clock and track Lanes are checked for functional operation at the lowest data
rate. The sequence is as follows:

1\. The UCIe Module sends the sideband message {MBINIT.REPAIRCLK init req} and waits for a
response. When ready to receive pattern on RCKP_L, RCKN_L, and RTRK_L, the UCIe Module
Partner responds with {MBINIT.REPAIRCLK init resp}. On receiving the sideband message
{MBINIT.REPAIRCLK init resp}, the UCIe Module sends 128 iterations of clock repair pattern
(16 clock cycles followed by 8 cycles of low) on TCKP_L, TCKN_L, and TTRK_L. Clock repair
pattern must not be scrambled.

2\. The UCIe Module Partner detects this pattern on RCKP_L, RCKN_L, and RTRK_L. Detection is
considered successful if at least 16 consecutive cycles of clock repair pattern are detected. The
UCIe Module Partner logs the detection result for RCKP_L, RCKN_L, and RTRK_L.

3\. After completing pattern transmission, the UCIe Module sends {MBINIT.REPAIRCLK result req}
sideband message to get the logged result.

4\. The UCIe Module Partner stops comparison and responds with {MBINIT.REPAIRCLK result resp}
sideband message with logged result of RCKP_L, RCKN_L, and RTRK_L.

5\. If detection is unsuccessful on any one of RCKP_L, RCKN_L, and RTRK_L, the UCIe Module and
UCIe Module Partner must exit to TRAINERROR after performing TRAINERROR handshake.

6\. If detection is successful, the UCIe Module sends {MBINIT.REPAIRCLK done req} sideband
message and the UCIe Module Partner responds with {MBINIT.REPAIRCLK done resp} sideband
message. When the UCIe Module has sent and received the sideband message
{MBINIT.REPAIRCLK done resp}, it must exit to MBINIT.REPAIRVAL.

### 4.5.3.3.4 MBINIT.REPAIRVAL

The UCIe Module sets the clock phase at the center of the data UI. The UCIe Module Partner must
sample the received Valid with the received forwarded Clock. All Data Lanes must be held low during
this state. Track and Data Receivers are permitted to be disabled. When not performing the actions
relevant to this state:

· Clock Transmitters are held differential low (for differential clocking) or simultaneous low (for
Quadrature clocking)

. Clock Receivers are enabled

· When not transmitting the VALTRAIN pattern, the transmitters for TVLD_L and TRDVLD_L are
disabled (tri-stated)

. The receivers for RVLD L and RRDVLD L are enabled

This state can be used to detect and apply repair (if needed) to Valid Lane for Advanced Package
and for functional check of Valid for Standard Package.

Following is the sequence for Advanced Package:

1\. The UCIe Module sends the sideband message {MBINIT.REPAIRVAL init req} and waits for a
response. When ready to receive pattern on RVLD_L and RRDVLD_L, the UCIe Module Partner
clears any previous comparison results and responds with {MBINIT.REPAIRVAL init resp}.

2\. The UCIe Module on receiving {MBINIT.REPAIRVAL init resp} must send 128 iterations of
VALTRAIN pattern (four 1's followed by four 0's) on TVLD_L along with the forwarded clock.
VALTRAIN pattern must not be scrambled.

3\. The UCIe Module Partner detects pattern on RVLD_L and RRDVLD_L. Detection is considered
successful if at least 16 consecutive iterations of VALTRAIN pattern are detected. The Receiver
logs the detection result for RVLD_L and RRDVLD_L.

4\. After completing the pattern transmission, the UCIe Module must send {MBINIT.REPAIRVAL result
req} sideband message and wait to get the logged result.

5\. The UCIe Module Partner must respond with {MBINIT.REPAIRVAL result resp} sideband message
with result in the previous step. If detection is successful on RVLD_L only and not on RRDVLD_L,
no repair is needed. If detection is successful on both RVLD_L and RRDVLD_L or only on
RRDVLD_L, the interconnect cannot be repaired. If detection is unsuccessful on both RVLD_L and
RRDVLD_L, Valid Lane (TVLD_P/RVLD_P) needs repair.

6\. After receiving {MBINIT.REPAIRVAL result resp}, Step 1 must be repeated.

7\. The UCIe Module sends 128 iterations of VALTRAIN repair pattern (four 1's followed by four 0's)
on TRDVLD_L along with the forwarded clock. VALTRAIN pattern must not be scrambled.

8\. The UCIe Module Partner detects pattern on RVLD_L and RRDVLD_L. Detection is considered
successful if at least 16 consecutive iterations of VALTRAIN pattern are detected. The Receiver
logs the detection result for RVLD_L and RRDVLD_L.

9\. After completing the pattern transmission, the UCIe Module must send {MBINIT.REPAIRVAL result
req} sideband message to get the logged result.

10\. The UCIe Module Partner must stop comparison and respond with {MBINIT.REPAIRVAL result
resp} sideband message with result from the previous step. If detection is successful on
RRDVLD_L only and not on RVLD_L, TRDVLD_P/RRDVLD_P is available for repair. If detection is
successful on both RVLD_L and RRDVLD_L or only on RVLD_L, the interconnect cannot be
repaired. If detection is unsuccessful on both RVLD_L and RRDVLD_L, TRDVLD_P/RRDVLD_P is
not available and cannot be used for Valid Lane repair.

11\. If repair is required on (TVLD_P/RVLD_P) and repair resource is available, the UCIe Module
applies repair on its Valid Transmitter (see Section 4.3.7) and sends sideband message
{MBINIT.REPAIRVAL apply repair req} with repair information. The UCIe Module Partner, after
receiving the message, must apply repair on its Valid Receiver and must respond with sideband
message {MBINIT.REPAIRVAL apply repair resp}.

12\. If a repair is applied, device must check the repair success by repeating Step 1 through Step 4.

13\. If repair is successful or repair is not required, the UCIe Module must send {MBINIT.REPAIRVAL
done req} sideband message and the UCIe Module Partner must respond with
{MBINIT.REPAIRVAL done resp}. When a UCIe Module has sent and received {MBINIT.REPAIRVAL
done resp} sideband message, it must exit to REVERSALMB. Else if repair is unsuccessful or Valid
Lane is unrepairable (in Step 11), the UCIe Module must exit to TRAINERROR after completing
the TRAINERROR handshake.

For Standard Package, Valid Lane is checked for functional operation at the lowest data rate.
Following is the flow:

1\. The UCIe Module must send the sideband message {MBINIT.REPAIRVAL init req} and wait for
a response. The UCIe Module Partner when ready to receive pattern on RVLD_L, must respond
with {MBINIT.REPAIRVAL init resp}.

2\. After receiving the sideband message {MBINIT.REPAIRVAL init resp}, the UCIe Module sends
128 iterations of VALTRAIN pattern (four 1's followed by four 0's) on TVLD_L along with the
forwarded clock.

3\. The UCIe Module Partner detects this pattern on RVLD_L. Detection is considered successful
if at least 16 consecutive iterations of valid repair pattern are detected. The Receiver logs the
detection result for RVLD_L.

4\. After completing pattern transmission, the UCIe Module must send {MBINIT.REPAIRVAL result
req} sideband message and wait to get the logged result.

5\. The UCIe Module Partner must stop comparison and respond with {MBINIT.REPAIRVAL result
resp} sideband message with result in the previous step.

6\. If detection fails, the UCIe Module must exit to TRAINERROR after completing the TRAINERROR
handshake.

7\. If detection is successful, the UCIe Module must send {MBINIT.REPAIRVAL done req} sideband
message and the UCIe Module Partner responds with {MBINIT.REPAIRVAL done resp}. When a
UCIe Module has sent and received {MBINIT.REPAIRVAL done resp} sideband message, it must
exit to REVERSALMB.

### 4.5.3.3.5 MBINIT.REVERSALMB

This state is entered only if Clock and Valid Lanes are functional. In this state, Data Lane reversal is
detected. All the Transmitters and Receivers are enabled. The UCIe Module sets the forwarded clock
phase at the center of the data UI. The UCIe Module Partner must sample the incoming Data with the
incoming forwarded clock. The Track Transmitter is held low and the Track Receiver is permitted to be
disabled. When not performing the actions relevant to this state:

· Clock Transmitters are held differential low (for differential clocking) or simultaneous low (for
Quadrature clocking)

· Clock Receivers are enabled

· Data and Valid Transmitters are held low

· Data and Valid Receivers are enabled

A 16-bit "Per Lane ID" pattern, shown in Table 4-7, is a Lane-specific pattern using the Lane ID
described in Section 4.2.1. Example of "Per Lane ID" pattern for Lane 1 and Lane 31 are shown in
Table 4-8. When "Per Lane ID" pattern is used, it must not be scrambled.

<table>
<caption>Table 4-7. Per Lane ID Pattern</caption>
<tr>
<td>Pattern</td>
<td>0</td>
<td>1</td>
<td>0</td>
<td>1</td>
<td></td>
<td></td>
<td colspan="5">Lane IDª</td>
<td></td>
<td>0</td>
<td>1</td>
<td>0</td>
<td>1</td>
</tr>
<tr>
<td>Bit</td>
<td>0</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>123456789</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>10</td>
<td>11</td>
<td>12</td>
<td>13</td>
<td>14</td>
<td>15</td>
</tr>
</table>

a. Note that bit 0 of Lane ID maps to bit 4 in the Per Lane ID pattern, bit 1 to bit 5 and so on until bit 7 to bit 11.

<table>
<caption>Table 4-8. Per Lane ID Pattern Examples</caption>
<tr>
<td>Lane 1</td>
<td>0</td>
<td>1</td>
<td>0</td>
<td>1</td>
<td>1</td>
<td>0</td>
<td>0</td>
<td>0</td>
<td>0</td>
<td>0</td>
<td>0</td>
<td>0</td>
<td>0</td>
<td>1</td>
<td>0</td>
<td>1</td>
</tr>
<tr>
<td>Lane 31</td>
<td>0</td>
<td>1</td>
<td>0</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>1111110000</td>
<td></td>
<td></td>
<td>1</td>
<td>0</td>
<td>1</td>
</tr>
<tr>
<td>Bit</td>
<td>0</td>
<td>1</td>
<td>2</td>
<td>3</td>
<td>4</td>
<td>5</td>
<td>6</td>
<td>7</td>
<td>8</td>
<td>9</td>
<td>10</td>
<td>11</td>
<td>12</td>
<td>13</td>
<td>14</td>
<td>15</td>
</tr>
</table>

Following is the Reversal MB sequence for Advanced Package and Standard Package:

1\. The UCIe Module must send the {MBINIT.REVERSALMB init req} sideband message. When ready
to receive "Per Lane ID" pattern and perform per-Lane pattern comparison, the UCIe Module
Partner must respond with {MBINIT.REVERSALMB init resp}.

2\. On Receiving the {MBINIT.REVERSALMB init resp} sideband message or entering from Step 8, the
UCIe Module must send {MBINIT.REVERSALMB clear error req} sideband message. Upon
receiving this message, the UCIe Module Partner clears any prior errors and responds with
{MBINIT.REVERSALMB clear error resp}. After receiving {MBINIT.REVERSALMB clear error resp},
the UCIe Module sends 128 iterations of Per Lane ID pattern (see Table 4-7) on all N data Lanes
with correct Valid framing on the Valid Lane (see Section 5.11 and Section 4.1.2) along with the
clock. Table 4-7 and Table 4-8 show examples of the Per Lane ID pattern. N is 68 (64
$\left. D a t a + 4 \quad R D \right) f o r$ a x64 Advanced Package. N is 34 (32 Data + 2 RD) for a x32 Advanced Package.
N is 16 for a x16 Standard Package. N is 8 for a x8 Standard Package.

3\. The UCIe Module Partner must perform a per-Lane compare on its Receivers on all N Lanes (see
Section 4.4). Detection on a Lane is considered successful if at least 16 consecutive iterations of
"Per Lane ID" pattern are detected. The UCIe Module Partner logs the detection result for its
Receiver Lanes to be used for Lane reversal Detection.

4\. After sending 128 iterations of "Per Lane ID" pattern, the UCIe Module stops sending the pattern
and sends {MBINIT.REVERSALMB result req} sideband message to get the logged result.

5\. The UCIe Module Partner stops comparison and must respond with {MBINIT.REVERSALMB result
resp} sideband message with per Lane result (see Table 7-11 for the message format).

6\. If majority of the Lanes show success (since some Lanes may need repair), Lane reversal is not
needed. Skip to Step 11. Note that if exactly 50% of the Lanes showed success, Lane reversal is
applied.

7\. The UCIe Module applies Lane reversal on its Transmitters (see Section 4.2).

8\. Following the Lane reversal application on its Transmitters, the UCIe Module repeats Step 2
through Step 5.

9\. If majority of Lanes show success, the Lane reversal is needed. Lane reversal preserved for rest
of the device operation. Skip to Step 11.

10\. The UCIe Module must exit to TRAINERROR after completing the TRAINERROR handshake.

11\. The UCIe Module must send {MBINIT.REVERSALMB done req} sideband message and the UCIe
Module Partner responds with {MBINIT.REVERSALMB done resp}. When the UCIe Module has sent
and received {MBINIT.REVERSALMB done resp} sideband message, it must exit to REPAIRMB.

If a x64 Advanced Package Module that supports interoperation with a x32 Advanced Package module
had received "UCIe-A x32" as 1b during parameter exchanges, it must recognize that it is connected
to a x32 Advanced Package Module and appropriately interpret the received {MBINIT.REVERSALMB
result resp} sideband message. In this scenario, the x64 applies steps 6 through 9 to lower 32 data
lane set and 2 repair lane set. The x64 module applies Lane reversal (if required) within the lower 32
data lane set and 2 repair lane set.

If a x32 Advanced Package Module had received "UCIe-A x32" as Ob during parameter exchanges, it
must recognize that it is connected to a x64 Advanced Package Module and appropriately interpret the

received {MBINIT.REVERSALMB result resp} sideband message, looking for majority of success in the
lower 32 data lane set and 2 repair lane set of the x64 module (the x64 module will always place the
results of its receiver on the lower half of its data/repair lane set).

If a x16 Standard Package Module that supports interoperation with a x8 Standard Package Module
had its SPMW bit set to 1b OR has transmitted or received "UCIe-S x8" as 1b during parameter
exchanges, the x16 Standard Package Module must recognize that it needs to operate in x8 mode and
appropriately interpret the received {MBINIT.REVERSALMB result resp} sideband message. In this
scenario, the x16 Standard Package Module applies Step 6 through Step 9 to the lower-8 data-lane
set. Additionally, the x16 Standard Package Module applies Lane reversal (if required) within the
lower-8 data-lane set.

When a x8 Standard Package Module receives the {MBINIT.REVERSALMB result resp} sideband
message, the module must look for majority of success in the bits that correspond to the lower-8
data-lane set only.

### 4.5.3.3.6 MBINIT.REPAIRMB

This state is entered only after Lane reversal detection and application is successful. All the
Transmitters and Receivers on a UCIe Module are enabled. The UCIe Module sets the clock phase at
the center of the data UI on its mainband Transmitter for data Lanes (including the redundant Lanes
for Advanced Package). The UCIe Module Partner must sample the incoming Data with the incoming
forwarded clock on its mainband Receivers for data Lanes (including the redundant Lanes for
Advanced Package). The Track Transmitter is held low and the Track Receiver is permitted to be
disabled. When not performing the actions relevant to this state:

· Clock Transmitters are held differential low (for differential clocking) or simultaneous low (for
Quadrature clocking)

· Clock Receivers are enabled

· Data and Valid Transmitters are held low

· Data and Valid Receivers are enabled

In this state, the mainband Lanes are detected and repaired (if needed) for Advanced Package. In
this state, functional checks and width degrade (if needed) are performed for Standard Package.

Following is the sequence for Advanced Package:

1\. The UCIe Module must send the {MBINIT.REPAIRMB start req} sideband message and waits for a
response. The UCIe Module Partner responds with {MBINIT.REPAIRMB start resp}.

2\. The UCIe Module device performs Transmitter-initiated Data-to-Clock point test as described in
Section 4.5.1.1 on its Transmitter Lanes (all the data Lanes including the redundant Lanes). The
Receiver must check for the pass/fail criteria on the data Lanes and the redundant Lanes.

a. The transmit pattern must be set up to send 128 iterations of continuous mode "Per Lane ID"
Pattern. "Per Lane ID" pattern must not be scrambled. The Receiver must be set up to perform
per Lane comparison.

b. Detection on a Receiver Lane is considered successful if at least 16 consecutive iterations of
"Per Lane ID" pattern are detected.

c. LFSR Reset has no impact in MBINIT.REPAIRMB.

3\. The UCIe Module receives the per-Lane pass/fail information over sideband message at the end
of Transmitter initiated data to clock point test Step 2.

4\. If Lane repair is required and the necessary repair resources are available, the UCIe Module
applies repair on its mainband Transmitters for data Lanes as described in Section 4.3.1, and
sends {MBINIT.REPAIRMB Apply repair req} sideband message. Upon receiving this sideband
message, the UCIe Module Partner applies repair on its mainband Receivers for data Lanes as
described in Section 4.3.1, and sends {MBINIT.REPAIRMB Apply repair resp} sideband message.
Otherwise, if the number of Lane failures are more than repair capability (see Section 4.3), the
mainband is unrepairable and the UCIe Module must exit to TRAINERROR after performing the
TRAINERROR handshake.

5\. If repair is not required, perform Step 7.

6\. If Lane repair is applied (Step 4), the applied repair is checked by UCIe Module by repeating
Step 2 and Step 3. If post repair Lane errors are logged in Step 5, the UCIe Module must exit to
TRAINERROR after performing the TRAINERROR handshake. If repair is successful, perform
Step 7.

7\. The UCIe Module sends {MBINIT.REPAIRMB end req} sideband message and the UCIe Module
Partner responds with {MBINIT.REPAIRMB end resp}. When UCIe Module has sent and received
{MBINIT.REPAIRMB end resp}, it must exit to MBTRAIN.

For Standard Package, mainband is checked for functional operation at the lowest data rate.
Following is the sequence of steps:

1\. The UCIe Module sends the {MBINIT.REPAIRMB start req} sideband message and waits for a
response. The UCIe Module Partner responds with the {MBINIT.REPAIRMB start resp} sideband
message when ready to receive the pattern on its mainband Receivers for data Lanes.

2\. The UCIe Module performs Transmitter-initiated Data-to-Clock point test as described in
Section 4.5.

a. The transmit pattern must be set up to send 128 iterations of continuous mode "Per Lane ID"
Pattern. The Receiver must be set up to perform per Lane comparison.

b. Detection on a Receiver Lane is considered successful if at least 16 consecutive iterations of
"Per Lane ID" pattern are detected.

c. LFSR Reset has no impact in MBINIT.REPAIRMB.

3\. The UCIe Module must send the {MBINIT.REPAIRMB apply degrade req} sideband message
indicating the functional Lanes on its Transmitter using one of the logical Lane map encodings
from Table 4-9. Encodings 100b and 101b can be used only when the SPMW bit is set to 1 or the
UCIe-S x8 bit was set to 1 in the transmitted or received {MBINIT.PARAM configuration req}
sideband message. If the remote Link partner indicated a width degrade in the functional Lanes,
the UCIe Module must apply the corresponding width degrade to its Receiver. If the remote Link
partner indicated all Lanes are functional (i.e. a Lane map code of 011b), the UCIe Module sets its
Transmitter and Receiver to the width corresponding to the functional Lane encoding determined
on its Transmitter. The UCIe Module sends the {MBINIT.REPAIRMB apply degrade resp} sideband
message after setting its Transmitter and Receiver lanes to the relevant width. If the width on the
Transmitter or Receiver has changed, both Link partners must repeat Step 2. If the width on the
Transmitter or Receiver has not changed, proceed to Step 4. If a "Degrade not possible" encoding
is sent or received in the {MBINIT.REPAIRMB apply degrade req} sideband message, the UCIe
Module must exit to TRAINERROR after performing the TRAINERROR handshake.

4\. The UCIe Module sends the {MBINIT.REPAIRMB end req} sideband message and the UCIe Module
Partner responds with the {MBINIT.REPAIRMB end resp} sideband message. When the UCIe
Module has sent and received the {MBINIT.REPAIRMB end resp} sideband message, it must exit
to MBTRAIN.

<table>
<caption>Table 4-9. Standard Package Logical Lane Map</caption>
<tr>
<th>Lane Map Code</th>
<th>Functional Lanes</th>
</tr>
<tr>
<td>000b</td>
<td>None (Degrade not possible)</td>
</tr>
<tr>
<td>001b</td>
<td>Logical $\mathrm { L a n e s } 0$ to 7</td>
</tr>
<tr>
<td>010b</td>
<td>Logical Lanes 8 to 15</td>
</tr>
<tr>
<td>011b</td>
<td>0 - 15</td>
</tr>
<tr>
<td>100b</td>
<td>Logical Lanes 0 to 3</td>
</tr>
<tr>
<td>$1 0 1 b$</td>
<td>Logical Lanes 4 to 7</td>
</tr>
</table>

### IMPLEMENTATION NOTE

Consider an example in which Die A is communicating with Die B over a Standard
Package UCIe Link.

During the first iteration of Step 2 of MBINIT.REPAIRMB, let's say that Tx on Die A
detects errors on Lane ID 1 and not on any other Lanes, but Tx on Die B detects
errors on Lane ID 10 and not on any other Lanes. Thus, as per the rules in Step 3, Die
A sends {MBINIT.REPAIRMB apply degrade req} with a Lane map code of 010b.
Similarly, in Step 3, Die B sends {MBINIT.REPAIRMB apply degrade req} with a Lane
map code of 001b. The Rx on Die B disables Lanes 0 to 7, and the Tx on Die B tri-
states Lanes 8 to 15. The Rx on Die A disables Lanes 8 to 15, and the Tx on Die A tri-
states Lanes 0 to 7. Following the rules in Step 3, each die goes back and repeats
Step 2.

In this second iteration of Step 2, both Die know that some of the Lanes are disabled,
and they will ignore the information related to the disabled Lanes in {Tx Init D to C
results resp} (e.g., Die A will ignore the information related to Lanes 0 to 7 and
perform only the Transmitter-initiated Data to Clock point test on Lanes 8 to 15).

Let's say that in the second iteration of Step 2, no errors are reported on the enabled
Lanes. In Step 3, Die A sends {MBINIT.REPAIRMB apply degrade req} with a Lane
map code of 010b. Similarly, in Step 3, Die B sends {MBINIT.REPAIRMB apply
degrade req} with a Lane map code of 001b. Because the width of the Tx and Rx
have not changed, both Die proceed to Step 4.

### 4.5.3.4 MBTRAIN

MBTRAIN state is used to setup operational speed and perform clock to data centering. At higher
speeds, additional calibrations like Rx clock correction, Tx and Rx deskew may be needed to ensure
Link performance. MBTRAIN uses sub-states to perform all the required calibration and training. UCIe
Modules must enter each sub-state and the exit from each sub-state is coordinated between UCIe
Module Partners through sideband handshakes. If a particular action within a sub-state is not needed,
the UCIe Module is permitted to exit the sub-state through the relevant sideband handshake without
performing the described operations in that sub-state.

Devices enter this state once the MBINIT is completed. This state is common for Advanced and
Standard Packages.

<figure>
<figcaption>Figure 4-41. Mainband Training</figcaption>

From MBINIT

VALVREF

VALTRAIN
$\mathrm { C E N T E R }$

DATAVREF

VALTRAIN
VREF

$F r o m \quad L 1$

SPEED
IDLE

DATATRAIN
CENTER1

From PHYRETRAIN

TXSELFCAL

DATATRAIN
VREF

REPAIR

RXCLKCAL

RXDESKEW

DATATRAIN
CENTER2

LINKSPEED

To PHYRETRAIN

To LINKINIT

</figure>

#### 4.5.3.4.1 MBTRAIN.VALVREF

Receiver reference voltage (Vref) to sample the incoming Valid is optimized in this state. The data
rate on the mainband continues to be at the lowest supported data rate (4 GT/s). The UCIe Module
Partner must set the forwarded clock phase at the center of the data UI on its mainband Transmitters.
The UCIe Module must sample the pattern on Valid signal with the forwarded clock. All data Lanes and
Track must be held low during Valid Lane reference voltage training. Track Receivers are permitted to
be disabled. When not performing the actions relevant to this state:

· Clock Transmitters are held differential low (for differential clocking) or simultaneous low (for
Quadrature clocking)

· Clock Receivers are enabled

The sequence for Valid Receiver reference voltage adjustment is as follows:

1\. The UCIe Module must send the {MBTRAIN. VALVREF start req} sideband message and wait for a
response. When {MBTRAIN.VALVREF start req} sideband message is received, the UCIe Module
Partner responds with {MBTRAIN. VALVREF start resp}.

2\. UCIe Module optimizes Vref on its Valid Receiver by adjusting Receiver reference voltage and
performing one or more Receiver-initiated Data-to-Clock point tests (see Section 4.5.1.3) (AND/
OR) one or more Receiver-initiated Data-to-Clock eye width sweeps (see Section 4.5.1.4).

a. The transmit pattern must be set to send 128 iterations of continuous mode "VALTRAIN" (four
1s and four 0s) pattern (see Table 4-5). This pattern must not be scrambled. The Receiver must
be set up to perform comparison on the Valid Lane.

b. Detection on a Receiver Lane is considered successful if "VALTRAIN" pattern detection errors
are less than the set threshold (per Lane comparison threshold in Section 9.5.3.29).

c. It should be noted that LFSR RESET has no impact in MBTRAIN. VALVREF.

3\. The UCIe Module must send {MBTRAIN. VALVREF end req} sideband message after the Vref
optimization (One way to perform Vref Optimization is to step through Vref and perform Step 2 at
each setting). When {MBTRAIN. VALVREF end req} is received, the UCIe Module Partner must
respond with {MBTRAIN. VALVREF end resp}. When the UCIe Module has sent and received the
sideband message {MBTRAIN. VALVREF end resp}, it must exit to MBTRAIN.DATAVREF.

### 4.5.3.4.2 MBTRAIN.DATAVREF

Receiver reference voltage (Vref) to sample the incoming data is optimized in this state. The data rate
on the UCIe Module mainband continues to be at the lowest supported data rate (4 GT/s). The
Transmitter sets the forwarded clock phase at the center of the data UI. The Track Transmitter is held
low and the Track Receiver is permitted to be disabled. When not performing the actions relevant to
this state:

· Clock Transmitters are held differential low (for differential clocking) or simultaneous low (for
Quadrature clocking)

· Clock Receivers are enabled

· Data and Valid Transmitters are held low

· Data and Valid Receivers are enabled

The sequence for data Receiver reference voltage adjustment is as follows:

1\. The UCIe Module sends the sideband message {MBTRAIN.DATAVREF start req}. When
{MBTRAIN.DATAVREF start req} sideband message is received, the UCIe Module Partner responds
with {MBTRAIN.DATAVREF start resp}.

2\. The UCIe Module optimizes data Vref by adjusting data Receiver reference voltage and
performing one or more Receiver-initiated Data-to-Clock point tests (see Section 4.5.1.3) (AND/
OR) one or more Receiver-initiated Data-to-Clock eye width sweeps (see Section 4.5.1.4).

a. The Transmitter must be set up to send 4K UI of continuous mode LFSR pattern described in
Section 4.4.1. The LFSR pattern on Data must be accompanied by correct Valid framing on the
Valid Lane as described in Section 4.1.2. The Receiver must be set up to perform per Lane
comparison.

b. Detection on a Receiver Lane is considered successful if total error count is less than the set
error threshold (see Section 9.5.3.29).

3\. The UCIe Module must send {MBTRAIN.DATAVREF end req} sideband message after the Vref
optimization (One way to perform Vref Optimization is to step through Vref and perform step 2 at
each setting). When {MBTRAIN.DATAVREF end req} is received, the UCIe Module Partner must
respond with {MBTRAIN.DATAVREF end resp}. Once the UCIe Module has sent and received the
sideband message {MBTRAIN.DATAVREF end resp}, it must exit to MBTRAIN.SPEEDIDLE.

### 4.5.3.4.3 MBTRAIN.SPEEDIDLE

This is an electrical idle state to allow frequency change. Clock Transmitters are held differential low
(for differential clocking) or simultaneous low (for Quadrature clocking). Clock Receivers are enabled.
Data, Valid, and Track Transmitters are held low.

The following rules apply:

1\. The data rate is determined as follows:

\- If this state is entered from MBTRAIN.DATAVREF, the UCIe Module transitions to a data rate
based on the highest common speed between the two devices (see Section 4.5.3.3.1).

\- Else if this state is entered from L1, the operating speed in the last ACTIVE state before
entering L1 must be restored.

\- Else if this state is entered from LINKSPEED or PHYRETRAIN (speed degrade), and the current
speed is not 4 GT/s, the next-lower data rate must be picked.

\- Else the UCIe Module must exit to TRAINERROR after performing the TRAINERROR
handshake.

2\. The width of the Link is set to the width previously determined at the exit of MBINIT.REPAIRMB or
MBTRAIN.REPAIR (whichever was the most-recent state relative to entry into SPEEDIDLE).

3\. Upon completing the transition to the required data rate, the UCIe Module must send
{MBTRAIN.SPEEDIDLE done req} sideband message. When {MBTRAIN.SPEEDIDLE done req}
sideband message is received, UCIe Module Partner responds with {MBTRAIN.SPEEDIDLE done
resp}. Once the UCIe Module has sent and received the {MBTRAIN.SPEEDIDLE done resp}
sideband message, it must exit to MBTRAIN.TXSELFCAL.

### 4.5.3.4.4 MBTRAIN.TXSELFCAL

The UCIe Module calibrates its circuit parameters independent of the UCIe Module Partner. Data,
Clock, Valid, and Track Transmitters are tri-stated. Data, Clock, Valid, and Track Receivers are
permitted to be disabled.

1\. UCIe Module is permitted to perform implementation specific Transmitter-related calibration.

2\. Upon completion of calibration, the UCIe Module must send the {MBTRAIN.TXSELFCAL Done req}
sideband message. When {MBTRAIN.TXSELFCAL Done req} sideband message is received, the
UCIe Module Partner must respond with {MBTRAIN.TXSELFCAL Done resp}. When the UCIe
Module has sent and received the {MBTRAIN.TXSELFCAL Done resp} sideband message, it must
exit to MBTRAIN. RXCLKCAL.

### 4.5.3.4.5 MBTRAIN.RXCLKCAL

In this state, Data, Valid Transmitters are held low (Data and Valid Receivers are permitted to be
disabled). When not performing the actions relevant to this state, if the operating speed is
<= 32 GT/s AND Strobe mode was advertised by the UCIe Module Partner, the Clock Transmitters are
held differential low (for differential clocking) or simultaneous low (for Quadrature clocking). When
not performing the actions relevant to this state, if the operating speed is > 32 GT/s OR continuous
clock mode was advertised by the UCIe Module Partner and the {MBTRAIN. RXCLKCAL start req}
sideband message has been received, then the Clock Transmitters are providing the free-running
forwarded clock.

1\. The UCIe Module, when ready to perform calibration on its Clock receive path, sends the
{MBTRAIN.RXCLKCAL start req} sideband message. When the {MBTRAIN.RXCLKCAL start req}
sideband message is received, the UCIe Module Partner starts sending the forwarded clock and
Track. Subsequently, the UCIe Module Partner sends the {MBTRAIN.RXCLKCAL start resp}
sideband message. The Transmitter clock must be free running and all Data Lanes and Valid must

be held low. If the operating speed is > 32 GT/s, the offset of TCKN_L relative to TCKP_L is set to
an implementation-specific default when entering this state for the first time since RESET state
exit or a speed degrade; otherwise, it is set to the value for the current speed from the last exit
from MBTRAIN.RXCLKCAL. The UCIe Module is permitted to use the forwarded clock to perform
any clock path-related and Clock-to-Track-related calibration. The UCIe Module Partner must not
adjust any circuit or PI phase parameters on its Transmitters within this state. If the operating
speed is $< = 3 2 \quad G T / s ,$ then proceed to Step 3.

2\. In this step, Rx of the UCIe Module is permitted to perform any required in-phase/quadrature (IQ)
correction on the received quarter rate clock by using the following sequence:

a. The UCIe Module Rx stops observing the incoming clock and track patterns, and subsequently
sends the {MBTRAIN.RXCLKCAL TCKN_L shift req} sideband message to request the UCIe
Module Partner to shift TCKN_L relative to TCKP_L. The parameters in this sideband message
contain a 5-bit "Shift Value" field that indicates the value of the shift from the current setting
with a step size of $1 / 6 4$ UI, as well as a 1-bit "Decrement" field that indicates that the request
is for an increment if it is cleared to 0, or for a decrement if it is set to 1. Here, "increment"
refers to shifting TCKN_L to be later in the phase relative to TCKP_L, and "decrement" refers
to shifting TCKN_L to be earlier in the phase relative to TCKP_L.

b. The UCIe Module Partner must apply the requested adjustment if it is within range of the
hardware implementation (see Section 5.5) and subsequently respond with
{MBTRAIN.RXCLKCAL TCKN_L shift resp} with a status that indicates the "Success" encoding.
If the requested adjustment is out of range of the hardware implementation, the UCIe Module
Partner does not apply the requested adjustment and responds with {MBTRAIN.RXCLKCAL
TCKN_L shift resp} with a status that indicates the "Out of Range" encoding.

c. The UCIe Module starts observing the incoming clock and track patterns only after the UCIe
Module has received a "Success" encoding on the {MBTRAIN.RXCLKCAL TCKN_L shift resp}
sideband message to check for acceptable in-phase/quadrature (I/Q) conditions and perform
any clock path-related calibration.

d. The UCIe Module returns to Step 2a if the UCIe Module needs to repeat this sequence for a
different setting; otherwise, the UCIe Module proceeds to Step 3.

3\. When the required calibration (if any) is performed, the UCIe Module sends {MBTRAIN.RXCLKCAL
done req} sideband message. When {MBTRAIN.RXCLKCAL done req} is received, the UCIe
Module Partner stops sending forwarded clock and responds by sending {MBTRAIN.RXCLKCAL
done resp} sideband message. When a UCIe Module has sent and received {MBTRAIN.RXCLKCAL
done resp} sideband message, it must exit to MBTRAIN. VALTRAINCENTER. If the operating speed
is > 32 GT/s, the Tx preserves the applied I/Q correction setting throughout the remainder of Link
training and operation until either the Link goes down or the Tx receives an {MBTRAIN.RXCLKCAL
TCKN_L shift req} sideband message.

### 4.5.3.4.6 MBTRAIN.VALTRAINCENTER

To ensure the valid signal is functional, valid to clock training is performed before the data Lane
training. The Receiver samples the pattern on Valid with the forwarded clock. Receiver reference
voltage is set to the optimized value achieved through Vref training (see Section 4.5.3.4.1 and
Section 4.5.3.4.2). All data and Track Transmitters are held low during valid to clock training. When
not performing the actions relevant to this state, if the operating speed is <= 32 GT/s AND Strobe
mode was advertised by the UCIe Module Partner, then the Clock Transmitters are held differential low
(for differential clocking) or simultaneous low (for Quadrature clocking). When not performing the
actions relevant to this state, if the operating speed is > 32 GT/s OR continuous clock mode was
advertised by the UCIe Module Partner, then the Clock Transmitters are providing the free-running
forwarded clock.

Following is the MBTRAIN. VALTRAINCENTER sequence:

1\. The UCIe Module sends a sideband message {MBTRAIN. VALTRAINCENTER start req}. The UCIe
Module Partner responds with {MBTRAIN. VALTRAINCENTER start resp}.

2\. The UCIe Module must perform one or more Transmitter-initiated Data-to-Clock eye width sweeps
(see Section 4.5.1.2) (AND/OR) one or more Transmitter-initiated Data-to-Clock point tests (see
Section 4.5.1.1) to determine the correct Valid to clock centering.

a. The transmit pattern must be set to send 128 iterations of continuous mode "VALTRAIN" (four
1s and four 0s) pattern (see Table 4-5). This pattern must not be scrambled. The Receiver must
be set up to perform comparison on the Valid Lane.

b. Detection on a Receiver Lane is considered successful if "VALTRAIN" pattern detection errors
are less than set threshold (per Lane comparison threshold in Section 9.5.3.29).

c. It should be noted that LFSR RESET has no impact in MBTRAIN. VALVREF.

3\. The UCIe Module can use the received results log to assess valid functionality and margins.
Following this, step 4 must be performed.

4\. The UCIe Module must send {MBTRAIN. VALTRAINCENTER done req} sideband message.
When {MBTRAIN. VALTRAINCENTER done req} is received the UCIe Module Partner responds
with {MBTRAIN. VALTRAINCENTER done resp}. Once the UCIe Module has sent and received
{MBTRAIN. VALTRAINCENTER done resp} sideband message, the UCIe Module must exit to
MBTRAIN. VALTRAINVREF.

### 4.5.3.4.7 MBTRAIN.VALTRAINVREF

The UCIe Module is permitted to optionally optimize the reference voltage (Vref) to sample the
incoming Valid at the operating data rate. All Data and Track Transmitters are held low during Valid-
to-Clock training. When not performing the actions relevant to this state, if the operating speed is
<= 32 GT/s AND Strobe mode was advertised by the UCIe Module Partner, then the Clock
Transmitters are held differential low (for differential clocking) or simultaneous low (for Quadrature
clocking). When not performing the actions relevant to this state, if the operating speed is > 32 GT/s
OR continuous clock mode was advertised by the UCIe Module Partner, then the Clock Transmitters
are providing the free-running forwarded clock.

The sequence for Valid Receiver reference voltage adjustment is as follows:

1\. The UCIe Module must send the sideband message {MBTRAIN. VALTRAINVREF start req}. When
{MBTRAIN.VALTRAINVREF start req} sideband message is received, the UCIe Module Partner
responds with {MBTRAIN. VALTRAINVREF start resp}.

2\. UCIe Module optionally optimizes Vref by adjusting Receiver reference voltage on its Valid
Receiver and performing one or more Receiver-initiated Data-to-Clock eye width sweeps (see
Section 4.5.1.4) (AND/OR) one or more Receiver-initiated Data-to-Clock point tests (see
Section 4.5.1.3). Step 2 is optional and implementation-specific.

a. If Valid centering is performed, the transmit pattern must be set to send 128 iterations of
continuous mode "VALTRAIN" (four 1s and four Os) pattern (see Table 4-5). This pattern must
not be scrambled. The Receiver must be set up to perform comparison on the Valid Lane.

b. Detection on a Receiver Lane is considered successful if "VALTRAIN" pattern detection errors
are less than set threshold (per Lane comparison threshold in Section 9.5.3.29).

c. It should be noted that LFSR RESET has no impact in MBTRAIN. VALVREF.

3\. The UCIe Module must send {MBTRAIN. VALTRAINVREF end req} sideband message after the Vref
optimization is complete. When {MBTRAIN. VALTRAINVREF end req} is received, the UCIe Module
Partner must respond with {MBTRAIN. VALTRAINVREF end resp}. Once the UCIe Module has sent
and received the sideband message {MBTRAIN. VALTRAINVREF end resp}, it must exit to
MBTRAIN.DATATRAINCENTER1.

### 4.5.3.4.8 MBTRAIN.DATATRAINCENTER1

In this state, the UCIe Module performs Data-to-Clock training (including valid). LFSR patterns
described in Section 4.4.1 must be used in this state. The Track Transmitter is held Low. When not
performing the actions relevant to this state:

· Clock Receivers are enabled

· Data and Valid Transmitters are held low

· Data and Valid Receivers are enabled

. If the operating speed is <= 32 GT/s AND Strobe mode was advertised by the UCIe Module
Partner, then the Clock Transmitters are held differential low (for differential clocking) or
simultaneous low (for Quadrature clocking)

. If the operating speed is > 32 GT/s OR continuous clock mode was advertised by the UCIe Module
Partner, then the Clock Transmitters are providing the free-running forwarded clock

. If the operating speed is > 32 GT/s, the UCIe Module sets the TX EQ presets to an
implementation-specific default when entering this state for the first time since RESET exit or a
speed degrade; otherwise, the TX EQ presets are set to the value for the current speed from the
last exit from MBTRAIN.RXDESKEW.

Following is the MBTRAIN.DATATRAINCENTER1 sequence:

1\. The UCIe Module sends the {MBTRAIN.DATATRAINCENTER1 start req} sideband message. When
{MBTRAIN.DATATRAINCENTER1 start req} sideband message is received, the UCIe Module
Partner responds with {MBTRAIN.DATATRAINCENTER1 start resp}.

2\. The UCIe Module must perform one or more Transmitter-initiated Data-to-Clock eye width sweeps
(see Section 4.5.1.2) (AND/OR) one or more Transmitter-initiated Data-to-Clock point tests (see
Section 4.5.1.1) to determine the correct data to clock centering and adjust Transmitter per-bit
deskew (if needed).

a. The Transmitter must be set up to send 4K UI of continuous mode LFSR pattern described in
Section 4.4.1. The LFSR pattern on data must be accompanied by correct valid framing on the
Valid Lane as described in Section 4.1.2. The Receiver must be set up to perform per Lane
comparison.

b. Detection on a Receiver Lane is considered successful if total error count is less than the set
error threshold (see Section 9.5.3.29).

3\. If the test is a success, the UCIe Module must set the clock phase to sample the data eye
at the optimal point to maximize eye margins. The UCIe Module must send
{MBTRAIN.DATATRAINCENTER1 end req} sideband message. When
{MBTRAIN.DATATRAINCENTER1 end req} sideband message is received, the UCIe Module Partner
responds with {MBTRAIN.DATATRAINCENTER1 end resp}. Once the UCIe Module has sent and
received the {MBTRAIN.DATATRAINCENTER1 end resp} sideband message, it must exit to
MBTRAIN.DATATRAINVREF.

### 4.5.3.4.9 MBTRAIN.DATATRAINVREF

UCIe Module is permitted to optionally optimize the reference voltage (Vref) on its data Receivers to
optimize sampling of the incoming Data at the operating data rate. The Track Transmitter is held Low.
When not performing the actions relevant to this state:

. Clock Receivers are enabled

· Data and Valid Transmitters are held low

· Data and Valid Receivers are enabled

. If the operating speed is <= 32 GT/s AND Strobe mode was advertised by the UCIe Module
Partner, then the Clock Transmitters are held differential low (for differential clocking) or
simultaneous low (for Quadrature clocking)

. If the operating speed is > 32 GT/s OR continuous clock mode was advertised by the UCIe Module
Partner, then the Clock Transmitters are providing the free-running forwarded clock

The sequence for data Receiver reference voltage adjustment is as follows:

1\. The UCIe Module must send the sideband message {MBTRAIN.DATATRAINVREF start req}. When
{MBTRAIN.DATATRAINVREF start req} sideband message is received, the UCIe Module Partner
responds with {MBTRAIN.DATATRAINVREF start resp}.

2\. UCIe Module optionally optimizes Vref by adjusting Receiver reference voltage and performing
one or more Receiver-initiated Data-to-Clock eye width sweeps (see Section 4.5.1.4) (AND/OR)
one or more Receiver-initiated Data-to-Clock point tests (see Section 4.5.1.3). Step 2 is optional
and implementation specific. If Data Vref optimization is performed:

a. The Transmitter must be set up to send 4K UI of continuous mode LFSR pattern described in
Section 4.4.1. The LFSR pattern on data must be accompanied by correct valid framing on the
Valid Lane as described in Section 4.1.2. The Receiver must be set up to perform per Lane
comparison.

b. Detection on a Receiver Lane is considered successful if total error count is less than the set
error threshold (see Section 9.5.3.29).

3\. The UCIe Module must send {MBTRAIN.DATATRAINVREF end req} sideband message after the
Vref optimization is complete. When {MBTRAIN.DATATRAINVREF end req} is received, the UCIe
Module Partner responds with {MBTRAIN.DATATRAINVREF end resp}. Once the UCIe Module has
sent and received the sideband message {MBTRAIN.DATATRAINVREF end resp}, it must exit to
MBTRAIN.RXDESKEW.

Note:
It is possible that the eye opening in this step is insufficient (test fails) and a per-bit
deskew may be needed on the Receiver. Thus, the UCIe Module must exit to
MBTRAIN.RXDESKEW.

### 4.5.3.4.10 MBTRAIN.RXDESKEW

The UCIe Module is permitted to optionally perform per Lane deskew on its Receivers to improve
timing margin in this state. The Track Transmitter is held Low. When not performing the actions
relevant to this state:

· Clock Receivers are enabled

· Data and Valid Transmitters are held low

· Data and Valid Receivers are enabled

. If the operating speed is <= 32 GT/s AND Strobe mode was advertised by the UCIe Module
Partner, then the Clock Transmitters are held differential low (for differential clocking) or
simultaneous low (for Quadrature clocking)

. If the operating speed is > 32 GT/s OR continuous clock mode was advertised by the UCIe Module
Partner, then the Clock Transmitters are providing the free-running forwarded clock

Following is the MBTRAIN.RXDESKEW sequence:

1\. The UCIe Module must send the {MBTRAIN.RXDESKEW start req} sideband message. When
{MBTRAIN.RXDESKEW start req} sideband message is received, the UCIe Module Partner
responds with the {MBTRAIN.RXDESKEW start resp} sideband message. If the operating speed is
$< = 3 2 \quad G T / s ,$ then proceed to Step 3.

2\. If the operating speed is > 32 GT/s, the UCIe Module is permitted to request a preset TX EQ
setting for the transmitters at the UCIe Module Partner in this step. To request a preset TX EQ
setting, the UCIe Module sends the {MBTRAIN.RXDESKEW EQ Preset req} sideband message. A
4-bit EQ preset encoding is provided in the Message Info field of this message (see Table 5-7 for
the preset encodings). The UCIe Module Partner applies the EQ preset if the request had a valid
encoding (i.e., one of the encodings from Table 5-7), and responds with the
{MBTRAIN.RXDESKEW EQ Preset resp} sideband message that indicates a status of "Success"
(see Table 7-9 for the sideband message encodings). If the request had a reserved encoding (i.e.,
it is not one of the encodings from Table 5-7), the UCIe Module Partner does not change its EQ
preset and responds with an {MBTRAIN.RXDESKEW EQ Preset resp} sideband message that
indicates a status of "Fail". In case of a "Fail" status, the UCIe Module is permitted to request
another preset by sending another {MBTRAIN.RXDESKEW EQ Preset req} sideband message and
repeating Step 2 before proceeding to Step 3.

3\. The UCIe Module optionally performs per Lane deskew on its Receivers by one or more Receiver-
initiated Data-to-Clock eye width sweeps (see Section 4.5.1.4) (AND/OR) one or more Receiver-
initiated Data-to-Clock point tests (see Section 4.5.1.3). Step 3 is optional and implementation
specific.

a. If per Lane deskew is performed:

o The Transmitter must be set up to send 4K UI of continuous mode LFSR pattern described
in Section 4.4.1. The LFSR pattern on data must be accompanied by correct valid framing
on the Valid Lane as described in Section 4.1.2. The Receiver must be set up to perform
per Lane comparison.

o Detection on a Receiver Lane is considered successful if total error count is less than the
set threshold (see Section 9.5.3.29).

b. If the operating speed $\mathrm { i s } > 3 2 \mathrm { G T / s } ,$ the following additional rules apply:

o The UCIe Module is permitted to repeat Step 2 and Step 3 multiple times, as long as
doing so does not lead to a state residency timeout for MBTRAIN.RXDESKEW.

o The UCIe Module is also permitted to issue an {MBTRAIN.RXDESKEW exit to
DATATRAINCENTER1 req} sideband message to request the next state to be
MBTRAIN.DATATRAINCENTER1 to allow additional transmitter side adjustments for the EQ
preset selected. The UCIe Module is permitted to take the RXDESKEW to
DATATRAINCENTER1 arc a maximum of four times.

o After the UCIe Module Partner receives an {MBTRAIN.RXDESKEW exit to
DATATRAINCENTER1 req} sideband message, if the UCIe Module Partner has not reached
the maximum limit of RXDESKEW to DATATRAINCENTER1 arc iterations, the UCIe Module
Partner responds with an {MBTRAIN.RXDESKEW exit to DATATRAINCENTER1 resp}
sideband message and transitions the state to MBTRAIN.DATATRAINCENTER1. If the
maximum limit of RXDESKEW to DATATRAINCENTER1 arc iterations is exceeded, the UCIe
Module Partner performs the TRAINERROR handshake and Link state transitions to
TRAINERROR state.

o After an {MBTRAIN.RXDESKEW exit to DATATRAINCENTER1 resp} sideband message is
sent or received, any pending {MBTRAIN.RXDESKEW end req} sideband messages are
discarded and that handshake is not completed (i.e,. the originator must not expect a
response for any discarded {MBTRAIN.RXDESKEW end req} sideband messages).

o If a UCIe Module receives an {MBTRAIN.RXDESKEW end req} sideband message but the
UCIe Module intends to send an {MBTRAIN.RXDESKEW exit to DATATRAINCENTER1 req}
sideband message, the UCIe Module must not send an {MBTRAIN.RXDESKEW end resp}
sideband message (i.e., the UCIe Module will not proceed to Step 4).

o If no other EQ preset adjustments are needed as determined by the Receiver, the UCIe
Module proceeds to Step 4.

4\. The UCIe Module must send {MBTRAIN.RXDESKEW end req} sideband message after the deskew
is performed or skipped. When {MBTRAIN.RXDESKEW end req} is received, the UCIe Module
Partner must respond with {MBTRAIN.RXDESKEW end resp}. Once UCIe Module has sent and
received the sideband message {MBTRAIN.RXDESKEW end resp}, it must exit to
MBTRAIN.DATATRAINCENTER2.

### 4.5.3.4.11 MBTRAIN.DATATRAINCENTER2

This state is needed for the UCIe Module to recenter clock to aggregate data in case the UCIe Module
Partner's Receiver performed a per Lane deskew. The Track Transmitter is held Low. When not
performing the actions relevant to this state:

· Clock Receivers are enabled

· Data and Valid Transmitters are held low

· Data and Valid Receivers are enabled

. If the operating speed is <= 32 GT/s AND Strobe mode was advertised by the UCIe Module
Partner, then the Clock Transmitters are held differential low (for differential clocking) or
simultaneous low (for Quadrature clocking)

. If the operating speed is > 32 GT/s OR continuous clock mode was advertised by the UCIe Module
Partner, then the Clock Transmitters are providing the free-running forwarded clock

Following is the MBTRAIN.DATATRAINCENTER2 sequence:

1\. The UCIe Module sends the sideband message {MBTRAIN.DATATRAINCENTER2 start req}. When
{MBTRAIN.DATATRAINCENTER2 start req} sideband message is received, the UCIe Module
Partner responds with {MBTRAIN.DATATRAINCENTER2 start resp}.

2\. The UCIe Module must perform one or more Transmitter-initiated Data-to-Clock eye width sweeps
(see Section 4.5.1.2) (AND/OR) one or more Transmitter-initiated Data-to-Clock point tests (see
Section 4.5.1.1) to determine the correct data-to-eye centering.

a. The Transmitter must be set up to send 4K UI of continuous mode LFSR pattern described in
Section 4.4.1. The LFSR pattern on data must be accompanied by correct valid framing on the
Valid Lane as described in Section 4.1.2. The Receiver must be set up to perform per Lane
comparison.

b. Detection on a Receiver Lane is considered successful if total error count is less than the set
error threshold (see Section 9.5.3.29).

3\. The UCIe Module uses the received training results to calculate the final eye center and set the
clock phase to sample the data eye at the optimal point to maximize eye margins. The UCIe
Module must send the {MBTRAIN.DATATRAINCENTER2 end req} sideband message. When
{MBTRAIN.DATATRAINCENTER2 end req} sideband message is received, the UCIe Module Partner
responds with {MBTRAIN. DATATRAINCENTER2 end resp}. Once UCIe Module has sent and
received {MBTRAIN.DATATRAINCENTER2 end resp} sideband message, it must exit to
MBTRAIN.LINKSPEED.

### 4.5.3.4.12 MBTRAIN.LINKSPEED

In this state, the UCIe Module checks Link stability at the operating date rate. The Track Transmitter is
held Low. When not performing the actions relevant to this state:

· Clock Receivers are enabled

· Data and Valid Transmitters are held low

· Data and Valid Receivers are enabled

. If the operating speed is <= 32 GT/s AND Strobe mode was advertised by the UCIe Module
Partner, then the Clock Transmitters are held differential low (for differential clocking) or
simultaneous low (for Quadrature clocking)

. If the operating speed is > 32 GT/s OR continuous clock mode was advertised by the UCIe Module
Partner, then the Clock Transmitters are providing the free-running forwarded clock

The following steps must be executed sequentially, when applicable:

1\. The UCIe Module sends the sideband message {MBTRAIN.LINKSPEED start req}. When
{MBTRAIN.LINKSPEED start req} sideband message is received, the UCIe Module Partner
responds with {MBTRAIN.LINKSPEED start resp}.

2\. The UCIe Module must perform a Transmitter-initiated Data-to-Clock point test (see
Section 4.5.1.1) with the final clock sampling phase calculated in the previous
MBTRAIN.DATACENTER2 state. LFSR pattern described in Section 4.4.1 must be used in this
state.

a. The Transmitter must be set up to send 4K UI of continuous mode LFSR pattern described in
Section 4.4.1. The LFSR pattern on data must be accompanied by correct valid framing on the
Valid Lane as described in Section 4.1.2. The Receiver must be set up to perform per Lane
comparison.

b. Detection on a Receiver Lane is considered successful if total error count is less than the set
threshold (see Section 9.5.3.29).

3\. For single-Module instantiations, if errors are encountered, the UCIe Module sets its Transmitters
to an electrical idle state and sends {MBTRAIN.LINKSPEED error req} sideband message. If an
{MBTRAIN.LINKSPEED error req} sideband message is received, the UCIe Module Partner must
complete Step 1 and Step 2, evaluate the results and if not initiating an {MBTRAIN.LINKSPEED
exit to phy retrain req} sideband message, the UCIe Module Partner enters electrical idle on its
Receiver and sends the {MBTRAIN.LINKSPEED error resp} sideband message. If an
{MBTRAIN.LINKSPEED exit to phy retrain req} sideband message is received, the UCIe Module
must exit to PHYRETRAIN and send an {MBTRAIN.LINKSPEED exit to PHY retrain resp} sideband
message; any outstanding messages are abandoned. Otherwise, after the {MBTRAIN.LINKSPEED
error resp} sideband message is received, the PHY_IN_RETRAIN flag is cleared and the following
rules apply:

a. Based on the number of Lanes encountering errors, the UCIe Module checks if the failing
Lanes can be repaired (for Advanced package) or Width degraded (for standard package).
If Lanes can be can be repaired (for Advanced package) or Width degraded (for standard
package), the UCIe Module must send {MBTRAIN.LINKSPEED exit to repair req} to the UCIe
Module Partner. The UCIe Module Partner, if not initiating a speed degrade, enters
MBTRAIN.REPAIR and sends the sideband message {MBTRAIN.LINKSPEED exit to repair resp}.
If {MBTRAIN.LINKSPEED exit to repair resp} is received in response to a
{MBTRAIN.LINKSPEED exit to repair req}, the UCIe Module must exit to MBTRAIN.REPAIR. If
a UCIe Module is initiating a speed degrade, it must not respond to {MBTRAIN.LINKSPEED exit
to repair req}.

b. If the Lanes cannot be repaired (for Advanced package) or width degraded (for Standard
package), the speed must be degraded. The UCIe Module sends {MBTRAIN.LINKSPEED exit to
speed degrade req} sideband message and waits for a response from the remote Link partner.
The UCIe Module Partner must respond with {MBTRAIN.LINKSPEED exit to speed degrade
resp}. Following this handshake, the UCIe Module must exit to MBTRAIN.SPEEDIDLE to set
data rate to next lower speed.

c. If the UCIe Module receives an {MBTRAIN.LINKSPEED exit to speed degrade req} any
outstanding {MBTRAIN.LINKSPEED exit to repair req} must be abandoned and the UCIe
Module must respond to {MBTRAIN.LINKSPEED exit to speed degrade req}.

d. Any outstanding {MBTRAIN.LINKSPEED done req} must be abandoned if a UCIe Module has
received a {MBTRAIN.LINKSPEED error req}.

4\. For single- or multi-module instantiations, if no errors are encountered, the UCIe Module must set
the clock phase on its Transmitter to sample the data eye at the optimal point to maximize eye
margins. If PHY_IN_RETRAIN is not set for single-module instantiations, proceed to Step 6. If
PHY_IN_RETRAIN is not set, for multi-module instantiations, the UCIe Module must send the
{MBTRAIN.LINKSPEED done req} (if not waiting for Link match criteria as a Retimer) to the
remote UCIe Module Partner and wait for multi-module PHY Logic (MMPL) resolution in Step 5c. If
the PHY_IN_RETRAIN variable is set, the following actions must be taken:

a. If a change is detected in Runtime Link Test Control register relative to the values at previous
PHYRETRAIN entry, the UCIe Module must send an {MBTRAIN.LINKSPEED exit to phy retrain
req} sideband message and wait for a response. Upon receiving this message, the UCIe Module
Partner must exit to PHY retrain and send an {MBTRAIN.LINKSPEED exit to PHY retrain resp}
sideband message. Once this sideband message is received, the UCIe Module must exit to PHY
retrain.

b. Else if no change is detected in the Runtime Link Test Control register relative to the values at
previous PHYRETRAIN entry, Busy bit in Runtime Link Test Status and PHY_IN_RETRAIN
variable must be cleared and the UCIe Module must proceed to Step 6.

5\. For multi-module instantiations, if errors are encountered, the UCIe Module sets its Transmitters
to an electrical idle state and sends {MBTRAIN.LINKSPEED error req} sideband message. If an
{MBTRAIN.LINKSPEED error req} sideband message is received, the UCIe Module Partner must
complete Step 1 and Step 2, evaluate the results and if not initiating an {MBTRAIN.LINKSPEED
exit to phy retrain req} sideband message, the UCIe Module Partner enters electrical idle on its
Receiver, and sends the {MBTRAIN.LINKSPEED error resp} sideband message. If an
{MBTRAIN.LINKSPEED exit to phy retrain req} sideband message is received on any of the
modules in the multi-module Link, the UCIe Module must exit to PHYRETRAIN and send an
{MBTRAIN.LINKSPEED exit to PHY retrain resp} sideband message; any outstanding messages
are abandoned. Otherwise, after the {MBTRAIN.LINKSPEED error resp} sideband message is
received, the PHY_IN_RETRAIN flag is cleared and the following rules apply:

a. Based on the number of Lanes encountering errors, the UCIe Module checks whether the failing
Lanes can be repaired (for Advanced Package) or Width degraded (for Standard Package). If
Lanes can be can be repaired (for Advanced Package) or Width degraded (for Standard
Package), the UCIe Module must send {MBTRAIN.LINKSPEED exit to repair req} to the UCIe
Module Partner.

b. If the Lanes cannot be repaired (for Advanced Package) or width degraded (for Standard
Package), the speed must be degraded. The UCIe Module sends {MBTRAIN.LINKSPEED exit to
speed degrade req}.

c. The UCIe Module informs MMPL of local and remote error requests, done requests, or speed
degrade requests, and waits for resolution. It also informs MMPL of any prior width degrade
(for example in MBINIT.REPAIRMB), and MMPL treats this as the corresponding module
requesting width degrade from the full operational width.

d. Based on the resolution flow chart in Section 4.7, MMPL directs each Module to send either the
{MBTRAIN.LINKSPEED exit to repair resp} (indicating next state is REPAIR),
{MBTRAIN.LINKSPEED exit to speed degrade resp} (indicating next state is SPEEDIDLE with
target speed to next-lower speed), {MBTRAIN.LINKSPEED multi-module disable module resp}
(indicating next state is TRAINERROR and eventually RESET), or {MBTRAIN.LINKSPEED done
resp} (indicating next state is LINKINIT). This is done regardless of the module's original error
request or done request, and indicates the result of the resolution and next state to each
module. The UCIe Module transitions to next state once it has sent and received the sideband
response message that matches the expected resolution. Any mismatch on received message
vs. expected resolution must take all modules to TRAINERROR. For Retimer dies, the resolution

must take into account any Link match requirements, and while resolving the target
configuration with remote Retimer partner, each UCIe Module from the Retimer die must send
{MBTRAIN.LINKSPEED done resp} with stall encoding every 4 ms. The UCIe Retimer must
ensure that this stall is not perpetual, and an implementation-specific timeout must be included
in the Retimer. If {MBTRAIN.LINKSPEED done resp} with stall encoding is received, it must
reset timers for state transition as well as any outstanding handshakes for multi-module
resolution.

6\. If the UCIe die is not a Retimer, proceed to Step 7. If the UCIe die is a Retimer, the following rules
apply to achieve Link match (if required):

a. Retimer must not send {MBTRAIN.LINKSPEED done req} unless the target Link speed and
width of the remote Retimer partner resolves to current Link and width. Proceed to Step 7 if
Link match is achieved or if it is not required.

b. While resolving the target Link speed and width with the remote Retimer partner, if a Retimer
has received an {MBTRAIN.LINKSPEED done req}, it must send {MBTRAIN.LINKSPEED done
resp} with stall encoding every 4 ms. UCIe Retimer must ensure that this stall is not perpetual,
and an implementation specific timeout must be included in the Retimer.

C. If the local UCIe Link speed or width is greater than the remote Retimer UCIe Link, then it must
treat this as an error condition, and perform Step 3 or Step 5 with repair or speed degrade
(whichever is applicable).

7\. The UCIe Module must send {MBTRAIN.LINKSPEED done req} sideband message. When
{MBTRAIN.LINKSPEED done req} is received, the UCIe Module must respond with
{MBTRAIN.LINKSPEED done resp} and when a UCIe Module has sent and received the
{MBTRAIN.LINKSPEED done resp} sideband message, both Transmitters and Receivers are now
enabled and idle and both devices exit to LINKINIT.

### 4.5.3.4.13 MBTRAIN.REPAIR

This state can be entered from PHYRETRAIN or from MBINIT.LINKSPEED. For Advanced package, this
state will be used to apply repair and for Standard package, this state will be used for Link width
degrade. Track, Data, and Valid Transmitters are held low. Clock Transmitters are held differential low
(for differential clocking) or simultaneous low (for Quadrature clocking).

For Advanced Package, if the number of repair resources currently available is greater than or equal
to the number of Lanes encountering errors, repair must be applied:

1\. The UCIe Module sends the sideband message {MBTRAIN.REPAIR init req} for its Transmitter and
the UCIe Module Partner responds with {MBTRAIN.REPAIR init resp}.

2\. If Lane repair is possible, the UCIe Module applies repair on its Transmitter Lanes as described in
Section 4.3.1 and sends {MBTRAIN.REPAIR Apply repair req} sideband message. The UCIe
Module Partner applies repair as described in Section 4.3.1 and responds with {MBTRAIN.REPAIR
Apply repair resp} sideband message once the required repair is applied.

3\. The UCIe Module must send {MBTRAIN.REPAIR end req} sideband message and waits for a
response. The UCIe Module Partner must then respond with {MBTRAIN.REPAIR end resp}. When
a UCIe Module has sent and received {MBTRAIN.REPAIR end resp}, it must exit to
MBTRAIN.TXSELFCAL.

For a x16 Standard package, if the Lanes encountering errors are all contained within the set of
Lane 0 through Lane 7 or Lane 8 through Lane 15, the width must be degraded to a x8 Link using the
set of Lanes without errors (Lane 0 ... Lane 7 OR Lane 8 ... Lane 15). Likewise, for a x8 Standard
package, if the Lanes encountering errors are all contained within the set of Lane 0 through Lane 3
or Lane 4 through Lane 7, the width must be degraded to a x4 Link using the set of Lanes without
errors (Lane 0 through Lane 3 or Lane 4 through Lane 7).

1\. The UCIe Module sends the sideband message {MBTRAIN.REPAIR init req} and the Receiver
responds with {MBTRAIN.REPAIR init resp}.

2\. The UCIe Module must send the {MBTRAIN.REPAIR apply degrade req} sideband message,
indicating the functional Lanes on its Transmitter using one of the logical Lane map encodings
from Table 4-9. Encodings 100b and 101b can be used only when the SPMW bit is set to 1 or the
UCIe-S x8 bit was set to 1 in the transmitted or received {MBINIT.PARAM configuration req}
sideband message. If the remote Link partner indicated a width degrade in the functional Lanes,
the UCIe Module must apply the corresponding width degrade to its Receiver. If the remote Link
partner indicated all Lanes are functional, the UCIe Module sets its Transmitter and Receiver to
the logical lane map corresponding to the functional Lane encoding determined on its Transmitter.
The UCIe Module sends the {MBTRAIN.REPAIR apply degrade resp} sideband message after
setting its Transmitter and Receiver lanes to the relevant logical lane map and proceeds to Step 3
if a degrade is possible or if all Lanes are functional. If a "Degrade not possible" encoding is sent
or received in the {MBTRAIN.REPAIR apply degrade req} sideband message, the UCIe Module
must exit to TRAINERROR after performing the TRAINERROR handshake.

3\. The UCIe Module must send the {MBTRAIN.REPAIR end req} sideband message and wait for a
response. The UCIe Module Partner must then respond with the {MBTRAIN.REPAIR end resp}
sideband message. When UCIe Module has sent and received the {MBTRAIN.REPAIR end resp}
sideband message, the UCIe Module must exit to MBTRAIN.TXSELFCAL.

### 4.5.3.5 LINKINIT

This state is used to allow die to die adapter to complete initial Link management before entering
Active state on RDI. See Section 10.1.6 for more details on RDI bring up flow. Track, Data, and Valid
Transmitters are held low. If the operating speed is <= 32 GT/s AND Strobe mode was advertised by
the UCIe Module Partner, then the Clock Transmitters are held differential low (for differential
clocking) or simultaneous low (for Quadrature clocking). If the operating speed is > 32 GT/s OR
continuous clock mode was advertised by the UCIe Module Partner, then the Clock Transmitters are
providing the free-running forwarded clock. Clock Receivers are enabled.

Once RDI is in Active state, the PHY will clear its copy of "Start UCIe Link training" bit from UCIe Link
control register.

The scrambler LFSR must be RESET upon entering this state.

This state is common for Advanced Package and Standard Package configurations.

### 4.5.3.6 ACTIVE

Physical layer initialization is complete, RDI is in Active state and packets from upper layers can be
exchanged between the two dies.

All data in this state is scrambled using the scrambler LFSR described in Section 4.4.1. Clock gating
rules as described in Section 5.11 apply.

This state is common for Advanced Package and Standard Package configurations.

### 4.5.3.7 PHYRETRAIN

A die can enter PHY retrain for a number of reasons. Track, Data, and Valid Transmitters are held low.
Clock Transmitters are held differential low (for differential clocking) or simultaneous low (for
Quadrature clocking). The trigger for PHY to enter PHY retrain is one of the following scenarios:

· Adapter directed PHY retrain: Adapter can direct the PHY to retrain for any reason it deems
necessary (see Section 10.3.3.4 Retrain State rules for more details and examples of Adapter-
initiated Retrain requests).

· PHY initiated PHY retrain: Local PHY must initiate retrain on detecting a Valid framing error.

. Remote die requested PHY retrain: Local PHY must enter PHY retrain on receiving a request from
the remote die.

. If a change is detected in Runtime Link Test Control register during MBTRAIN.LINKSPEED.

A variable PHY_IN_RETRAIN must be set when entering PHYRETRAIN. For a multi-module
configuration, the Retrain encoding (and hence the Retrain exit resolution) must be the same for all
the modules which are part of the same multi-module Link. This is required because in a multi-
module Link all modules must operate at the same speed and width (however, for Advanced package,
it is possible for a module not needing repair to go through the Repair state and send the "No Repair"
encoding in the corresponding {\*apply repair\*} messages).

<table>
<caption>Table 4-10. Runtime Link Test Status Register based Retrain encoding</caption>
<tr>
<th colspan="2">Link Test Status Register</th>
<th rowspan="2">Retrain Encoding Resolution</th>
</tr>
<tr>
<th>Busy bit value</th>
<th>Repair Required</th>
</tr>
<tr>
<td>0b</td>
<td>$N / A$</td>
<td>TXSELFCAL</td>
</tr>
<tr>
<td rowspan="2">1b</td>
<td rowspan="2">Repair needed</td>
<td>REPAIR (If repair resources are available)</td>
</tr>
<tr>
<td>SPEEDIDLE (if unrepairable)</td>
</tr>
<tr>
<td>1b</td>
<td>No Repair</td>
<td>TXSELFCAL</td>
</tr>
</table>

<table>
<caption>Table 4-11. Retrain encoding</caption>
<tr>
<th>Retrain Encoding</th>
<th>State</th>
<th>Retain Condition</th>
</tr>
<tr>
<td>001b</td>
<td>TXSELFCAL</td>
<td>No Lane errors (Valid framing errors detected by PHY)</td>
</tr>
<tr>
<td>010b</td>
<td>SPEEDIDLE</td>
<td>Lane errors &amp; faulty Lanes cannot be repaired</td>
</tr>
<tr>
<td>100b</td>
<td>REPAIR</td>
<td>Lane errors &amp; faulty Lanes are repairable</td>
</tr>
</table>

<table>
<caption>Table 4-12. Retrain exit state resolution</caption>
<tr>
<th colspan="2">Retrain reg Condition</th>
<th colspan="2">Retrain Request Encoding</th>
<th colspan="2">Resolved State Encoding</th>
<th>Exit</th>
</tr>
<tr>
<th>Die 0</th>
<th>Die 1</th>
<th>Die 0</th>
<th>Die 1</th>
<th>Die 0</th>
<th>Die 1</th>
<th>Both Dies</th>
</tr>
<tr>
<td>No Lane Errors</td>
<td>No Lane Errors</td>
<td>001b</td>
<td>001b</td>
<td>001b</td>
<td>001b</td>
<td>MBTRAIN. TXSELFCAL</td>
</tr>
<tr>
<td>No Lane Errors</td>
<td>Repair</td>
<td>001b</td>
<td>100b</td>
<td>100b</td>
<td>100b</td>
<td>MBTRAIN.REPAIR</td>
</tr>
<tr>
<td>No Lane Errors</td>
<td>Speed Degrade</td>
<td>001b</td>
<td>010b</td>
<td>010b</td>
<td>010b</td>
<td>MBTRAIN.SPEEDIDLE</td>
</tr>
<tr>
<td>Repair</td>
<td>No Lane Errors</td>
<td>100b</td>
<td>001b</td>
<td>100b</td>
<td>100b</td>
<td>MBTRAIN.REPAIR</td>
</tr>
<tr>
<td>Repair</td>
<td>Repair</td>
<td>100b</td>
<td>100b</td>
<td>100b</td>
<td>100b</td>
<td>MBTRAIN.REPAIR</td>
</tr>
<tr>
<td>Repair</td>
<td>Speed Degrade</td>
<td>100b</td>
<td>010b</td>
<td>010b</td>
<td>010b</td>
<td>MBTRAIN.SPEEDIDLE</td>
</tr>
<tr>
<td>Speed Degrade</td>
<td>No Lane Errors</td>
<td>010b</td>
<td>001b</td>
<td>010b</td>
<td>010b</td>
<td>MBTRAIN.SPEEDIDLE</td>
</tr>
<tr>
<td>Speed Degrade</td>
<td>Repair</td>
<td>010b</td>
<td>100b</td>
<td>010b</td>
<td>010b</td>
<td>MBTRAIN.SPEEDIDLE</td>
</tr>
<tr>
<td>Speed Degrade</td>
<td>Speed Degrade</td>
<td>010b</td>
<td>010b</td>
<td>010b</td>
<td>010b</td>
<td>MBTRAIN.SPEEDIDLE</td>
</tr>
</table>

#### 4.5.3.7.1 Adapter initiated PHY retrain

Following is the sequence of steps for an Adapter initiated PHY retrain:

1\. UCIe Module receives retrain request from the local Adapter (RDI state req moved to Retrain).
Following this, the UCIe Module must complete the stall Req/Ack (pl_stallreq; lp_stallack)
hand shake on RDI as described in Chapter 10.0.

2\. After completion of stall Req/Ack handshake and transmitting any pending data over mainband,
UCIe Module must send sideband message {LinkMgmt.RDI.Req.Retrain} to UCIe Module Partner.

3\. The UCIe Module Partner on receiving the sideband message {LinkMgmt.RDI.Req.Retrain} must
transition its RDI state to Retrain after completion of stall Req/Ack (pl_stallreq;
lp_stallack) handshake on its RDI and there is no mainband data pending in the Receiver
pipeline. After completion of stall Req/Ack handshake and transmitting any pending data over
mainband, the UCIe Module Partner responds with {LinkMgmt.RDI.Rsp.Retrain}.

4\. Once {LinkMgmt.RDI.Rsp.Retrain} is received and there is no mainband data pending in the
receiver pipeline, the UCIe Module must transition its RDI to Retrain.

5\. UCIe Module must send {PHYRETRAIN.retrain start req} with retrain encoding reflecting the
contents of Runtime Link Test Control register except the Start bit (if the Busy bit in Runtime Link
Test Status Register is set). Following this, the UCIe Module Partner compares the received retrain
encoding with the local retrain encoding. If received retrain encoding is the same as the local
retrain encoding, the UCIe Module Partner must respond with {PHYRETRAIN.retrain start resp}. If
the retrain encodings do not match, the UCIe Module Partner must resolve according to Retrain
encodings and resolutions shown in Table 4-10, Table 4-11, and Table 4-12 and then send
{PHYRETRAIN.retrain start resp} with the resolved retrain encoding.

6\. Once UCIe Module sends and receives the sideband message {PHYRETRAIN.retrain start resp}, it
must exit to corresponding training state according to the resolved retrain register encoding.

### 4.5.3.7.2 PHY initiated PHY retrain

Following is the sequence of steps for PHY initiated PHY retrain:

1\. On detecting a valid framing error, the UCIe Module must assert pl_error when transmitting
that flit (or flit chunk) on RDI. Following this the UCIe Module (PHY) must complete the stall Req/
Ack (pl_stallreq; lp_stallack) handshake on RDI.

2\. The UCIe Module must send sideband message {LinkMgmt.RDI.Req.Retrain}.

3\. The UCIe Module Partner on receiving the sideband message {LinkMgmt.RDI.Req.Retrain} must
transition its RDI to retrain after completion of stall Req/Ack (pl_stallreq; lp_stallack)
handshake on its RDI. Following that the UCIe Module Partner responds with
{LinkMgmt.RDI.Rsp.Retrain}.

4\. Once {LinkMgmt.RDI.Rsp.Retrain} is received, the UCIe Module must transition its RDI to Retrain.

5\. UCIe Module must send {PHYRETRAIN.retrain start req} with retrain encoding reflecting the
contents of Runtime Link Test Control register except the Start bit (if the Busy bit in Runtime Link
Test Status Register is set). Following this, the UCIe Module Partner compares the received retrain
encoding with the local retrain encoding. If received retrain encoding is the same as the local
retrain encoding, the UCIe Module Partner must respond with {PHYRETRAIN.retrain start resp}. If
the retrain encodings do not match, the UCIe Module Partner must resolve according to Retrain
encodings and resolutions shown in Table 4-10, Table 4-11, and Table 4-12 and then send
{PHYRETRAIN.retrain start resp} with the resolved retrain encoding.

6\. Once a UCIe Module has sent and received the sideband message {PHYRETRAIN.retrain start
resp}, it must exit to corresponding training state according to the resolved retrain encoding.

### 4.5.3.7.3 Remote Die requested PHY retrain

1\. On receiving {LinkMgmt.RDI.Req.Retrain}, the UCIe Module must transition local RDI to retrain
after completion of stall Req/Ack (pl_stallreq; lp_stallack) handshake on its RDI.
Following that the UCIe Module responds with {LinkMgmt.RDI.Rsp. Retrain}.

2\. Once {LinkMgmt.RDI.Rsp.Retrain} is received, the UCIe Module Partner must transition its RDI to
retrain.

3\. UCIe Module must send {PHYRETRAIN.retrain start req} with retrain encoding reflecting the
contents of Runtime Link Test Control register except the Start bit (if the Busy bit in Runtime Link
Test Status Register is set). Following this, the UCIe Module Partner compares the received retrain
encoding with the local retrain encoding. If received retrain encoding is the same as the local
retrain encoding, the UCIe Module Partner responds with {PHYRETRAIN.retrain start resp}. If the
retrain encodings do not match, the UCIe Module Partner must resolve according to Retrain
encodings and resolutions shown in Table 4-10, Table 4-11, and Table 4-12 and then send
{PHYRETRAIN.retrain start resp} with the resolved retrain encoding.

4\. Once a die has sent and received the sideband message {PHYRETRAIN.retrain start resp}, it must
exit to corresponding training state according to the resolved retrain encoding.

### 4.5.3.7.4 PHY retrain from LINKSPEED

1\. The UCIe Module must send {PHYRETRAIN.retrain start req} with retrain encoding reflecting the
contents of Runtime Link Test Control register except the Start bit (if the Busy bit in Runtime Link
Test Status Register is set). Following this, the UCIe Module Partner compares the received retrain
encoding with the local retrain encoding. If received retrain encoding is the same as the local
retrain encoding, the UCIe Module Partner must respond with {PHYRETRAIN.retrain start resp}. If
the retrain encodings do not match, the UCIe Module Partner must resolve according to Retrain
encodings and resolutions shown in Table 4-10, Table 4-11, and Table 4-12 and then send
{PHYRETRAIN.retrain start resp} with the resolved retrain encoding.

2\. Once a die has sent and received the sideband message {PHYRETRAIN.retrain start resp}, it must
exit to corresponding training state according to the resolved retrain encoding.

### 4.5.3.8 TRAINERROR

This state used as a transitional state due to any fatal or non-fatal events that need to bring the state
machine back to RESET state. This can happen during initialization and training or if "Start UCIe Link
training" bit from UCIe Link control register is set when state machine is not in RESET. It is also used
for any events that transition the Link from a Link Up to a Link Down condition. Data, Valid, Clock,
and Track transmitters are tri-stated, and their receivers are permitted to be disabled.

The exit from TRAINERROR to RESET is implementation specific. For cases when there is no error
escalation (i.e., RDI is not in LinkError), it is recommended to exit TRAINERROR as soon as possible.
For cases when there is error escalation (i.e., RDI is in LinkError), it is required for Physical Layer to
be in TRAINERROR as long as RDI is in LinkError. To avoid problems with entering RESET while
transmitting sideband packets, any in-progress sideband packets must finish transmission before
entering RESET state.

See Chapter 10.0 for correctable, non-fatal, and fatal error escalation on RDI.

This state is common for Advanced Package and Standard Package configurations.

If sideband is Active, a sideband handshake must be performed to enter TRAINERROR state from any
state other than SBINIT. The following is defined as the TRAINERROR handshake:

. The UCIe Module requesting exit to TRAINERROR must send {TRAINERROR Entry req} sideband
message and wait for a response. The UCIe Module Partner must exit to TRAINERROR and

respond with {TRAINERROR Entry resp}. Once {TRAINERROR Entry resp} sideband message is
received, the UCIe Module must exit to TRAINERROR. If no response is received for 8 ms, the
LTSM transitions to TRAINERROR.

### 4.5.3.9 L1/L2

PM state allows a lower power state than dynamic clock gating in ACTIVE. Data, Valid, Clock, and
Track transmitters are tri-stated, and their receivers are permitted to be disabled.

. This state is entered when RDI has transitioned to PM state as described in Chapter 10.0. The PHY
power saving features in this state are implementation specific.

. When local Adapter requests Active on RDI or remote Link partner requests L1 exit the PHY must
exit to MBTRAIN.SPEEDIDLE. L1 exit is coordinated with the corresponding L1 state exit
transitions on RDI.

· When local Adapter requests Active on RDI or remote Link partner requests L2 exit the PHY must
exit to RESET. L2 exit is coordinated with the corresponding L2 state exit transitions on RDI.

### 4.5.3.9.1 Powering down Sideband in L2 State

Implementations are permitted to optionally support the L2 Sideband Power Down (L2SPD) feature.
This capability is negotiated by way of Sideband Feature Extensions. If L2SPD is negotiated,
implementations are permitted to aggressively power down most of the sideband logic, with the
exceptions noted in the rules of this section. The sideband clock and data pins are used to provide a
mechanism to wake up the sideband infrastructure and re-perform SBINIT before sideband packets
can be transmitted. The rules are provided so that the L2 exit can be triggered from either side of the
Link.

In a multi-module Link, all the modules must advertise the same capability in the context of L2SPD
(see Table 7-11 for the bit assignment of L2SPD capability during negotiation in the {MBINIT.PARAM
SBFE req/resp} sideband messages). The L2SPD bit is set to 1 in the {MBINIT.PARAM SBFE req}
sideband message if the L2SPD capability is supported by hardware and enabled through the L2SPD
bit in UCIe Link Control register; otherwise, the bit is cleared to 0. The L2SPD bit is set to 1 in the
{MBINIT.PARAM SBFE resp} sideband message if the L2SPD capability was advertised in the
transmitted as well as the received {MBINIT.PARAM SBFE req} sideband messages; otherwise, the bit
is cleared to 0. The following rules apply for L2, and L2 exit after L2SPD has been negotiated; for
multi-module Links, the following rules and steps must be independently followed for each module:

. After L2 entry is complete, implementations are permitted to aggressively power down most of
their sideband infrastructure, with the following exceptions:

\- Sideband transmitters must drive 0 on the clock and data pins.

\- Sideband receivers must have a minimal sampling circuit powered on to detect the sideband
clock = 1 and sideband data = 0.

\- If the SB_MGMT_UP flag is supported, it is cleared to 0.

. The L2 exit flow in this mode consists of three Phases. The L2 exit trigger is provided to the
remote Link partner by driving 1 on the sideband clock transmitter and 0 on the sideband data
transmitter.

\- Phase 1: L2 exit trigger is sent and received.

o If an L2 exit trigger is detected on the sideband clock and data receivers for at least 100
ns OR if the UCIe Module is initiating L2 exit, the UCIe Module must bring up its local die's
sideband infrastructure.

o When ready to perform SBINIT, initiate the L2 exit trigger on its sideband transmitter.

o After the L2 exit trigger has been transmitted and received for at least 100 ns, the UCIe
Module proceeds to Phase 2 of L2 exit.

\- Phase 2: Bringing the sideband and mainband to the initial state to prepare for Link training.

o The UCIe Module transitions the LTSM to Reset state and drives 0 on both the sideband
clock and data transmitters.

o After meeting the residency and exit requirements of Reset state (see Section 4.5.3.1),
the UCIe Module proceeds to Phase 3.

· Phase 3: Link Initialization and Training

o The UCIe Module begins regular Link Initialization and Training - Reset exit is initiated to
proceed with SBINIT and the remainder of the Link bring-up flow.

Figure 4-42 illustrates an example ladder diagram for the L2 exit flow.

<figure>
<figcaption>Figure 4-42. Example L2 Exit Flow with L2SPD Capability</figcaption>

Chiplet A

Chiplet B

L2 Entry complete (Sideband power down*)

Chiplet A:

\* Sideband power down still requires:

. Receives the L2 exit trigger

· Brings up its infrastructure/sideband
voltage and dock when it is ready for SBINIT

· On Tx, drive 0 on sb clk and sb data
. On Rx, have minimal sampling circuit
to detect sb clk = 1 and sb data = 0

sb clk = 1, sb data = 0

Chiplet B:

· Detects sb clk = 1 and sb data = 0,
and treats this event as an L2 exit trigger

· Brings up its infrastructure/sideband voltage
and clock when it is ready for SBINIT

sb clk = 1, sb data = 0

Both sides detect sb clk = 1, sb data = 0
for at least 100 ns on $T \mathrm { x }$ and Rx,
LTSM transitions from L2 to Reset

sb clk = 0, sb data = 0

After Reset residency is complete, proceed with
Reset state exit and SBINIT, Link Training and
RDI Active handshake to complete L2 Exit flow

</figure>

## 4.6 Runtime Recalibration

Track signal can be used by the Receiver to perform periodic runtime calibration while in ACTIVE (see
Section 5.5.1 for Track usage and examples). Mainband data must continued to be sampled and
processed (when accompanied by correct valid framing) during Runtime Recalibration. For
unterminated Link, when not sending the required pattern the Track signal must alternate between
being held low and held high (for anti aging) across consecutive Track recalibration iterations. For a
terminated Link, when not sending the required pattern, the Track transmitter must go to Hi-Z. Tx
Adjustment during Runtime Recalibration (TARR) is an optional feature that can be used to permit $T \mathrm { x }$
adjustments for drift compensation. Because the Tx performs the majority of the adjustments during
Link training, this option permits more power-efficient Rx designs because the Rx does not have to
provision for a wide range of margin for drift compensation.

The following sequence is used to request track pattern:

1\. The UCIe Module enables the Track signal buffers on its Receiver and sends a {RECAL.track
pattern init req} sideband message, and then waits for a response.

2\. The UCIe Module Partner sends {RECAL.track pattern init resp} and enables its Track signal
Transmitter (is preconditioned to drive low if needed). Following this, the UCIe Module Partner's
Track Transmitter starts sending the pattern described in Section 5.5.1, along with the forwarded
clock. If the link is in Clock-gated mode, the UCIe Module Partner should enable the clock and
manage whether the Link should return to Clock-gated mode after the Track update is complete.

3\. If TARR was not negotiated or the Rx has determined that it can successfully perform
recalibration, the UCIe Module on its Receiver performs the required recalibration and sends the
{RECAL.track pattern done req} sideband message and proceeds to Step 6. Otherwise, proceed
to Step 4.

4\. The UCIe Module sends a {RECAL.track tx adjust req} sideband message to notify the UCIe
Module Partner Tx of the delay compensation value and direction, in units of 1/64 UI (see
Table 7-9 for the encodings).

5\. The UCIe Module Partner is permitted to use the information provided in the {RECAL.track tx
adjust req} sideband message to perform Tx adjustments for drift compensation. The UCIe
Module Partner responds with a {RECAL.track tx adjust resp} sideband message after receiving
the {RECAL.track tx adjust req} sideband message. It is the responsibility of the UCIe Module
Partner to prevent the 8-ms timeout for this handshake. The UCIe Module Partner is
recommended to send the "Stall" once every 4 ms to prevent the timeout. The MsgInfo field in the
{RECAL.track tx adjust resp} sideband message has the following information (see Table 7-9 for
the encodings):

\- Drift Compensated: This indicates that the Tx of the UCIe Module Partner was successfully
able to fully or partially compensate for the drift

\- Drift not Compensated: This indicates that the $\mathrm { T x }$ of the UCIe Module Partner did not
compensate for the drift at all

\- Stall: This indicates that the Tx of the UCIe Module Partner is still working on the drift
compensation and that the Rx of the UCIe Module must reset its timeout counter

The algorithm for Tx adjustment of drift is implementation-specific; however, note that this
compensation only occurs while the LTSM is in Active state. If the response received is with "Drift
not Compensated" encoding, the receiver is permitted to compensate for the maximum-available
compensation on the Rx side before finishing the flow.

If any of the following conditions are true:

\- A {RECAL.track tx adjust resp} sideband message is not received within 8 ms of sending the
{RECAL.track tx adjust req} sideband message. Note that for the {RECAL.track tx adjust *}
sideband message handshake, the 8-ms timeout is not an error condition, and does not take
RDI to LinkError.

\- A {RECAL.track tx adjust resp} sideband message is received without the "Stall" encoding

\- LTSM transitions away from Active state

then, the Rx must finish the Runtime Recalibration flow by sending the {RECAL.track pattern done
req} sideband message. Any Tx adjustments must be stopped if the {RECAL.track pattern done
req} sideband message is received, and no subsequent {RECAL.track tx adjust resp} sideband
message is sent. The {RECAL.track tx adjust resp} sideband message should be ignored if the
message is received after deciding to finish the Runtime Recalibration flow.

6\. Upon receiving the {RECAL.track pattern done req} sideband message, the UCIe Module Partner's
Track Transmitter stops sending the pattern and sends the {RECAL.track pattern done resp}
sideband message.

7\. The UCIe Module is permitted to disable the Track Receiver upon receiving the {RECAL.track
pattern done resp} sideband message.

### 4.7 Multi-module Link

As described in Chapter 1.0, the permitted configurations for a multi-module Link are one-, two-, and
four-module configurations. In a multi-module Link, each module is assigned a dedicated Module
Identifier (Module ID), which is advertised to the remote Link partner during MBINIT. PARAM.
Chapter 5.0 defines the permitted combinations of Module ID assignments for the different scenarios
of Multi-module instantiations that must be supported by multi-module implementations.

#### 4.7.1 Multi-module initialization

Each module in a multi-module configuration must initialize and train independently, using its
sideband. If two or four modules are used, a separate multi-module PHY logic block coordinates
across the modules, as described in Section 1.2.2. The MMPL is responsible for orchestrating data
transfer and any associated byte swizzling for the Transmitters across the multiple modules such that
the remote Link partner's Receivers observe the correct byte-to-Lane mapping (i.e., for any valid
transfer, bytes are laid out from LSB to MSB in ascending order of Module ID and Lane ID across all
the active Lanes). Figure 4-43, Figure 4-44, Figure 4-45, and Figure 4-46 illustrate examples of the
aforementioned byte swizzling for some of the Standard Package configurations. M0, M1, M2, and M3
in the figures correspond to Module ID 0, Module ID 1, Module ID 2, and Module ID 3, respectively.
The figures provide the RDI byte-to-Module mapping. Figure 4-43 shows the scenario in which the
remote Link partner's Module ID is the same. Figure 4-44 shows an example of a scenario in which
the remote Link partner's Module ID is different. Figure 4-45 shows an example of width degradation
for Standard package in which the remote Link partner's Module ID is different (note that the bytes
are laid out in ascending order of Module ID and Lane ID across all the active Lanes at the Receiver in
all cases). Figure 4-46 shows a scenario in which two modules are disabled. This corresponds to a
case outlined in Chapter 5.0 in which a stacked configuration is connected with an unstacked
configuration and the M0 and M2 modules are disabled; the remaining bytes of RDI are sent over
subsequent 8-UI intervals such that M1 on the remote Link partner receives the least significant
bytes.

<table>
<caption>Figure 4-43. Example of Byte Mapping for Matching Module IDs</caption>
<tr>
<th rowspan="2"></th>
<th>Module Name</th>
<th colspan="2">M1</th>
<th colspan="2">MO</th>
<th colspan="2">M2</th>
<th colspan="2">M3</th>
</tr>
<tr>
<th>Data Bytes</th>
<th>RDI B16 -- -- RDI B31</th>
<th>RDI B16 -- -- RDI B31</th>
<th>RDI BO -- -- RDI B15</th>
<th>RDI BO -- -- RDI B15</th>
<th>RDI B32 -- -- RDI B47</th>
<th>RDI B32 -- -- RDI B47</th>
<th>RDI B48 -- -- RDI B63</th>
<th>RDI B48 -- -- RDI B63</th>
</tr>
<tr>
<td rowspan="5"></td>
<td>Tx/Rx</td>
<td>Rx (x16)</td>
<td>Tx (x16)</td>
<td>Rx (x16)</td>
<td>Tx (x16)</td>
<td>Rx (x16)</td>
<td>Tx (x16)</td>
<td>Rx (x16)</td>
<td>Tx (x16)</td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td>Tx/Rx</td>
<td>Tx (x16)</td>
<td>Rx(x16)</td>
<td>Tx (x16)</td>
<td>Rx(x16)</td>
<td>Tx (x16)</td>
<td>$R x \left( \times 1 6 \right)$</td>
<td>Tx (x16)</td>
<td>$R \times \left( \times 1 6 \right)$</td>
</tr>
<tr>
<td>Data Bytes</td>
<td>RDI B16 -- -- RDI B31</td>
<td>RDI B16 -- -- RDI B31</td>
<td>RDI BO -- -- RDI B15</td>
<td>RDI BO -- -- RDI B15</td>
<td>RDI B32 RDI B47</td>
<td>RDI B32 -- -- RDI B47</td>
<td>RDI B48 -- -- RDI B63</td>
<td>RDI B48 -- -- RDI B63</td>
</tr>
<tr>
<td>Module Name</td>
<td colspan="2">M1</td>
<td colspan="2">MO</td>
<td colspan="2">M2</td>
<td colspan="2">M3</td>
</tr>
</table>

<table>
<caption>Figure 4-44. Example of Byte Mapping for Differing Module IDs</caption>
<tr>
<th rowspan="8"></th>
<th>Module Name</th>
<th colspan="2">$M 1$</th>
<th colspan="2">MO</th>
<th colspan="2">M2</th>
<th colspan="2">M3</th>
</tr>
<tr>
<th>Data Bytes</th>
<th>RDI B16 -- -- RDI B31</th>
<th>RDI B48 -- -- RDI B63</th>
<th>RDI BO -- -- RDI B15</th>
<th>RDI B32 RDI B47</th>
<th>RDI B32 -- -- RDI B47</th>
<th>RDI BO -- -- RDI B15</th>
<th>RDI B48 -- -- RDI B63</th>
<th>RDI B16 -- -- RDI B31</th>
</tr>
<tr>
<td>$T x / R x$</td>
<td>Rx (x16)</td>
<td>Tx (x16)</td>
<td>Rx (x16)</td>
<td>Tx (x16)</td>
<td>Rx (x16)</td>
<td>Tx (x16)</td>
<td>Rx (x16)</td>
<td>Tx (x16)</td>
</tr>
<tr>
<td></td>
<td rowspan="2"></td>
<td rowspan="2"></td>
<td rowspan="2"></td>
<td rowspan="2"></td>
<td rowspan="2"></td>
<td rowspan="2"></td>
<td rowspan="2"></td>
<td rowspan="2"></td>
</tr>
<tr>
<td></td>
</tr>
<tr>
<td>$T x / R x$</td>
<td>Tx (x16)</td>
<td>Rx(x16)</td>
<td>Tx (x16)</td>
<td>Rx(x16)</td>
<td>Tx (x16)</td>
<td>Rx(x16)</td>
<td>Tx (x16)</td>
<td>Rx(x16)</td>
</tr>
<tr>
<td>Data Bytes</td>
<td>RDI B16 -- -- RDI B31</td>
<td>RDI B48 -- -- RDI B63</td>
<td>RDI BO -- -- RDI B15</td>
<td>RDI B32 RDI B47</td>
<td>RDI B32 -- -- RDI B47</td>
<td>RDI BO -- -- RDI B15</td>
<td>RDI B48 -- -- RDI B63</td>
<td>RDI B16 -- -- RDI B31</td>
</tr>
<tr>
<td>Module Name</td>
<td colspan="2">M3</td>
<td colspan="2">M2</td>
<td colspan="2">MO</td>
<td colspan="2">M1</td>
</tr>
</table>

<table>
<caption>Figure 4-45. Example of Width Degradation with Byte Mapping for Differing Module IDs</caption>
<tr>
<th rowspan="9"></th>
<th>Module Name</th>
<th colspan="2">M1</th>
<th colspan="2">MO</th>
<th colspan="2">M2</th>
<th colspan="2">M3</th>
</tr>
<tr>
<th>Data Bytes UI 15-8</th>
<th>RDI B40 -- -- RDI B47</th>
<th>RDI B57 -- -- RDI B63</th>
<th>RDI B32 -- -- RDI B39</th>
<th>RDI B48 -- -- RDI B55</th>
<th>RDI B48 -- -- RDI B55</th>
<th>RDI B32 -- -- RDI B39</th>
<th>RDI B57 -- -- RDI B63</th>
<th>RDI B40 -- -- RDI B47</th>
</tr>
<tr>
<th>Data Bytes UI 7-0</th>
<th>RDI B8 -- -- RDI B15</th>
<th>RDI B24 -- -- RDI B31</th>
<th>RDI BO -- -- RDI B7</th>
<th>RDI B16 -- -- RDI B23</th>
<th>RDI B16 -- -- RDI B23</th>
<th>RDI BO -- -- RDI B7</th>
<th>RDI B24 -- -- RDI B31</th>
<th>RDI B8 -- -- RDI B15</th>
</tr>
<tr>
<td>Tx/Rx</td>
<td>Rx (x8)</td>
<td>Tx (x8)</td>
<td>Rx (x8)</td>
<td>Tx (x8)</td>
<td>Rx (x8)</td>
<td>$T \times \left( \times 8 \right)$</td>
<td>Rx (x8)</td>
<td>Tx (x8)</td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td>$T x / R x$</td>
<td>Tx (x8)</td>
<td>Rx(x8)</td>
<td>$T x \left( x 8 \right)$</td>
<td>Rx(x8)</td>
<td>$T x \left( x 8 \right)$</td>
<td>Rx(x8)</td>
<td>$T x \left( x 8 \right)$</td>
<td>Rx(x8)</td>
</tr>
<tr>
<td>Data Bytes UI 7-0</td>
<td>RDI B8 -- -- RDI B15</td>
<td>RDI B24 -- -- RDI B31</td>
<td>RDI BO -- -- RDI B7</td>
<td>RDI B16 -- -- RDI B23</td>
<td>RDI B16 -- -- RDI B23</td>
<td>RDI BO -- -- RDI B7</td>
<td>RDI B24 -- -- RDI B31</td>
<td>RDI B8 -- -- RDI B15</td>
</tr>
<tr>
<td>Data Bytes UI 15-8</td>
<td>RDI B40 -- -- RDI B47</td>
<td>RDI B57 -- -- RDI 63</td>
<td>RDI B32 -- -- RDI B39</td>
<td>RD B48 -- -- RDI B55</td>
<td>RDI B48 -- -- RDI B55</td>
<td>RDI B32 -- -- RDI B39</td>
<td>RDI B57 -- -- RDI B63</td>
<td>RDI B40 -- -- RDI B47</td>
</tr>
<tr>
<td>Module Name</td>
<td colspan="2">M3</td>
<td colspan="2">M2</td>
<td colspan="2">MO</td>
<td colspan="2">M1</td>
</tr>
</table>

<table>
<caption>Figure 4-46. Example of Byte Mapping with Module Disable</caption>
<tr>
<th rowspan="7"></th>
<th>Module Name</th>
<th colspan="2">M1</th>
<th colspan="2">$M O$</th>
<th colspan="2">M2</th>
<th colspan="2">M3</th>
</tr>
<tr>
<th>Data Bytes</th>
<th>RDI BO -- -- RDI B15</th>
<th>RDI B16 -- -- RDI B31</th>
<th></th>
<th></th>
<th></th>
<th></th>
<th>RDI B16 -- -- RDI B31</th>
<th>RDI BO -- -- RDI B15</th>
</tr>
<tr>
<td>Tx/Rx</td>
<td>$R \times \left( \times 1 6 \right.$</td>
<td>$T x \left( x 1 6 \right)$</td>
<td>$R \times \left( \times 1 6 \right)$</td>
<td>$T \times \left( \times 1 6 \right)$</td>
<td>$R \times \left( \times 1 6 \right)$</td>
<td>$T \times \left( \times 1 6 \right)$</td>
<td>$R \times \left( \times 1 6 \right)$</td>
<td>$T \times \left( \times 1 6 \right.$</td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td colspan="2">Disabled</td>
<td colspan="2">Disabled</td>
<td></td>
<td></td>
</tr>
<tr>
<td>$T x / R x$</td>
<td>Tx (x16)</td>
<td>Rx(x16)</td>
<td>Tx (x16)</td>
<td>Rx(x16)</td>
<td>Tx (x16)</td>
<td>Rx(x16)</td>
<td>Tx (x16)</td>
<td>Rx(x16)</td>
</tr>
<tr>
<td>Data Bytes</td>
<td>RDI BO -- -- RDI B15</td>
<td>RDI B16 -- -- RDI B31</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>RDI B16 -- -- RDI B31</td>
<td>RDI BO -- -- RDI B15</td>
</tr>
<tr>
<td>Module Name</td>
<td colspan="2">M3</td>
<td colspan="2">M2</td>
<td colspan="2">MO</td>
<td colspan="2">M1</td>
</tr>
</table>

Each module in a multi-module Link must operate at the same width and speed. During initialization
or retraining, if any module failed to train, the MMPL must ensure that the multi-module configuration
degrades to the next permitted configuration for width or speed degrade (see Figure 4-47 and
Figure 4-48). Subsequently, any differences in width and speed between the different modules must
be resolved using the following rules:

1\. For Standard package multi-module configuration, if width degrade is reported for any of the
modules:

a. If less than or equal to half the number of modules report width degrade at the current Link
speed, the corresponding Modules must be disabled. The MMPL must ensure that the multi-
module configuration degrades to the next permitted configuration for width or speed degrade
(see Figure 4-47 and Figure 4-48). For example, if three out of four modules are active, the
MMPL must degrade the Link to a two-module configuration.

b. If the majority of modules report width degrade at the current Link speed, see the pseudo code
below:

<figure>

CLS: Current Link Speed
CLS-1: Next lower allowed Link Speed

M is number of active Modules

Aggregate Raw BW (M, CLS) = Common Minimum Link width * M * CLS

If modules report Width degrade:
If CLS = 4 GT/s
Apply Width degrade for all modules
Else If Aggregate Raw BW (M, (CLS-1) ) > Aggregate raw BW (M/2, CLS) :
Attempt Speed Degrade

Else :

Apply Width degrade for all modules

</figure>

When a module has been width degraded before entering LINKSPEED, the Common Minimum Link
Width is the degraded width. When modules are reporting errors that indicate width degrade
during LINKSPEED, the Common Minimum Link width is the same as when it entered LINKSPEED.

2\. For Advanced or Standard package multi-module configuration, if any Module reports speed
difference, see the pseudo code below:

<figure>

IF modules report speed difference:
CMLS: Common Maximum Link Speed

HMLS: Highest Maximum Link Speed of next lower configuration
IF HMLS/2 > CMLS :

Modules degrade to next lower configuration

Else:

Speed for all modules degrades to CMLS

</figure>

Figure 4-47 and Figure 4-48 provide a consolidated view of the above two rules as a flow chart that
Advanced Package and Standard Package implementations, respectively, must follow. Note that the
"Yes" condition for HMLS/2 > CMLS question is there to cover the base case of 4 GT/s. In other words,
if some module(s) passed MBINIT but failed 4 GT/s in LinkSpeed, then the "Yes" arc will result in
module disable instead of TrainError (because CMLS will be 0 for that) and provide the opportunity to
remain operational at 4 GT/s for the modules that were still operational at 4 GT/s.

<figure>
<figcaption>Figure 4-47. Decision Flow Chart for Multi-module Advanced Package</figcaption>

LinkSpeed

1

Any enabled
module reporting
errors?

Speedidle

Repair

NO

LinkInit

Yes

Operational Modules
Transition to LINKINIT

equal $\begin{array}{} { \text { less than or } } \\ { \text { ato half modules } } \end{array}$
report error and
unrepairable and no speed
degrade possible

Modules with errors
$d i s a b l e d \quad t o \quad r e a c h \quad n e x t$
lower module count
configuration

Yes

1

Z
O

Yes

Yes

All Modules with
errors repairable?

Any modules with an
operational configuration?

TRAINERROR

No

Z
0

Some modules
will report speed
degrade

Speed degrade
all modules

HMLS/2 >
CMLS?

Modules reporting speed
$d e g r a d e \quad d i s a b l e d \quad t o \quad r e a c h$
next lower module count
configuration

No

Yes

</figure>

<figure>
<figcaption>Figure 4-48. Decision Flow Chart for Multi-module Standard Package</figcaption>

LinkSpeed

1

Any enabled
module reporting
errors?

Speedidle

Width
Degrade

$N O$

LINKINIT

Yes-

Operational Modules
Transition to
LINKINIT

Less than or equal to half
number of modules report error
and all modules with errors
report width degrade

Modules with errors
disabled to reach next
lower module count
configuration

Yes

1

Yes

$B W \left( M , \left( C L S - 1 \right) \right) >$
BW (M/2, CLS)?

More than half number of modules
report errors and all modules with
errors report width degrade

No

Yes

Any modules with an
operational configuration ?
No

TRAINERROR

+Yes

This arc implies at least one
module reported speed
degrade

Speed degrade
all operational
modules

Modules reporting speed
degrade disabled to reach
next lower module count
configuration

$\begin{array}{} { \text { HMLS/2 } } \\ { \text { CMLS? } } \end{array}$ >

No

Yes

</figure>

##### 4.7.1.1 Sideband Assignment and Retimer Credits for Multi-module Configurations

During Link initialization, training and retraining (see Section 4.5) certain sideband packets are sent
on individual module sideband interfaces. These include all the messages in Table 7-9 and Table 7-11,
and any vendor-defined messages that were defined as such.

Other sideband packets use a single sideband to send sideband packets. These include Register
Access packets (requests as well as completions), all the non-vendor defined messages in Table 7-8
and Table 7-10, and any vendor-defined messages that were defined as such. A device must send
these sideband packets on the sideband interface of the numerically least Module ID whose LTSM is
not in RESET or SBINIT. A packet sent on a given Module ID could be received on a different Module
ID on the sideband Receiver.

Similarly, Retimer credits are returned on the Valid signal of the numerically least Module ID whose
LTSM is in Active state. Credits sent on a given Module ID could be received on a different Module ID
on the remote Link partner.

##### 4.7.1.2 Examples of MMPL Synchronization

When a module is part of a multi-module UCIe Link, it performs individual training steps through
Step 2 of MBTRAIN.LINKSPEED independent of other modules using its own sideband Link. This is
true for both Link Initialization and Link Retraining. The common Link parameters exchanged in
MBINIT.PARAM are the same for all modules that are part of the multi-module Link (for example the
"Maximum Data Rate"). Thus, when in MBTRAIN.LINKSPEED, all modules of a multi-module Link are
operating at the same data rate.

The synchronization orchestration by MMPL occurs in the MBTRAIN.LINKSPEED state based on the
rules outlined in Section 4.7.1. Note that different modules of a multi-module Link could take a
different amount of time to finish the individual training steps to reach MBTRAIN.LINKSPEED. In the
unlikely scenario where the staggering is greater than 8 ms, this could cause a module waiting in

MBTRAIN.LINKSPEED to time out while waiting for other modules to finish. As outlined in
Section 4.5.3.4.12, after Step 2 of MBTRAIN.LINKSPEED has completed and PHY_IN_RETRAIN is not
set:

· If no errors are encountered for a module, an {MBTRAIN.LINKSPEED done req} is sent to the
remote Link partner module

· If errors are encountered for a module, an {MBTRAIN.LINKSPEED error req}/
{MBTRAIN.LINKSPEED error resp} handshake is performed followed by sending an
{MBTRAIN.LINKSPEED exit to repair req} or an {MBTRAIN.LINKSPEED exit to speed degrade req}
on that module's sideband.

The individual modules notify the MMPL of the sent and received information from these sideband
messages. MMPL collects this information from all the modules which are operational in the Link and
determines the next state based on resolution of the rules outlined in Section 4.7.1. Of course, the
case without errors is when all modules sent and received the {MBTRAIN.LINKSPEED done req}
message with no change to Link width. In this scenario, the MMPL directs them to proceed to Step 6
of MBTRAIN.LINKSPEED.

The following sections cover a few examples of this resolution for a Link with four modules and
Standard Package configuration where errors were encountered.

#### 4.7.1.2.1 Example 1: MMPL Resolution results in a Width Degrade per Module

In this example, the four modules of the UCIe Link are in MBTRAIN.LINKSPEED at 8 GT/s. Table 4-13
shows the exchanged messages for one die (in the case where errors are encountered, it is assumed
that the {MBTRAIN.LINKSPEED error req}/ {MBTRAIN.LINKSPEED error resp} has completed before
the messages shown). Because the resolution is consistent in using the sent and received messages,
both die of the Link will reach the same resolution.

<table>
<caption>Table 4-13. Messages exchanged that are used to determine resolution for Example 1</caption>
<tr>
<th>Module Identifier</th>
<th>Sent Message</th>
<th>Received Message</th>
</tr>
<tr>
<td>Module 0</td>
<td>{MBTRAIN.LINKSPEED done req}</td>
<td>{MBTRAIN.LINKSPEED done req}</td>
</tr>
<tr>
<td>Module 1</td>
<td>{MBTRAIN.LINKSPEED exit to repair req}</td>
<td>{MBTRAIN.LINKSPEED done req}</td>
</tr>
<tr>
<td>Module 2</td>
<td>{MBTRAIN.LINKSPEED done req}</td>
<td>{MBTRAIN.LINKSPEED exit to repair req}</td>
</tr>
<tr>
<td>Module 3</td>
<td>{MBTRAIN.LINKSPEED exit to repair req}</td>
<td>{MBTRAIN.LINKSPEED exit to repair req}</td>
</tr>
</table>

In this example, 3 out of the 4 modules have either sent or received the {MBTRAIN.LINKSPEED exit
to repair req} message which indicate a width degrade for Standard Package configurations. The
value of "CLS" (Current Link Speed) is 8 GT/s, and the value of "CLS-1" is 4 GT/s. The value of ${ } ^ { 1 1 } M ^ { \prime \prime }$
(Number of Active Modules) is 4. Because BW (4 Links at 4 GT/s) is not greater than BW (2 Links at 8
GT/s), the flow chart in Figure 4-48 would result in the MMPL notifying all the modules to proceed
with a width degrade by moving to MBTRAIN.REPAIR as the next state (i.e., {MBTRAIN.LINKSPEED
exit to repair resp} will be sent on each Module). Note that "CLS" and "M" are re-computed using the
updated information every time the Link is MBTRAIN.LINKSPEED and there is a corresponding MMPL
resolution. Width degrade is applied per module following the steps in MBTRAIN.REPAIR for every
module in this UCIe Link. For the module where no errors were encountered, the transmitter is
permitted to pick either of Lanes 0 to 7 or Lanes 8 to 15 as the operational Lanes when transmitting
the {MBTRAIN.REPAIR apply degrade req} to the remote Link partner module. Following the exit from
MBTRAIN.REPAIR, the training continues through the substates of MBTRAIN and in the next iteration
of MBTRAIN.LINKSPEED, if no errors are encountered, MMPL will direct the modules to proceed to
Step 6 of MBTRAIN.LINKSPEED.

Note that this example is covering the case where errors occurred during the LINKSPEED state. If the
width of a module is already lower from the rest of the operational modules that are part of a multi-

module Link (e.g., if a module had degraded width during MBINIT.REPAIRMB itself), it may have sent
and received {MBTRAIN.LINKSPEED done req} during LINKSPEED. However, from a MMPL resolution
perspective, MMPL must treat this as a Module reporting errors requiring width degrade. This is
because a multi-module Link requires all modules to operate at the same width and speed.

#### 4.7.1.2.2 Example 2: MMPL Resolution results in a Speed Degrade

In this example, the four modules of the UCIe Link are in MBTRAIN.LINKSPEED at 16 GT/s. Table 4-14
shows the exchanged messages for one die (in the case where errors are encountered, it is assumed
that the {MBTRAIN.LINKSPEED error req}/ {MBTRAIN.LINKSPEED error resp} has completed before
the messages shown). Because the resolution is consistent in using the sent and received messages,
both die of the Link will reach the same resolution.

<table>
<caption>Table 4-14. Messages exchanged that are used to determine resolution for Example 2</caption>
<tr>
<th>Module Identifier</th>
<th>Sent Message</th>
<th>Received Message</th>
</tr>
<tr>
<td>Module 0</td>
<td>{MBTRAIN.LINKSPEED exit to repair req}</td>
<td>{MBTRAIN.LINKSPEED done req}</td>
</tr>
<tr>
<td>Module 1</td>
<td>{MBTRAIN.LINKSPEED done req}</td>
<td>{MBTRAIN.LINKSPEED done req}</td>
</tr>
<tr>
<td>Module 2</td>
<td>{MBTRAIN.LINKSPEED done req}</td>
<td>{MBTRAIN.LINKSPEED done req}</td>
</tr>
<tr>
<td>Module 3</td>
<td>{MBTRAIN.LINKSPEED done req}</td>
<td>{MBTRAIN.LINKSPEED exit to speed degrade req}</td>
</tr>
</table>

In this example, Module 3 has received a message indicating that the remote partner wants to speed
degrade. "CMLS" always maps to the next degraded Link speed and so in this case "CMLS" is 12 GT/s.
"HMLS" always ends up mapping to current Link speed and so in this case it is 16 GT/s. Because
Module 3 received a speed degrade request, following the flow chart in Figure 4-48, this would result
in MMPL notifying all the modules to proceed with a speed degrade by moving to
MBTRAIN.SPEEDIDLE (i.e. {MBTRAIN.LINKSPEED exit to speed degrade resp} will be sent on each
Module). Following the exit from MBTRAIN.SPEEDIDLE, the training continues through the substates
of MBTRAIN and in the next iteration of MBTRAIN.LINKSPEED, if no errors are encountered, MMPL will
direct the modules to proceed to Step 6 of MBTRAIN.LINKSPEED. Note that "CMLS" and "HMLS" are
using the updated information every time the Link is MBTRAIN.LINKSPEED and there is a
corresponding MMPL resolution. In this example, for the next iteration, CMLS will be 8 GT/s and HMLS
will be 12 GT/s.

#### 4.7.1.2.3 Example 3: MMPL Resolution results in a Module Disable

In this example, the four modules of the UCIe Link are in MBTRAIN. LINKSPEED at 16 GT/s. Table 4-15
shows the exchanged messages for one die (in the case where errors are encountered, it is assumed
that the {MBTRAIN.LINKSPEED error req}/ {MBTRAIN.LINKSPEED error resp} has completed before
the messages shown). Because the resolution is consistent in using the sent and received messages,
both die of the Link will reach the same resolution.

<table>
<caption>Table 4-15. Messages exchanged that are used to determine resolution for Example 3</caption>
<tr>
<th>Module Identifier</th>
<th>Sent Message</th>
<th>Received Message</th>
</tr>
<tr>
<td>Module 0</td>
<td>{MBTRAIN.LINKSPEED done req}</td>
<td>{MBTRAIN.LINKSPEED done req}</td>
</tr>
<tr>
<td>Module 1</td>
<td>{MBTRAIN.LINKSPEED exit to repair req}</td>
<td>{MBTRAIN.LINKSPEED done req}</td>
</tr>
<tr>
<td>Module 2</td>
<td>{MBTRAIN.LINKSPEED done req}</td>
<td>{MBTRAIN.LINKSPEED done req}</td>
</tr>
<tr>
<td>Module 3</td>
<td>{MBTRAIN.LINKSPEED done req}</td>
<td>{MBTRAIN.LINKSPEED done req}</td>
</tr>
</table>

Because less than half of the modules are reporting errors and requesting a width degrade, as per the
flow chart in Figure 4-48, MMPL would take the configuration to a two module configuration. As per
the rules in Section 5.7.3.4.1, Module 0 and Module 1 would send the {MBTRAIN.LINKSPEED multi-

module disable module resp} to take these modules to TRAINERROR and RESET. Module 2 and
Module 3 would send the {MBTRAIN.LINKSPEED done resp} to take them to LINKINIT.

### 4.7.2 Multi-module Interoperability between x64 and x32 Advanced Packages

MMPL is responsible for the appropriate byte swizzling and width adjustment when a multi-module
x64 Advanced Package module is connected to a corresponding multi-module x32 Advanced Package
module. All the modules in a multi-module configuration must be of the same type (in this context, all
the modules within a multi-module set must be x64 Advanced or x32 Advanced). All the rules related
to module naming conventions and disabled configurations apply to x32 Advanced Package Modules
as well.

One example of interoperation between UCIe-A x64 and UCIe-A x32 is when the UCIe-A x64 Stack
(including RDI and FDI maximum throughput) is bandwidth-matched (Full Width Mode) by the remote
Link partner's maximum throughput for a given interface. Figure 4-49 shows an example of two x64
modules that are capable of operating as two independent UCIe stacks with independent Adapters
and Protocol Layers (bypass MMPL logic in configuration (a) in Figure 4-49) and is also capable of
operating as a multi-module configuration when connected to a corresponding multi-module
configuration of x32 Advanced Package to achieve the equivalent bandwidth of a single x64 module
(configuration (b) in Figure 4-49). In the latter configuration, one of the Adapters (shown in gray) is
disabled.

Software and firmware are permitted to use UCIe DVSEC Link Capability and Control registers to
determine within which configuration to train the link.

Figure 4-49. Implementation Example Showing Two Different Operating Modes
of the Same Hardware Implementation

<table>
<tr>
<th>Physical Layer (x64 module)</th>
<th>Physical Layer (x64 module)</th>
</tr>
<tr>
<td>AFE</td>
<td>$\mathrm { A F E }$</td>
</tr>
</table>

<figure>

Die-to-Die
Adapter

Die-to-Die
Adapter

Die-to-Die
Adapter

Die-to-Die
Adapter

RDI

RDI

Multi-module PHY Logic
(two x64 modules operating in x32 mode)

Module 0 AFE/PHY Logic

Module 1 AFE/PHY Logic

Two D2D stacks $e n a b l e d ;$ MMPL bypassed and each stack uses
one module and operates in Full Width mode
For each stack.

Only one D2D stack enabled; Uses MMPL with two modules and
operates in Full Width mode

(a)

(b)

</figure>

<table>
<tr>
<th rowspan="2">UCIe Link DVSEC Capability Register</th>
<th>Max Link Width</th>
<th>×64</th>
</tr>
<tr>
<td>APMW</td>
<td>0</td>
</tr>
<tr>
<td>Link Training Parameter</td>
<td>UCIe-A x32</td>
<td>0</td>
</tr>
</table>

<table>
<tr>
<th rowspan="2">UCIe Link DVSEC Capability Register</th>
<th>Max Link Width</th>
<th>×64</th>
</tr>
<tr>
<th>APMW</th>
<th>1</th>
</tr>
<tr>
<td>Link Training Parameter</td>
<td>UCIe-A x32</td>
<td>1</td>
</tr>
</table>

Another example of interoperation between UCIe-A x64 and UCIe-A x32 is when the UCIe-A x64
Stack degrades bandwidth (Degraded Width Mode) to match the remote Link partner's maximum
throughput. Figure 4-50 shows an example of RDI byte-to-module assignments for a four-module set
of x64 Advanced Package modules interoperating with a four-module set of x32 Advanced Package
modules. The example is for a 256B RDI width on the x64 set, and a 128B RDI on the x32 set. On the
Transmitter side of x64 modules, the MMPL throttles RDI, as required, because the MMPL can only
send half the bytes over 8 UI; and on the Receiver side, the MMPL accumulates 16 UI worth of data
before forwarding it over RDI (assumes data transfers are in chunks of 256B OR appropriate pause of
data stream indications are applied and detected by MMPLs/Adapters within the data stream).

<table>
<caption>Figure 4-50. RDI Byte-to-Module Assignment Example for $x 6 4$ Interop with $x 3 2$</caption>
<tr>
<th colspan="10"></th>
</tr>
<tr>
<th></th>
<th></th>
<th colspan="2">M1</th>
<th colspan="2">MO</th>
<th colspan="2">M2</th>
<th colspan="2">M3</th>
</tr>
<tr>
<td rowspan="8"></td>
<td>$U I \quad 8 \quad - \quad 1 5$</td>
<td>RDI B160 -- -- RDI B191</td>
<td>RDI B224 -- -- RDI B255</td>
<td>RDI B128 -- -- RDI B159</td>
<td>RDI B192 -- -- RDI B223</td>
<td>RDI B192 -- -- RDI B223</td>
<td>RDI B128 -- -- RDI B159</td>
<td>RDI B224 -- -- RDI B255</td>
<td>RDI B160 -- -- RDI B191</td>
</tr>
<tr>
<td>UI 0 - 7</td>
<td>RDI B32 -- -- RDI B63</td>
<td>RDI B96 -- -- RDI B127</td>
<td>RDI BO -- -- RDI B31</td>
<td>RDI B64 -- -- RDI B95</td>
<td>RDI B64 -- -- RDI B95</td>
<td>RDI BO -- -- RDI B31</td>
<td>RDI B96 -- -- RDI B127</td>
<td>RDI B32 -- -- RDI B63</td>
</tr>
<tr>
<td rowspan="3"></td>
<td>$R \times \left( \times 3 2 \right)$</td>
<td>Tx (x32)</td>
<td>Rx (x32)</td>
<td>Tx (x32)</td>
<td>Rx (x32)</td>
<td>$T x \left( x 3 2 \right)$</td>
<td>Rx (x32)</td>
<td>Tx (x32)</td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td>Tx (x64)</td>
<td>Rx(x64)</td>
<td>Tx (x64)</td>
<td>Rx(x64)</td>
<td>Tx (x64)</td>
<td>Rx(x64)</td>
<td>Tx (x64)</td>
<td>Rx(x64)</td>
</tr>
<tr>
<td>$U I \quad 0 \quad - \quad 7$</td>
<td>RDI B32 -- -- RDI B63</td>
<td>RDI B96 -- -- RDI B127</td>
<td>RDI BO -- -- RDI B31</td>
<td>RDI B64 -- -- RDI B95</td>
<td>RDI B64 -- -- RDI B95</td>
<td>RDI BO -- -- RDI B31</td>
<td>RDI B96 -- -- RDI B127</td>
<td>RDI B32 -- -- RDI B63</td>
</tr>
<tr>
<td>$U I \quad 8 \quad - \quad 1 5$</td>
<td>RDI B160 -- -- RDI B191</td>
<td>RDI B224 RDI B255</td>
<td>RDI B128 -- -- RDI B159</td>
<td>RDI B192 -- -- RDI B223</td>
<td>RDI B192 -- -- RDI B223</td>
<td>RDI B128 -- -- RDI B159</td>
<td>RDI B224 -- -- RDI B255</td>
<td>RDI B160 -- -- RDI B191</td>
</tr>
<tr>
<td></td>
<td colspan="2">M3</td>
<td colspan="2">M2</td>
<td colspan="2">MO</td>
<td colspan="2">M1</td>
</tr>
</table>

For the example shown in Figure 4-50, a single Adapter is operating with all four Modules. The D2D
stack uses MMPL with 4 modules, with each of the x64 modules operating in Degraded Width Mode,
and only 32 lanes routed per module. The corresponding values in the capability register and Link
Training parameter are as listed in Table 4-16.

<table>
<caption>Table 4-16. Capability Register and Link Training Parameter Values for RDI Byte-to-Module Assignment Example for x64 Interop with $x 3 2$</caption>
<tr>
<td rowspan="2">UCIe Link DVSEC Capability Register</td>
<td>Max Link Width</td>
<td>$\times 1 2 8$</td>
</tr>
<tr>
<td>APMW</td>
<td>1</td>
</tr>
<tr>
<td>Link Training Parameter</td>
<td>UCIe-A x32</td>
<td>1</td>
</tr>
</table>

See Section 5.7.2.4 for comprehensive rules of interoperation between x64 and x32 Advanced
Package modules.

### 4.8 Sideband PHY Arbitration between MPMs and Link Management Packets

While the exact arbitration policy is implementation specific, care should be taken to avoid delaying
transmitting any pending link management packets for extended lengths of time potentially causing
timeouts. See Section 8.2.5.1.2 for length restriction on MPMs with Data that allows for PHY
arbitration to provide an upper bound on the amount of delay to send a link management packet or a
higher-priority MPM packet that might be waiting behind an MPM with Data packet. Additionally, PHY
transmitter must fully complete transmission of an MPM with Data within 512 UI max (when Sideband
Performant Mode Operation is negotiated) and 768 UI max (when Sideband Performant Mode

Operation is not negotiated). See Section 4.1.5 for details of sideband transmission UI notation. See
Section 4.1.5.1 for Performant Mode Operation (PMO) details.

Figure 4-51 and Figure 4-52 show the arbitration at the PHY.

<figure>
<figcaption>Figure 4-51. Example of Encapsulated MTPs Transmitted on Sideband Link without Sideband PMO</figcaption>

1 Encapsulated MTP with
maximum payload length of
7 QWORDs sent over 768 UI

A "Link Management" packet can be sent
here by arbiter, if pending, or another
Encapsulated MTP can start here

Encapsulated
$\mathrm { M T P }$ Header

IDLE

Encapsulated
MTP Payload

IDLE

Encapsulated
MTP Header

64 UI

32 UI

64 UI

32 UI

64 UI

Time

</figure>

<figure>
<figcaption>Figure 4-52. Example of a Large Management Packet Split into Two Encapsulated MTPs, with No Segmentation, No Sideband PMO, and with Two Link Management Packets between the Two Encapsulated MTPs</figcaption>

1st Encapsulated MTP from a large
Management Packet

2nd Encapsulated MTP from the same
large Management Packet starts here ...

Link Management Msg without Data

Link Management Msg with Data

Encapsulated
MTP Header

IDLE

Encapsulated
MTP Payload
QWORD 0

IDLE

Encapsulated
MTP Payload
QWORD 6

IDLE

Link Mgmt
Msg
Header

IDLE

Link Mgmt
MsgD
Header

IDLE

Link Mgmt
MsgD
Payload

IDLE

Encapsulated
MTP Header

IDLE

64 UI

32 UI

64 UI

32 UH

64 UI

32 UH

64 UI

32 UH

64 UI

32 UI

64 UI

32 UH

64 UI

32 UH

Time

</figure>

### 5.0 Electrical Layer (2D and 2.5D)

Key attributes of electrical specification include:

· Support for 4, 8, 12, 16, 24, 32, 48, and 64 GT/s data rates

· Support for Advanced and Standard package interconnects

· Support for clock and power gating mechanisms

· Single-ended unidirectional data signaling

· DC coupled point-to-point interconnect

· Forwarded clock for transmit jitter tracking

· Matched length interconnect design within a module

· For Advanced Package:

\- Tx driver strength control

\- Unterminated Rx for up to 32 GT/s

\- Terminated Rx for 48 GT/s and 64 GT/s

. Tx termination and data rate and channel reach dependent Rx termination for Standard Package

#### 5.1 Interoperability

##### 5.1.1 Data rates

A device must support 4 GT/s and all the data rates data rates between 4 GT/s and the highest
supported data rate. For example, a device supporting 16 GT/s must also support 4, 8, and 12 GT/s
data rates. References to data rates refer to the current operating speed unless the negotiated
maximum data rate is specifically mentioned.

Spread-Spectrum Clocking (SSC) is permitted. Common reference clock (REFCLK) is required
between a UCIe Link Transmitter and the corresponding UCIe Link partner's Receiver with a transport
delay difference less than 5 ns to limit the FIFO depth and minimize the latency impact. For the
retimer use case, the "Local UCIe Link connection" shall use common REFCLK, while the "Off-Package
Link connection" is not required to use or share the common REFCLK. Figure 5-1 shows the transport
delay difference and is symmetrical for both directions of a Die's UCIe Link connection. The transport
delay represents the delay difference between the Transmitter data to the Receiver data latch and the
clock as seen at the receiver's FIFO output data latch. See Section 5.1.2 for REFCLK details.

<figure>
<figcaption>Figure 5-1. Example Common Reference Clock</figcaption>

$D i e - 1$

Die-2

Data

TX Flop

$R x \quad F l o p + F I F O$

Clock
Phase

TXCK

RXCK

$T _ { 1 }$

$T = | T _ { 1 } - T _ { 2 } |$

$T _ { 2 }$

TX PLL

Ref
Clock

RX PLL

</figure>

# IMPLEMENTATION NOTE

In typical implementations, the LCLK for UCIe Link Transmitter and LCLK for the
corresponding link partner Receiver, are both generated from the common reference
clock. In the example implementation of Figure 5-1, the LCLK for Transmitter in Die-1
can be generated from TX PLL and the LCLK for Receiver in Die-2 can be generated
from the RX PLL.

## 5.1.2 Reference Clock (REFCLK)

Common reference clock (REFCLK) uses a single source that is distributed to both the Transmitter and
the Receiver. The clock can be supplied from a package pin or be forwarded by another die on the
package. In either case, the reference clock used by both dies on the same link must be from the
same clock source. Although other reference clocks are possible, it is recommended that every chiplet
use a 100-MHz reference clock, including both dies having different reference clock values from the
same clock source. Table 5-1 lists the permitted reference clock frequency range. The minimum and
maximum frequencies listed in the table indicate the limits, and do not indicate a requirement to
support the entire frequency range. It is required for implementations to generate precise I/O clock
frequencies for the supported data rates that use the reference clock. Note that this is possible if the
I/O clock frequency is an exact integer multiple of the reference clock frequency (if different from 100
MHz). The reference clock may be disabled in low-power states (such as is done in other Standards
and Specifications).

<table>
<caption>Table 5-1. REFCLK Frequency PPMs and SSC PPMs (Sheet 1 of 2)</caption>
<tr>
<th rowspan="2">Symbol</th>
<th rowspan="2">Description</th>
<th colspan="3">Limits</th>
<th rowspan="2">Unit</th>
<th rowspan="2">Notes</th>
</tr>
<tr>
<th>Min</th>
<th>Rec</th>
<th>Max</th>
</tr>
<tr>
<td>$\mathrm { F } _ { \mathrm { R E F C L K } }$</td>
<td>REFCLK Frequency</td>
<td>25</td>
<td>100</td>
<td>200</td>
<td>MHz</td>
<td></td>
</tr>
<tr>
<td>FREFCLKDEVIATION</td>
<td>REFCLK Frequency Deviation</td>
<td>-300</td>
<td></td>
<td>300</td>
<td>ppm</td>
<td>Maximum deviation allowed from ideal target frequency.</td>
</tr>
<tr>
<td>$\mathrm { F s s c }$</td>
<td>SSC Modulation Frequency</td>
<td>30</td>
<td></td>
<td>33</td>
<td>kHz</td>
<td></td>
</tr>
</table>

<table>
<caption>Table 5-1. REFCLK Frequency PPMs and SSC PPMs (Sheet 2 of 2)</caption>
<tr>
<th rowspan="2">Symbol</th>
<th rowspan="2">Description</th>
<th colspan="3">Limits</th>
<th rowspan="2">Unit</th>
<th rowspan="2">Notes</th>
</tr>
<tr>
<th>Min</th>
<th>Rec</th>
<th>Max</th>
</tr>
<tr>
<td>TSSC-FREQ-DEVIATION</td>
<td>SSC Deviation</td>
<td>-0.5</td>
<td></td>
<td>0</td>
<td>%</td>
<td>Tracks for different frequencies.</td>
</tr>
<tr>
<td>TTRANSPORT-DELAY</td>
<td>Tx-to-Rx Transport Delay</td>
<td></td>
<td></td>
<td>5</td>
<td>ns</td>
<td></td>
</tr>
<tr>
<td>TSSC-MAX-FREQ-SLEW</td>
<td>SSC df/dt</td>
<td></td>
<td></td>
<td>1250</td>
<td>ppm/us</td>
<td></td>
</tr>
</table>

### 5.2 Overview

#### 5.2.1 Interface Overview

High-level block diagrams of UCIe PHY are shown in Figure 5-2 and Figure 5-3. The UCIe physical
interface consists of building blocks called Modules. A Module that uses advanced packaging
technology (e.g., EMIB, CoWoS) called "Advanced Package Module" consists of a pair of clocks, 64 or
32 single-ended data Lanes for x64 or x32 Advanced Package Module, respectively, a data valid Lane
each direction (transmit and receive) and a Track Lane. There is a low-speed sideband bus for
initialization, Link training, and configuration reads/writes. The sideband consists of a single-ended
sideband data Lane and single-ended sideband clock Lane in both directions (transmit and receive).

The x16 or x8 "Standard Package Module" uses a traditional Standard packaging with larger pitch. A
Standard Package Module consists of a pair of clocks, 16 or 8 single-ended data Lanes, a data valid
Lane and Track Lane in each direction (transmit and receive). There is a low-speed sideband bus for
initialization, Link training, and configuration reads/writes. The sideband consists of a single-ended
sideband data Lane and single-ended sideband clock Lane in both directions (transmit and receive).

For some applications, multiple modules (2 or 4) can be aggregated to deliver additional bandwidth.

To avoid reliability issues, it is recommended to limit the Transmitter output high $\left( V _ { O H } \right)$ to a maximum
of 100 mV above the receiving chiplet's Receiver front-end circuit power supply rail. An over-stress
protection circuit may be implemented in the Receiver when $\mathrm { V } _ { O H }$ is more than 100 mV above the
Receiver power supply rail.

<figure>
<figcaption>Figure 5-2. x64 or x32 Advanced Package Module</figcaption>

Multi-die Advanced Package Module

$D i e - 1$

Mainband

$D i e - 2$

x64/x32 Data

2 Clock

1 Valid

1 Track

R
R

T

T

R

x
☒

x
☒

x64/x32 Data

x

x

Module

2 Clock

Module

1 Valid

1 Track

SB Data

R

T

SB Clock

T
R

☒
x

x
☒

SB Data

x

x

SB Clock

Sideband

</figure>

<figure>
<figcaption>Figure 5-3. x16 or x8 Standard Package Module</figcaption>

Multi-die Standard Package Module

Die-1

Mainband

Die-2

x16/x8 Data.

2 Clock

1 Valid

1 Track

R

T

T

R

x
☒

$X$
☒

☒

x16/x8 Data

x
☒

x

Module

2 Clock

Module

1 Valid

1 Track

SB Data

R

T

SB Clock

T
R

x
☒

$X$
☒

SB Data

x

x

SB Clock

Sideband

</figure>

#### 5.2.2 Electrical Summary

Table 5-2 defines the PHY electrical characteristics of a UCIe device <= to 32 GT/s. Table 5-3 defines
the PHY electrical characteristics of a UCIe device > 32 GT/s.

<table>
<caption>Table 5-2. Electrical Summary for 4 $\mathrm { G T } / \mathrm { s }$ to 32 GT/s</caption>
<tr>
<th>Parameter</th>
<th colspan="3">Advanced Package (x64)</th>
<th colspan="4">Standard Package</th>
</tr>
<tr>
<td>Data Width (per module)</td>
<td>64</td>
<td>64</td>
<td>64</td>
<td>16</td>
<td>16</td>
<td>16</td>
<td>16</td>
</tr>
<tr>
<td>Data Rate (GT/s)</td>
<td>$4 / 8 / 1 2$</td>
<td>16</td>
<td>$2 4 / 3 2$</td>
<td>4-16</td>
<td>$4 / 8 / 1 2$</td>
<td>16</td>
<td>$2 4 / 3 2$</td>
</tr>
<tr>
<td>$P o w e r \quad E f f i c i e n c y \quad T a r g e t \left( p J / b \right)$</td>
<td colspan="2">See Table 1-4</td>
<td colspan="5"></td>
</tr>
<tr>
<td>$\begin{array}{} \text { Latency Target } \left( T x + R x \right) \left( U I \right) ^ { a } \\ \text { \left(Target upper bound\right) } \end{array}$</td>
<td>12</td>
<td>12</td>
<td>16</td>
<td>12</td>
<td>12</td>
<td>12</td>
<td>16</td>
</tr>
<tr>
<td>$I d l e \quad E x i t / E n t r y \quad L a t e n c y \left( n s \right)$ (Target upper bound)</td>
<td>0.5</td>
<td>1</td>
<td>1</td>
<td>0.5</td>
<td>0.5</td>
<td>1</td>
<td>1</td>
</tr>
<tr>
<td>Idle Power (% of peak power) (Target upper bound)</td>
<td>15</td>
<td>15</td>
<td>15</td>
<td>15</td>
<td>15</td>
<td>15</td>
<td>15</td>
</tr>
<tr>
<td>Channel Reach (mm)</td>
<td>2</td>
<td>2</td>
<td>2</td>
<td>2-10</td>
<td>25</td>
<td>25</td>
<td>25</td>
</tr>
<tr>
<td>Die Edge Bandwidth Density (GB/s/mm)b</td>
<td colspan="7">See Table 1-4</td>
</tr>
<tr>
<td>Bandwidth area density (GB/s/mm2)</td>
<td>$1 5 8 / 3 1 6 / 4 7 3$</td>
<td>631</td>
<td>710/947</td>
<td>21-85</td>
<td>21/42/64</td>
<td>85</td>
<td>$1 0 9 / 1 4 5$</td>
</tr>
<tr>
<td>PHY dimension width per module (um)c</td>
<td>388.8</td>
<td>388.8</td>
<td>388.8</td>
<td>$5 7 1 . 5$</td>
<td>571.5ª</td>
<td>571.5ª</td>
<td>571.5ª</td>
</tr>
<tr>
<td>$\left( u m \right) ^ { e }$</td>
<td>1043</td>
<td>1043</td>
<td>1225</td>
<td>1320</td>
<td>1320</td>
<td>1320</td>
<td>1540</td>
</tr>
<tr>
<td>ESDf</td>
<td colspan="7">30-V CDM (Anticipating going $\left. t o \quad 5 - 1 0 \quad V \quad i n \quad f u t u r e . \right)$</td>
</tr>
</table>

a. Electrical PHY latency target. For overall latency target, see Table 1-4.

b. See Table 1-4.

c. For compatibility, PHY dimension width must match spec for Advanced Package. Tolerance of PHY dimension width for Standard
Package can be higher because there is more routing flexibility. For best channel performance, it's recommended for width to
be close to spec.

d. Standard Package PHY dimension width is the effective width of one (x16) module based on x32 interface (see Figure 5-46 and
Figure 5-47).

e. PHY dimension depth is an informative parameter and depends on bump pitch. Number in the table is based on 45-um bump
pitch for 10-column x64 Advanced Package and 100-um bump pitch for Standard Package. See Section 5.7.2 for informative
values of PHY dimension depth for combinations of the x64 and x32 Advanced Package modules in 10-column, 16-column, and
8-column bump matrix construction. Different variants of bump map that are deeper are required at high data rates.

f. Reference (Industry Council on ESD Target Levels): White Paper 2: A Case for Lowering Component-level CDM ESD
Specifications and Requirements.

<table>
<caption>Table 5-3. Electrical Summary for 48 GT/s and 64 GT/s</caption>
<tr>
<th>Parameter</th>
<th colspan="2">Advanced Package (x64)</th>
<th colspan="2">Standard Package</th>
</tr>
<tr>
<td>Data Width (per module)</td>
<td>64</td>
<td>64</td>
<td>16</td>
<td></td>
</tr>
<tr>
<td>Data Rate $\left( G T / s \right)$</td>
<td>48</td>
<td>$6 4$</td>
<td>48</td>
<td>$\frac { 1 6 } { 6 4 }$</td>
</tr>
<tr>
<td>Power Efficiency Target (pJ/b)</td>
<td colspan="2">$S e e \quad T a b l e \quad 1 - 4$</td>
<td colspan="2"></td>
</tr>
<tr>
<td>$\begin{array}{} { \text { Latency Target } \left( T x + R x \right) \left( U I \right) ^ { 6 } } \\ { \text { \left(Target upper bound\right) } } \end{array}$</td>
<td>24</td>
<td>32</td>
<td>24</td>
<td>32</td>
</tr>
<tr>
<td>$\begin{array}{} { \text { Idle Exit/Entry Latency } \left( n s \right) } \\ { \text { \left(Taraet upoer bound\right) } } \end{array}$</td>
<td>1</td>
<td>1</td>
<td>1</td>
<td>1</td>
</tr>
<tr>
<td>$\mathrm { I d l e } \mathrm { P o w e r b }$ (% of peak power) (Target upper bound)</td>
<td>20</td>
<td>20</td>
<td>25</td>
<td>25</td>
</tr>
<tr>
<td>Channel Reach (mm)</td>
<td>2</td>
<td>2</td>
<td>25</td>
<td>$2 5$</td>
</tr>
<tr>
<td>$\begin{array}{} { \text { Die Edge Bandwidth Density } } \\ { \left( G B / s / m m \right) ^ { a } } \end{array}$</td>
<td colspan="4">See Table 1-4</td>
</tr>
<tr>
<td>$\begin{array}{} { \text { Bandwidth area density } } \\ { \left( G B / s / m m ^ { 2 } \right) } \end{array}$ $\left( G B / s / m m ^ { 2 } \right)$</td>
<td>1235</td>
<td>1646</td>
<td>144</td>
<td>$1 9 2$</td>
</tr>
<tr>
<td>$P H Y \quad d i m e n s i o n \quad w i d t h \quad p e r$</td>
<td>388.8</td>
<td>388.8</td>
<td>$6 9 1 . 2 ^ { 6 }$</td>
<td>$6 9 1 . 2 ^ { 8 }$</td>
</tr>
<tr>
<td>PHY dimension Depth (um)ª</td>
<td>1600</td>
<td>1600</td>
<td>1925</td>
<td>1925</td>
</tr>
<tr>
<td>ESDª</td>
<td colspan="4">30-V CDM (Anticipating going to 5-10 V in future.)</td>
</tr>
</table>

a. Parameter definition is the same as in Table 5-2.

b. At data rates > 32 GT/s, only continuous forwarded clock is supported, which results in higher idle power. The impact of
continuous forwarded clock is larger for Standard Packages due to fewer data lanes.

# IMPLEMENTATION NOTE

If an application requires it, the system designer can control the data rate by
adjusting the REFCLK supplied to the PLLs or by adjusting the PLL divider ratio in the
UCIe IP (see Table 5-4 for the range of values). The REFCLK must be stable before
initiating link training. Changes to REFCLK frequency should only be made when the
link is down.

Additionally, the frequency-adjusted REFCLK may be used in place of AUXCLK (see
Section 5.13.2 for AUXCLK details) as the source for the sideband clock. In this
situation, the sideband data rates range from 400 MT/s to 800 MT/s and must be the
same in both directions. Sideband timeouts will be scaled accordingly, ranging from
8 ms at 800 MT/s to 16 ms at 400 MT/s.

Compliance testing will only be conducted at the UCIe data rates specified in the Link
Speed Setting column of Table 5-4, as supported by the UCIe IP.

<table>
<caption>Table 5-4. Operating Data Rate Ranges for UCIe Link Speed Settings</caption>
<tr>
<th rowspan="2">Link Speed Setting</th>
<th colspan="2">Adjusted Operating Speed</th>
</tr>
<tr>
<th>Min</th>
<th>Max</th>
</tr>
<tr>
<td>4 GT/s</td>
<td>2 GT/s</td>
<td>4 GT/s</td>
</tr>
<tr>
<td>8 GT/s</td>
<td>4 GT/s</td>
<td>8 GT/s</td>
</tr>
<tr>
<td>12 GT/s</td>
<td>8 GT/s</td>
<td>12 GT/s</td>
</tr>
<tr>
<td>16 GT/s</td>
<td>12 GT/s</td>
<td>16 GT/s</td>
</tr>
<tr>
<td>24 GT/s</td>
<td>16 GT/s</td>
<td>24 GT/s</td>
</tr>
<tr>
<td>32 GT/s</td>
<td>24 GT/s</td>
<td>32 GT/s</td>
</tr>
<tr>
<td>48 GT/s</td>
<td>32 GT/s</td>
<td>48 GT/s</td>
</tr>
<tr>
<td>64 GT/s</td>
<td>48 GT/s</td>
<td>64 GT/s</td>
</tr>
</table>

## 5.3 Transmitter Specification

The Transmitter topology is shown in Figure 5-4. Each data module consists of N single-ended data
Transmitters plus a Valid signal. N is 68 (64 Data + 4 Redundant Data) for a x64 Advanced Package
Module. N is 34 (32 Data + 2 Redundant Data) for a x32 Advanced Package Module. N is 16 for $a \times 1 6$
Standard Package Module. N is 8 for a x8 Standard Package Module. There is a pair of Transmitters for
clocking and a Track signal in each module. The clock rates and phases are discussed in detail in
Section 5.5.

<figure>
<figcaption>Figure 5-4. Transmitter</figcaption>

$N$

$N$

$D a t a + V a l i d$

Data In

FIFO

Serializer

TXD

0

/N

Phase-1

Deskew

0

PI

TXCK

0

Clock

PLL

DLL

\+

Phase-2

CK

DCC

Buf

fCK

Track

$T X D$

0

</figure>

The Valid signal is used to gate the clock distribution to all data Lanes to enable fast idle exit and
entry. The signal also serves the purpose of Valid framing, see Section 4.1.2 for details. The
Transmitter implementation for Valid signal is expected to be the same as for regular Data.

The Track signal can be used for PHY to compensate for slow-changing variables such as voltage or
temperature. Track is a unidirectional signal similar to a data bit. The UCIe Module sends a clock
pattern (1010 ... ) aligned with Phase-1 of the forwarded clock signal on its Track Transmitter when
requested over the sideband by the UCIe Module Partner for its Track Receiver. See Section 4.6 for
more details on Runtime Recalibration steps and Section 5.5.1 for Track usage.

### 5.3.1 Driver Topology

The Transmitter is optimized for simplicity and low power operation. An example of a low power
Transmitter driver is shown in Figure 5-5. Separate pull-up and pull-down network strengths are
permitted to achieve optimal performance across different channel configurations.

A control loop or training is recommended to adjust output impedance to compensate for the process,
voltage and temperature variations. Control loop and training are implementation specific and beyond
the scope of this specification. In low power states, the implementation must be capable of tri-stating
the output.

It is recommended to optimize the ESD network to minimize pad capacitance. Inductive peaking
technique such as T-coil may be needed at higher data rates.

<figure>
<figcaption>Figure 5-5. Transmitter driver example circuit</figcaption>

VCCIO

$M _ { 1 }$

Pre-
Driver

$R _ { s }$

Data

☒
Pad

$R _ { s }$

ESD
Network

$M _ { 2 }$

Segmented Driver

</figure>

### 5.3.2 Transmitter Electrical parameters

<table>
<caption>Table 5-5 defines the Transmitter electrical parameters. Table 5-5. Transmitter Electrical Parameters (Sheet 1 of 2)</caption>
<tr>
<th>Parameter</th>
<th>Min</th>
<th>Typ</th>
<th>Max</th>
<th>Unit</th>
</tr>
<tr>
<td>Data Lane Tx Swinga</td>
<td>0.4</td>
<td></td>
<td></td>
<td>$V$</td>
</tr>
<tr>
<td>Fwd Clock Tx Swing (single ended)</td>
<td>0.4</td>
<td></td>
<td></td>
<td>V</td>
</tr>
<tr>
<td>Incoming Clock Rise/Fall timeb</td>
<td>0.1</td>
<td>0.22</td>
<td>0.25</td>
<td>UI</td>
</tr>
<tr>
<td>Incoming Differential Clock Overlapb</td>
<td></td>
<td></td>
<td>30</td>
<td>mUI</td>
</tr>
<tr>
<td>Incoming Data Rise/Fall timeb</td>
<td></td>
<td>0.35</td>
<td></td>
<td>UI</td>
</tr>
<tr>
<td>Driver Pull-up/Pull-down Impedance for Advanced Packagec</td>
<td>22</td>
<td>25</td>
<td>28</td>
<td>Ohms</td>
</tr>
<tr>
<td>Impedance Step Size for Advanced Packaged</td>
<td></td>
<td></td>
<td>0.5</td>
<td>Ohms</td>
</tr>
<tr>
<td>Driver Pull-up/Pull-down Impedance for Standard Packagee</td>
<td>27</td>
<td>30</td>
<td>33</td>
<td>Ohms</td>
</tr>
<tr>
<td>Impedance Step Size for Standard Packaged</td>
<td></td>
<td></td>
<td>0.5</td>
<td>Ohms</td>
</tr>
<tr>
<td>1-UI Total Jitterf</td>
<td></td>
<td></td>
<td>96/113</td>
<td>mUI pk-pk at BER</td>
</tr>
<tr>
<td>1-UI Deterministic Jitter (Dual Dirac)9</td>
<td></td>
<td></td>
<td>48</td>
<td>mUI pk-pk</td>
</tr>
<tr>
<td>Tx Data/Clock Differential Jitter (Divergent Path)h</td>
<td></td>
<td></td>
<td>60</td>
<td>mUI pk-pk at BER</td>
</tr>
</table>

<table>
<caption>Table 5-5. Transmitter Electrical Parameters (Sheet 2 of 2)</caption>
<tr>
<th>Parameter</th>
<th>Min</th>
<th>Typ</th>
<th>$M a x$</th>
<th>Unit</th>
</tr>
<tr>
<td>Tx Data/Clock Differential Deterministic Jitter'</td>
<td></td>
<td></td>
<td>30</td>
<td>mUI pk-pk</td>
</tr>
<tr>
<td></td>
<td>-0.02</td>
<td></td>
<td>0.02</td>
<td>UI</td>
</tr>
<tr>
<td>$\begin{array}{} { \text { Duty Cycle Errorj } } \\ { \text { Lane-to-Lane Skew Correction Range \left(up to 16 GT/s\right)^{k } } } \end{array}$</td>
<td>-0.1</td>
<td></td>
<td>0.1</td>
<td>UI</td>
</tr>
<tr>
<td>Lane-to-Lane Skew Correction Range (up to 32 GT/s)k</td>
<td>-0.15</td>
<td></td>
<td>0.15</td>
<td>UI</td>
</tr>
<tr>
<td>Lane-to-Lane Skew Correction Range (up to 64 GT/s)k</td>
<td>-0.18</td>
<td></td>
<td>0.18</td>
<td>UI</td>
</tr>
<tr>
<td>Lane-to-Lane Skew Correction Range (up to 16 GT/s)'</td>
<td>-0.14</td>
<td></td>
<td>0.14</td>
<td>UI</td>
</tr>
<tr>
<td>Lane-to-Lane Skew Correction Range (up to 32 GT/s)!</td>
<td>-0.22</td>
<td></td>
<td>0.22</td>
<td>UI</td>
</tr>
<tr>
<td>Lane-to-Lane Skew Correction Range (up to 64 GT/s)!</td>
<td>-0.5</td>
<td></td>
<td>0.5</td>
<td>$\mathrm { U I }$</td>
</tr>
<tr>
<td>Lane-to-Lane Skewj</td>
<td>-0.02</td>
<td></td>
<td>0.02</td>
<td>$\mathrm { U I }$</td>
</tr>
<tr>
<td>Clock to Mean Data Training Accuracym</td>
<td>-0.07</td>
<td></td>
<td>0.07</td>
<td>$\mathrm { U I }$</td>
</tr>
<tr>
<td>Phase Adjustment Stepn</td>
<td></td>
<td></td>
<td>16</td>
<td>mUI</td>
</tr>
<tr>
<td>Effective Tx Pad Capacitance (32 GT/s capable design)k</td>
<td></td>
<td></td>
<td>250</td>
<td>fF</td>
</tr>
<tr>
<td>Effective Tx Pad Capacitance (64 GT/s capable design)k</td>
<td></td>
<td></td>
<td>180</td>
<td>fF</td>
</tr>
<tr>
<td>Effective Tx Pad Capacitance (8 GT/s capable design)!</td>
<td></td>
<td></td>
<td>300</td>
<td>fF</td>
</tr>
<tr>
<td>Effective Tx Pad Capacitance (16 GT/s capable design)!</td>
<td></td>
<td></td>
<td>200</td>
<td>fF</td>
</tr>
<tr>
<td>Effective Tx Pad Capacitance (&gt; 16 GT/s capable design)'</td>
<td></td>
<td></td>
<td>125</td>
<td>fF</td>
</tr>
<tr>
<td>Tx Driver S11 from DC to Nyquist Frequency! o</td>
<td></td>
<td></td>
<td>-9.5</td>
<td>dB</td>
</tr>
</table>

a. For recommended maximum Transmitter voltage, see Section 1.5.

b. Expected input (informative). Measured 20% to 80%. Differential clock overlap is deviation from the ideal
differential phase (180 degrees apart).

c. Driver pull-up/down impedance is calibrated at midpoint of Transmitter signal swing.

d. Impedance step size is an informative parameter and can be implementation specific to meet Driver pull-up/
pull-down impedance.

e. Driver pull-up/pull-down impedance is calibrated at midpoint of Transmitter signal swing (with nominal $R x$
termination when applicable).

f. 96 mUI for BER 1E-12 and 1E-15. 113 mUI for BER 1E-27.

g. Data dependent jitter excluding Duty Cycle Error.

h. Includes absolute random jitter and untracked deterministic jitter of the divergent path due to $\mathrm { d e l a v }$ mismatch
(in the matched architecture).

i. Untracked deterministic jitter for divergent path. This spec is for > 32 GT/s only.

j. Post correction.

k. Advanced Package.

I. Standard Package.

m. Includes static and tracking error.

n. Informative parameter. Phase adjustment step size must be chosen to meet other timing parameters,
including Clock-to-Mean Data Training Accuracy, Lane-to-Lane skew, and Duty cycle error (if applicable).

o. This is the input reflection coefficient. Transmission effect is much more significant at 48 to 64 GT/s for
UCIe-S. Lumped Cpad may not capture the full effect.

For UCIe-S designs that target a maximum data rate of 64 GT/s, it is recommended to implement a
full-cycle skew correction range (i.e., ±0.5 UI as indicated in Table 5-5). This adjustment

compensates for variations in bump maps because mismatches in bump-to-bump connection length
result in a larger percentage of UI time at higher data rates, thereby enhancing forward-scaling
capability.

The 1-UI Total Jitter, Tx Data/Clock Differential Total Jitter, Duty Cycle Error, Lane-to-Lane Skew, and
Clock to Mean Data Training Accuracy parameters listed in Table 5-5 are recommended target values.
It is permissible to make trade-offs among these individual components, as long as the overall sum of
the listed items does not exceed the specified total.

### 5.3.3 24 GT/s and 32 GT/s Transmitter Equalization

Transmitter equalization is recommended for 16 GT/s and must be supported at 24 GT/s and 32 GT/s
data rates to mitigate the channel ISI impact. Tx equalization is de-emphasis only for all applicable
Data rates.

Tx equalization coefficients for 24 GT/s and 32 GT/s are based on the FIR filter shown in Figure 5-6.
Equalization coefficient is subject to maximum unity swing constraint.

The Transmitter must support the equalization settings shown in Table 5-6. Determination of de-
emphasis setting is based on initial configuration or training sequence, where the value with larger
eye opening will be selected.

<figure>
<figcaption>Figure 5-6. Transmitter de-emphasis</figcaption>

$V _ { i n } \left( n \right)$

$1 \quad U I$

$C _ { 0 }$

$C _ { + 1 }$

$\sum$

$V _ { o u t } \left( n \right)$

$V _ { 0 u t } \left( n \right) = C _ { 0 } V _ { i n } \left( n \right) + C _ { + 1 } V _ { i n } \left( n - 1 \right) + | C _ { + 1 } |$

$$| C _ { 0 } | + | C _ { + 1 } | = 1$$

$V _ { i n } \left( n \right) = \left\{ 0 , + 1 \right)$

</figure>

<figure>
<figcaption>Figure 5-7. Transmitter de-emphasis waveform</figcaption>

$V _ { a }$

$V _ { b }$

$= 2 0 \log _ { 1 0 } \left( V _ { b } / V _ { a } \right)$

</figure>

<table>
<caption>Table 5-6. Transmitter de-emphasis values</caption>
<tr>
<th>Setting</th>
<th>De-emphasis</th>
<th>Accuracy</th>
<th>$\mathrm { C } _ { + 1 }$</th>
<th>$V _ { b } / V _ { a }$</th>
</tr>
<tr>
<td>1</td>
<td>0.0 dB</td>
<td>-</td>
<td>0.000</td>
<td>1.000</td>
</tr>
<tr>
<td>2</td>
<td>-2.2 dB</td>
<td>±0.5 dB</td>
<td>-0.112</td>
<td>0.776</td>
</tr>
</table>

### 5.3.4 48 GT/s and 64 GT/s Transmitter Equalization

Transmitter equalization is required for data rates of 48 GT/s and 64 GT/s. The coefficients for
transmitter equalization are derived from a Finite Impulse Response $\left( F I R \right)$ model, which is illustrated
in Figure 5-8.

<figure>
<figcaption>Figure 5-8. 3-tap Transmitter Equalization (Used at 48 GT/s and 64 GT/s)</figcaption>

$V _ { i n } \left( n \right)$

1.0 UI
delay

1.0 UI
delay

$C _ { - 1 }$
☒

$\mathrm { c } _ { n }$
☒

☒
$C _ { + 1 }$

$\Sigma$

$V _ { o u t } \left( n \right)$

$$V _ { o u t } \left( n \right) = C _ { - 1 } V \left( n \right) + C _ { 0 } V \left( n - 1 \right) + C _ { + 1 } V \left( n - 2 \right) + | C _ { - 1 } | + | C _ { + 1 } |$$
$$| C _ { - 1 } | + | C _ { 0 } | + | C _ { + 1 } | = 1$$
$$V _ { i n } \left( n \right) = \left\{ 0 , 1 \right\}$$

</figure>

The equalization coefficient is constrained by a maximum unity swing limitation. The transmitter is
required to support the equalization presets outlined $i n \quad T a b l e \quad 5 - 7 .$ The selection of the appropriate
preset is based on either the initial configuration or a training sequence, where the value with the
larger eye opening will be chosen. If multiple presets have the same eye opening, the one with the
largest $\mathrm { C } _ { 0 }$ coefficient should be selected. For a detailed explanation of the process, see
Section 4.5.3.4.10.

<table>
<caption>Table 5-7. 48 $G T / s$ and 64 GT/s Tx Equalization Coefficient Presets</caption>
<tr>
<th>Preset #</th>
<th>Preset Encoding</th>
<th>$C - 1$</th>
<th>$C _ { 0 }$</th>
<th>$\mathrm { C } _ { + 1 }$</th>
<th>Accuracy</th>
</tr>
<tr>
<td>PO</td>
<td>0000b</td>
<td>0</td>
<td>1</td>
<td>0</td>
<td>-</td>
</tr>
<tr>
<td>P1</td>
<td>0001b</td>
<td>-0.05</td>
<td>0.95</td>
<td>0</td>
<td>±0.025</td>
</tr>
<tr>
<td>P2</td>
<td>0010b</td>
<td>0</td>
<td>0.9</td>
<td>-0.1</td>
<td>±0.025</td>
</tr>
<tr>
<td>P3</td>
<td>0011b</td>
<td>-0.05</td>
<td>0.85</td>
<td>-0.1</td>
<td>±0.025</td>
</tr>
<tr>
<td>P4</td>
<td>0100b</td>
<td>0</td>
<td>0.8</td>
<td>-0.2</td>
<td>±0.025</td>
</tr>
<tr>
<td>P5</td>
<td>0101b</td>
<td>-0.05</td>
<td>0.75</td>
<td>-0.2</td>
<td>$0 . 0 2 5$</td>
</tr>
</table>

## 5.4 Receiver Specification

The Receiver topology is illustrated in Figure 5-9. Each Module (Advanced Package and Standard
Package) consists of clocks Receivers, data Receivers, and Track Receiver.

The received clock is used to sample the incoming data. The Receiver must match the delays between
the clock path and the data/valid path to the sampler. This is to minimize the impact of power supply
noise induced jitter. The data Receivers may be implemented as 2-way or 4-way interleaved. For
4-way interleaved implementation the Receiver needs to generate required phases internally from the
two phase of the forwarded clock. This may require duty cycle correction capability on the Receiver.
The supported forwarded clock frequencies and phases are described in Section 5.5.

At higher data rates, deskew capability may be needed in the receiver to achieve the matching
requirements between the data Lanes. Receiver Deskew, when applicable, can be performed during
mainband training. More details are provided in Section 4.5.

The UCIe Module, upon requesting the Track signal, receives a clock pattern (1010 ... ) aligned with
Phase-1 of the forwarded clock signal on its Track Receiver from the UCIe Module Partner's Track
Transmitter and may use the Track signal to track the impact of slow varying voltage and temperature
changes on sampling phase.

<figure>
<figcaption>Figure 5-9. Receiver topology</figcaption>

Deskew

Data

Flip-
flop

RXD

FIFO

2/4 Phases

...

Phase-1

Phase
Gen
(Optional)

RXCK

Phase-2

...

Track

RXD

Track

</figure>

### 5.4.1 Receiver Electrical Parameters for $< = 3 2$ GT/s

The specified Receiver electrical parameters for $< = 3 2 \quad G T / s$ are shown in Table 5-8.

<table>
<caption>Table 5-8. Receiver Electrical Parameters for $< = 3 2 \quad G T / s$</caption>
<tr>
<th>Parameter</th>
<th>Min</th>
<th>Typ</th>
<th>Max</th>
<th>Unit</th>
</tr>
<tr>
<td>Rx Input Impedanceª</td>
<td>45</td>
<td>50</td>
<td>55</td>
<td>Ohms</td>
</tr>
<tr>
<td>Impedance Step Sizeª</td>
<td>-</td>
<td>-</td>
<td>1</td>
<td>Ohms</td>
</tr>
<tr>
<td>Data/Clock Total Differential Jitterb c</td>
<td>-</td>
<td>-</td>
<td>60</td>
<td>mUI pk-pk</td>
</tr>
<tr>
<td>Lane-to-Lane skew (up to 16 GT/s)d</td>
<td>-0.07</td>
<td>-</td>
<td>0.07</td>
<td>UI</td>
</tr>
<tr>
<td>Lane-to Lane skew (&gt; 16 GT/s)d</td>
<td>-0.12</td>
<td>-</td>
<td>0.12</td>
<td>UI</td>
</tr>
<tr>
<td>Phase errore (Including Duty cycle error and I/Q mismatch)</td>
<td>-0.04</td>
<td>-</td>
<td>0.04</td>
<td>$\mathrm { U I }$</td>
</tr>
<tr>
<td>Per-Lane deskew adjustment stepf</td>
<td>-</td>
<td>-</td>
<td>16</td>
<td>mUI</td>
</tr>
<tr>
<td>Output Rise Timeg</td>
<td>-</td>
<td>-</td>
<td>0.1</td>
<td>UI</td>
</tr>
<tr>
<td>Output Fall Time9</td>
<td>-</td>
<td>-</td>
<td>0.1</td>
<td>UI</td>
</tr>
<tr>
<td>Rx Pad Capacitanceh</td>
<td>-</td>
<td>-</td>
<td>200</td>
<td>fF</td>
</tr>
<tr>
<td>Rx Pad Capacitance (up to 8 GT/s)ª</td>
<td>-</td>
<td>-</td>
<td>300</td>
<td>fF</td>
</tr>
<tr>
<td>Effective Rx Pad Capacitance (up to 16 GT/s)a</td>
<td>-</td>
<td>-</td>
<td>200</td>
<td>$\mathrm { f F }$</td>
</tr>
<tr>
<td>Effective Rx Pad Capacitance (24 and 32 GT/s)a</td>
<td>-</td>
<td>-</td>
<td>125</td>
<td>$\mathrm { f F }$</td>
</tr>
<tr>
<td>Rx Voltage sensitivity</td>
<td>-</td>
<td>-</td>
<td>40</td>
<td>mV</td>
</tr>
</table>

a. Standard Package mode with termination. Impedance step size is an informative parameter and can be
implementation specific to meet Rx Input Impedance.

b. Based on matched architecture.

c. Includes absolute random jitter and untracked deterministic jitter of the divergent path due to delay mismatch
(in the matched architecture).

d. Require Rx per-Lane deskew if limit is exceeded.

e. Residual error post training and correction.

f. When applicable (informative).

g. Expected output (informative). Measured 20% to 80%.

h. Advanced Package.

### 5.4.2 Receiver Electrical Parameters for 48 GT/s and 64 GT/s

The specified Receiver electrical parameters for 48 GT/s and 64 GT/s are shown in Table 5-9.

<table>
<caption>Table 5-9. Receiver Electrical Parameters for 48 GT/s and 64 GT/s</caption>
<tr>
<th>Parameter</th>
<th>Min</th>
<th>Typ</th>
<th>Max</th>
<th>Unit</th>
</tr>
<tr>
<td>Rx Input Impedanceª</td>
<td>45</td>
<td>50</td>
<td>55</td>
<td>Ohms</td>
</tr>
<tr>
<td>Impedance Step Sizeª</td>
<td></td>
<td></td>
<td>1</td>
<td>Ohms</td>
</tr>
<tr>
<td>Data/Clock Total Differential Jitterb c</td>
<td></td>
<td></td>
<td>60</td>
<td>mUI pk-pk at BER</td>
</tr>
<tr>
<td>Data/Clock Deterministic Differential Jitter</td>
<td></td>
<td></td>
<td>30</td>
<td>mUI pk-pk</td>
</tr>
<tr>
<td>Lane-to Lane skewd</td>
<td>-0.12</td>
<td></td>
<td>0.12</td>
<td>UI</td>
</tr>
<tr>
<td>Phase Errore (including Duty cycle error and I/Q mismatch)</td>
<td>-0.04</td>
<td></td>
<td>0.04</td>
<td>$\mathrm { U I }$</td>
</tr>
<tr>
<td>Per-lane Deskew Adjustment Stepf</td>
<td></td>
<td></td>
<td>16</td>
<td>mUI</td>
</tr>
<tr>
<td>Output Rise Timeg</td>
<td></td>
<td></td>
<td>0.1</td>
<td>UI</td>
</tr>
<tr>
<td>Output Fall Timeg</td>
<td></td>
<td></td>
<td>0.1</td>
<td>UI</td>
</tr>
<tr>
<td>Effective Rx Pad Capacitance for Advanced Packageª</td>
<td></td>
<td></td>
<td>180</td>
<td>fF</td>
</tr>
<tr>
<td>Effective Rx Pad Capacitance for Standard Packageª</td>
<td></td>
<td></td>
<td>125</td>
<td>fF</td>
</tr>
<tr>
<td>Data Rx Voltage Reference Error</td>
<td></td>
<td></td>
<td>5</td>
<td>mV</td>
</tr>
<tr>
<td>Rx Input Referred Noise Spectral Density</td>
<td></td>
<td></td>
<td>4.10E-08</td>
<td>$v ^ { 2 } / G H z$</td>
</tr>
</table>

a. Applies to both Advanced Packages and Standard Packages. Impedance step size is an informative parameter
and can be implementation specific to meet Rx Input Impedance.

b. Based on matched architecture.

c. Includes absolute random jitter and untracked deterministic jitter of the divergent path due to delay mismatch
(in the matched architecture).

d. Require Rx per-Lane deskew if limit is exceeded.

e. Residual error post training and correction.

f. When applicable (informative).

g. Expected output (informative). Measured 20% to 80%.

### 5.4.3 Rx Termination

Receivers on Advanced Package modules must be unterminated up to 32 GT/s, and terminated to
ground for 48 GT/s and 64 GT/s negotiated maximum data rate. The remainder of this section
elaborates on the details of Rx termination for Standard Package modules.

Receiver termination on Standard Package is data rate and channel dependent. Table 5-10 shows the
maximum data rate and channel reach combinations for which the Receivers in Standard Package
Modules are recommended to remain unterminated for a minimally compliant Transmitter.
Figure 5-10 shows an alternate representation of termination requirement. The area below the curve
in Figure 5-10 shows the speed and channel-reach combinations for which the Receivers in Standard
Package Modules are recommended to remain unterminated. Termination is required for all other
combinations. Receivers must be ground-terminated when applicable, as shown in Figure 5-11.

<table>
<caption>Table 5-10. Maximum channel reach for unterminated Receiver $\left( T x \sin g = 0 . 4 V \right)$</caption>
<tr>
<th></th>
<th>Data Rate (GT/s)</th>
<th>Channel Reach (mm)</th>
</tr>
<tr>
<td>12</td>
<td></td>
<td>3</td>
</tr>
<tr>
<td>8</td>
<td></td>
<td>5</td>
</tr>
<tr>
<td>4</td>
<td></td>
<td>10</td>
</tr>
</table>

<figure>
<figcaption>Figure 5-10. Receiver Termination Map for Table 5-10 $\left( T \times S w i n g = 0 . 4 V \right)$</figcaption>

16

14

12

Data Rate (GT/s)

10

8

6

4

2

0

0

5

10

15

20

25

Channel Reach (mm)

</figure>

<figure>
<figcaption>Figure 5-11. Receiver termination</figcaption>

Data

RXD

Clock Phase-1

RXCK

Clock Phase-2

Track

$R X D$

</figure>

For higher Transmitter swing, unterminated Receiver can be extended to longer channel and high data
rate. Table 5-11 shows the maximum data rate and channel reach combinations for Transmitter swing
and 0.85 V (maximum recommended swing). Figure 5-12 shows an alternate representation of
termination requirement. The area below the curve in Figure 5-12 shows the speed and channel reach
combinations for which the Receivers in Standard Package Modules are recommended to remain
unterminated.

<table>
<caption>Table 5-11. Maximum Channel reach for unterminated Receiver $\left( T X \quad s w i n g = 0 . 8 5 V \right)$</caption>
<tr>
<th>$\begin{array}{} { \text { Data Rate } } \\ { \left( G T / s \right) } \end{array}$</th>
<th>Channel Reach (mm)</th>
</tr>
<tr>
<td>16</td>
<td>5</td>
</tr>
<tr>
<td>12</td>
<td>10</td>
</tr>
<tr>
<td>8 and below</td>
<td>All supported Lengths</td>
</tr>
</table>

<figure>
<figcaption>Figure 5-12. Receiver termination map for Table 5-11 $\left( T X \quad S w i n g = 0 . 8 5 \quad V \right)$</figcaption>

32

28

24

Data Rate (GT/s)

20

16

12

8

4

0

0

5

10

15

20

25

30

35

40

Channel Reach (mm)

</figure>

# IMPLEMENTATION NOTE

When the Transmitter is tri-stated and the Receiver is not required to be enabled
(e.g., SBINIT, and some MBINIT states):

· Disabled Receivers must be tolerant of a floating input pad

· Receivers are permitted to enable weak-termination directly on the input pad to
prevent crowbar current in the receiver and to lower noise sensitivity at the
receiver trip point

When the Transmitter is tri-stated and the Receiver is required to be enabled (e.g.,
REPAIRCLK and REPAIRVAL states for Advanced Package):

· Enabled Receivers for (CLKP, CLKN, CLKRD, TRK, VLD, VLDRD) must be tolerant
of a floating input signal on the pad

· Receivers are permitted to enable weak-termination directly on the input pad to
prevent crowbar current in the receiver and to lower noise sensitivity at the
receiver trip point

## 5.4.4 Receiver Equalization > 16 GT/s

Receiver equalization may be implemented at 24 GT/s and 32 GT/s data rates. This enables Link
operation even when TX equalization is not available. Implementation can be CTLE, inductive peaking,
1-tap DFE, or others. Expected RX equalization capability is equivalent of 1st order CTLE. Example
transfer function curves of a first order CTLE are shown in Figure 5-13 and the corresponding
equation is shown below:

$$H \left( s \right) = \mathrm { o } _ { p 2 } \left( \frac { s + A _ { D C } \mathrm { o } _ { p 1 } } { \left( s + \mathrm { o } _ { p 1 } \right) \left( s + \mathrm { o } _ { p 2 } \right) } \right)$$

where, @p2 = 2n*DataRate, $\omega _ { p 1 } = 2 \pi ^ { * } D a t a R a t e / 4 ,$ and $\mathrm { A } _ { \mathrm { D C } }$ is the DC gain.

<figure>
<figcaption>Figure 5-13. Reference Rx CTLE for 24 GT/s</figcaption>

5

0

CTLE Gain (dB)

-5

-10

-15

-20

1.00E+07

$1 . 0 0 E + 0 8$

$1 . 0 0 E + 0 9$

1.00E+10

$1 . 0 0 E + 1 1$

$1 . 0 0 E + 1 2$

Frequency $\left( H z \right)$

</figure>

For data rates of 48 GT/s and 64 GT/s, Rx equalization is required to be utilized in conjunction with $\mathrm { T x }$
equalization to facilitate correct Link operation. The Rx equalization, a reference behavioral model for
channel analysis, adheres to the following design criteria:

· Transfer Function: Simple 1-zero, 2-pole configuration

· Adjustable Parameterized DC Gain: Gain value less than 1, or negative measured in dB

· Consistent Peak Gain: Peak gain is fixed at 0 dB, regardless of the DC gain level

· Nyquist Peak Gain: Peak gain frequency is aligned with the Nyquist frequency, independent of DC
gain adjustments

The Rx equalizer's frequency response is captured by the closed-form equations presented in
Equation 5-1 through Equation $5 - 4 :$

Equation 5-1.

$$H \left( s \right) = \frac { A _ { D C } \omega _ { P } ^ { 2 } } { \omega _ { z } } \frac { s + \omega _ { z } } { \left( s + \omega _ { p } \right) ^ { 2 } }$$

Equation 5-2.

$$\omega _ { n } = 2 \pi f _ { n }$$

