

Equation 5-3.

$$\omega _ { p } = \min \left( \frac { \omega _ { n } } { \sqrt [ 4 ] { 1 - A _ { D c } ^ { 2 } } } , 2 \omega _ { n } \right)$$

Equation 5-4.

$$a _ { z } = a _ { p } \sqrt { \frac { 1 - \sqrt { 1 - A _ { D c } ^ { 2 } } } { 2 } }$$

Apc is the DC gain value. $f _ { n }$ the peak frequency, 24 GHz and 32 GHz, for 48 GT/s and 64 GT/s,
respectively.

It is recommended to provide a minimum of seven CTLE settings to span the DC gain range from
-6 dB to 0 dB, adjustable in 1-dB increments. Figure 5-14 shows the Reference Rx CTLE responses for
64 GT/s.

<figure>
<figcaption>Figure 5-14. Reference Rx CTLE for 64 GT/s</figcaption>

5

0

CTLE Gain (dB)

-5

-10

-15

-20

1.00E+07

1.00E+08

1.00E+09

1.00E+10

1.00E+11

$1 . 0 0 E + 1 2$

Frequency (Hz)

</figure>

Additionally, designers have the option to implement a 1-tap DFE alongside the CTLE, which can
potentially enhance signal integrity at a data rate of 64 GT/s. To maintain control over error
propagation in the DFE, it is recommended that the coefficient ratio h1/h0 be maintained at less than
0.35.

# 5.5 Clocking

Figure 5-15 shows the forwarded clocking architecture. Each module supports a two-phase forwarded
clock. It is critical to maintain matching between all data Lanes and valid signal within the module.
The Receiver must provide matched delays between the Receiver clock distribution and Data/Valid
Receiver path. This is to minimize the impact of power supply noise-induced jitter on Link
performance. Phase adjustment is performed on the Transmitter as shown in Figure 5-15. Link
training is required to set the position of phase adjustment to maximize the Link margin.

At higher data rates, Receiver eye margins may be small and any skew between the data Lanes
(including Valid) may further degrade Link performance. Per-Lane deskew must be supported on the
Transmitter at high data rates.

This specification supports quarter-rate clock frequencies at data rates (24 GT/s and 32 GT/s). The
forwarded clock Transmitter must support quadrature phases in addition to differential clock at these
data rates (to enable either quarter-rate or half-rate Receiver implementations). Table 5-12 shows the
clock frequencies and phases that must be supported at different data rates. Forwarded Clock Phase
is negotiated during Link Initialization and Training (see Section 4.5.3.3.1). At 24 GT/s and 32 GT/s,
Receiver has the options to support differential clock or quadrature clock. The capability register is
defined in Table 9-47, and advertised at the beginning of link negotiation. Note that to achieve
interoperability with designs of lower max data rate, differential clock must always be used at
16 GT/s and below, independent of the choice at 24 GT/s and 32 GT/s.

At data rates of 48 GT/s and 64 GT/s, the forwarded clock operates at a quarter rate and is free-
running. Additionally, in-phase/quadrature (I/Q) training can be conducted during the Rx clock
calibration phase. I/Q training is utilized to fine-tune the relative timing between Phase-1 and
Phase-2 of the forwarded clock. It is recommended that the phase adjustment resolution and range
adhere to Table 5-13 to ensure sufficient precision and coverage. For additional information, see
Section 4.5.3.4.5.

## 5.5.1 Track

Track signal can be used to perform Runtime Recalibration to adjust the Receiver clock path against
slow varying voltage, temperature and transistor aging conditions.

When requested by the UCIe Module, the UCIe Module Partner sends a clock-like pattern that
matches the frequency and is phase-aligned with Phase-1 of the forwarded clock on its Track
Transmitter, as shown in Figure 5-15. The pattern is 1010 ... in the half-rate forwarded clock mode and
1100 ... in the quarter-rate forwarded clock mode.

<figure>
<figcaption>Figure 5-15. Clocking architecture</figcaption>

Die-1

Die-2

Deskew

$D a t a + V a l i d$

Flip-
flop

Data

FIFO

Serializer

TXD

RXD

FIFO

$2 / 4 \quad P h a s e s$

/N

$1 6 x / 6 4 x$

...

Phase-1

Deskew

Clock

$P I$
+
DCC

Phase
Gen

TXCK

RXCK

PLL

DLL

Phase-2

CK

Buf

$f C K$

Track

...

$T X D$

RXD

Phase
Control

Track

</figure>

<table>
<caption>Table 5-12. Forwarded Clock Frequency and Phase</caption>
<tr>
<th>Data rate $\left( G T / s \right)$</th>
<th>Clock freq. (fCK) (GHZ)</th>
<th>Phase-1</th>
<th>Phase-2</th>
<th>Deskew $\left( \mathrm { R e q } / \mathrm { O p t } \right)$</th>
</tr>
<tr>
<td>64</td>
<td>16</td>
<td>45</td>
<td>135</td>
<td>Required</td>
</tr>
<tr>
<td>48</td>
<td>12</td>
<td>45</td>
<td>135</td>
<td>Required</td>
</tr>
<tr>
<td rowspan="2">32</td>
<td>16</td>
<td>90</td>
<td>270</td>
<td>Required</td>
</tr>
<tr>
<td>8</td>
<td>45</td>
<td>135</td>
<td>Required</td>
</tr>
<tr>
<td rowspan="2">24</td>
<td>12</td>
<td>90</td>
<td>270</td>
<td>Required</td>
</tr>
<tr>
<td>6</td>
<td>45</td>
<td>135</td>
<td>Required</td>
</tr>
<tr>
<td>16</td>
<td>8</td>
<td>90</td>
<td>270</td>
<td>Required</td>
</tr>
<tr>
<td>12</td>
<td>6</td>
<td>90</td>
<td>270</td>
<td>Required</td>
</tr>
<tr>
<td>8</td>
<td>4</td>
<td>90</td>
<td>270</td>
<td>Optional</td>
</tr>
<tr>
<td>4</td>
<td>2</td>
<td>90</td>
<td>270</td>
<td>Optional</td>
</tr>
</table>

<table>
<caption>Table 5-13. I/Q Correction for 48 GT/s and 64 GT/s</caption>
<tr>
<th>Parameter</th>
<th>Min</th>
<th>Typ</th>
<th>Max</th>
<th>Unit</th>
</tr>
<tr>
<td>I/Q Correction Step</td>
<td></td>
<td>1/64</td>
<td></td>
<td>$\mathrm { U I }$</td>
</tr>
<tr>
<td rowspan="2">I/Q Correction Range</td>
<td>-12</td>
<td></td>
<td>12</td>
<td>step</td>
</tr>
<tr>
<td>-0.1875</td>
<td></td>
<td>$0 . 1 8 7 5$</td>
<td>$\mathrm { U I }$</td>
</tr>
</table>

### IMPLEMENTATION NOTE

This implementation note provides an example usage for Track signal to calibrate out
slow varying temperature- and voltage-related delay drift between Data and Clock on
the Receiver.

Track uses the same type of Tx driver and Rx receiver as Data (see Figure 5-15). A
clock pattern aligned with Phase-1 of the forwarded clock is sent from Track
Transmitter and received on the Track Receiver. Any initial skew can be calibrated out
during initialization and training (MBTRAIN.RXCLKCAL) on the Receiver side. During
run-time, any drift between Data and the forwarded clock can be detected. One
method for detecting the drift is to sample Track with the forwarded clock. An
implementation-specific number of samples can be collected, averaged if needed, and
used for drift detection. This drift can then be corrected on the forwarded clock
(if needed).

<figure>
<figcaption>Figure 5-16. Track Usage Example</figcaption>

Track and Fwd clock pre initialization

Fwd Clock

Track

Track and Fwd clock post initialization (alignment)

Fwd Clock

Track

Clock drift and correction

Fwd Clock

Track

Fwd Clock
$\left( p o s t \quad c o r r e c t i o n \right)$

</figure>

# 5.6 Supply noise and clock skew

I/O Vcc noise and the clock skew between data modules shall be within the range specified in
Table 5-14.

<table>
<caption>Table 5-14. I/O Noise and Clock Skew</caption>
<tr>
<th>Parameter</th>
<th>Min</th>
<th>Nom</th>
<th>Max</th>
<th>Unit</th>
</tr>
<tr>
<td>I/O Vcc noise for 4 GT/s and 8 GT/sa</td>
<td>-</td>
<td>-</td>
<td>80</td>
<td>mVpp</td>
</tr>
<tr>
<td>$\begin{array}{} { \text { I/O Vcc noise for } 1 2 \text { GT/s^{\circ } } } \\ { \text { I/O Vcc noise for } 1 6 \text { GT/s } } \end{array}$</td>
<td>-</td>
<td>-</td>
<td>50</td>
<td>mVpp</td>
</tr>
<tr>
<td></td>
<td>-</td>
<td>-</td>
<td>40</td>
<td>mVpp</td>
</tr>
<tr>
<td>I/O Vcc noise for 24, 32, 48, and 64 GT/sa</td>
<td>-</td>
<td>-</td>
<td>30</td>
<td>mVpp</td>
</tr>
<tr>
<td>Module to module clock skewb</td>
<td>-</td>
<td>-</td>
<td>60</td>
<td>ps</td>
</tr>
</table>

a. I/O VCC noise includes all noise at the I/O supply bumps relative to VSS bumps. This noise includes all DC and
AC fluctuations at all applicable frequencies.

b. Applies only to multi-module instantiations.

## IMPLEMENTATION NOTE

Due to different micro bump max current capacity and power delivery requirements,
PHY in Advanced Package may have TX providing I/O power supply to RX circuits.

Due to low current draw, sideband supply voltage is strongly recommended to be on
an always-on power domain.

# 5.7 Ball-out and Channel Specification

The UCIe interconnect channel is required to achieve a minimum eye opening that conforms to a
specified eye mask, under channel compliance simulation conditions with noiseless and jitter-less
behavioral Tx and Rx models.

For data rates <= 32 GT/s, the eye mask conforms to a rectangular shape (see Figure 5-17), with the
minimum eye height and width specified in Table 5-15.

<figure>
<figcaption>Figure 5-17. Example Rectangular Eye Mask Diagram for $< = 3 2 \quad G T / s$</figcaption>

Voltage (mV)

-0.8

0

+0.8

Time $\left( U I \right)$

</figure>

<table>
<caption>Table 5-15. Rectangular Eye Mask Requirements for $< = 3 2 \quad G T / s$</caption>
<tr>
<th>Data Rate (GT/s)</th>
<th>$\begin{array}{} { \text { Eye Height } } \\ { \left( m v \right) } \end{array}$</th>
<th>$\begin{array}{} { \text { Eye Width } } \\ { \left( U I \right) } \end{array}$</th>
</tr>
<tr>
<td>4, 8, 12, $1 6 ^ { \circ }$</td>
<td>40</td>
<td>0.75</td>
</tr>
<tr>
<td>24, 32ª b</td>
<td>40</td>
<td>0.65</td>
</tr>
</table>

a. Based on minimum Tx swing specification.

b. With equalization enabled.

At the higher data rates of 48 GT/s and 64 GT/s, the eye mask adopts a diamond shape (see
Figure 5-18). During the channel analysis, the search space for Tx equalization is confined to the
presets outlined in Table 5-7. Concurrently, Rx equalization utilizes a 1st order CTLE, as detailed in
Section 5.4.4, with a DC gain range from -6 dB to 0 dB, adjustable in 1-dB increments. The minimum
eye height and eye width defined for this specification are 65 mV and 0.65 UI, respectively.

<figure>
<figcaption>Figure 5-18. Diamond Eye Mask for 48 GT/s and 64 GT/s</figcaption>

EH

EW

</figure>

## IMPLEMENTATION NOTE

Figure 5-19 shows an example circuit setup that can be used to generate the eye
diagrams shown in Figure 5-17 and Figure 5-18. $\mathrm { R } _ { \mathrm { T X } }$ is the Transmitter impedance
and RRx represents the Receiver termination. $\mathrm { C } _ { \mathrm { T X } }$ and $\mathrm { C } _ { \mathrm { R X } }$ represent effective
Transmitter and Receiver capacitance, respectively. For crosstalk, the 19-largest
aggressors need to be included. At data rates of 24 GT/s and above, the
corresponding Transmitter and Receiver equalization are enabled.

The eye diagram was generated using a two-step process.

1\. Generate ISI and XTALK channel step response using circuit setup shown in
Figure 5-19.

2\. Use the generated channel response in a signal-integrity or channel-simulation
tool to generate a statistical eye diagram (see Figure 5-17).

Other equivalent methods may be used, depending on the signal-integrity or channel-
simulation tool.

<figure>
<figcaption>Figure 5-19. Example Eye Simulation Setup</figcaption>

Tx Model

Interconnect

Rx Model

$R _ { T X }$

CTX

$R _ { R X } \sum _ { T = 1 } ^ { T }$

$\mathrm { C } _ { R X }$

Agg # N

$V _ { 0 \_ a g g N }$

RTX

:

Victim

Vo_vic

\+

$\mathrm { C } _ { \mathrm { T Y } }$

:

CRX

$R _ { R X }$

Agg # 1

o_agg1

$c _ { m }$

$\mathrm { R } _ { \mathrm { T X } }$

$| \mathrm { C } _ { R X }$

$\mathrm { R } _ { \mathrm { R X } }$

</figure>

The Tx Lane-to-Lane Skew Correction Range is the range that the Tx can compensate for interconnect
channel mismatches and Rx lane-to-lane delay variations (within the specified limits). Therefore, the
difference between Tx Lane-to-Lane Skew Correction Range in Section 5.3.2 and the Rx Lane-to-Lane
Skew in Section 5.4.1 and Section 5.4.2 represents interconnect channel-matching tolerance. The
tolerance defined with respect to the center of distribution across Lanes is quantified in Table 5-16.
The maximum-allowable mismatch between any two Lanes is constrained by the tolerance span listed
in the table.

Additionally, the deskew circuit in the Tx can be used to correct Tx clock distribution skew. In this
scenario, the combined correction range for Tx, Rx, and channel mismatches depends on the Tx
design implementation; however, the combined correction range must exceed the specified Tx Lane-
to-Lane Skew Correction Range value listed in Table 5-5.

<table>
<caption>Table 5-16. Channel Matching Tolerance of Tx or Rx within a Module</caption>
<tr>
<th colspan="2">Channel Matching Tolerance</th>
<th rowspan="2">Min</th>
<th rowspan="2">Max</th>
<th rowspan="2">Tolerance Span</th>
<th rowspan="2">Unit</th>
</tr>
<tr>
<th>Package Type</th>
<th>Data Rate</th>
</tr>
<tr>
<td rowspan="2">Advanced</td>
<td>4 to 32 GT/s</td>
<td>-0.03</td>
<td>0.03</td>
<td>0.06</td>
<td>UI</td>
</tr>
<tr>
<td>48 and 64 GT/s</td>
<td>-0.06</td>
<td>0.06</td>
<td>0.12</td>
<td>UI</td>
</tr>
<tr>
<td rowspan="3">Standard</td>
<td>4 to 16 GT/s</td>
<td>-0.07</td>
<td>0.07</td>
<td>0.14</td>
<td>UI</td>
</tr>
<tr>
<td>$2 4 \quad a n d \quad 3 2 \quad G T / s$</td>
<td>-0.10</td>
<td>0.10</td>
<td>0.20</td>
<td>UI</td>
</tr>
<tr>
<td>48 and 64 GT/s</td>
<td>-0.20</td>
<td>0.20</td>
<td>0.40</td>
<td>UI</td>
</tr>
</table>

### 5.7.1 Voltage Transfer Function

Voltage Transfer Function (VTF) based metrics are used to define insertion loss and crosstalk. VTF
metrics incorporate both resistive and capacitive components of $T x$ and Rx terminations. Figure 5-20
shows the circuit diagram for VTF calculations.

<figure>
<figcaption>Figure 5-20. Circuit for VTF calculation</figcaption>

$\mathrm { V } _ { \mathrm { s } }$

$\mathrm { R } _ { \mathrm { t x } }$

interconnect

$\mathrm { V } _ { \mathrm { r } }$

Victim

$\mathrm { C } _ { \mathrm { t } }$

$C _ { x }$

$R _ { f x }$

$R _ { x }$

interconnect

$V _ { a 1 }$

Aggressor1

$C _ { 0 x }$

$C _ { x x }$

$\mathrm { R } _ { _ { \mathrm { f X } } }$

$R _ { x }$

interconnect

$V _ { a }$

Aggressor2

$\mathrm { C } _ { \mathrm { x } }$

$C _ { x x }$

$R _ { n }$

$R _ { t x }$

interconnect

$V _ { a 1 9 }$

Aggressor19

$\mathrm { C } _ { \mathrm { t x } }$

$c _ { n } = \frac { 1 } { T }$

</figure>

VTF loss is defined as the ratio of the Receiver voltage and the Source voltage, as shown in
Equation 5-5 and Equation 5-6.

# Equation $5 - 5 .$

$$L \left( f \right) = 2 0 \log 1 0 | \frac { V _ { r } \left( f \right) } { V _ { s } \left( f \right) } |$$

Equation 5-6.

$$L \left( 0 \right) = 2 0 \log 1 0 \left( \frac { R _ { r x } } { R _ { t x } + R _ { c h a n n e l } + R _ { r x } } \right)$$

L(f) is the frequency dependent loss and L(0) is the $D C \quad l o s s .$ For unterminated channel, $L \left( 0 \right)$ is
effectively 0.

VTF crosstalk is defined as the power sum of the ratios of the aggressor Receiver voltage to the
source voltage. 19 aggressors are included in the calculation. Based on crosstalk reciprocity,
VTF crosstalk can be expressed as shown in Equation 5-7.

Equation $5 - 7 .$

$$X T \left( f \right) = 1 0 \log 1 0 \left( \sum _ { i = 1 } ^ { 1 9 } | \frac { V _ { a i } \left( f \right) } { V _ { s } \left( f \right) } | ^ { 2 } \right)$$

## 5.7.2 Advanced Package

<table>
<caption>Table 5-17. Channel Characteristics</caption>
<tr>
<th>Data Rate</th>
<th>4-16 GT/s</th>
<th>$2 4 , 3 2 \quad G T / s$</th>
</tr>
<tr>
<td>VTF Loss (dB)</td>
<td>$L \left( f _ { N } \right) > - 3$</td>
<td>$L \left( f _ { N } \right) > - 5$</td>
</tr>
<tr>
<td>VTF Crosstalk (dB)ª</td>
<td>XT(fN) &lt; 1.5 L(fN) - 21.5 and XT(fN) &lt; - 23</td>
<td>XT(fN) &lt; 1.5 L(fN) - 19 and $X T \left( f _ { N } \right) < - 2 4$</td>
</tr>
</table>

a. Based on Voltage Transfer Function Method (Tx: 25 ohm / 0.25 pF; Rx: 0.2 pF).

$f _ { N }$ is the Nyquist frequency. The equations in the table form a segmented line in the loss-crosstalk
coordinate plane, defining the pass/fail region.

<table>
<caption>Table 5-18. x64 Advanced Package Module Signal List (Sheet 1 of 2)ª</caption>
<tr>
<th>Signal Name</th>
<th>Count</th>
<th>Description</th>
</tr>
<tr>
<td colspan="3">Data</td>
</tr>
<tr>
<td>TXDATA [ 63 : 0]</td>
<td>64</td>
<td>Transmit Data</td>
</tr>
<tr>
<td>TXVLD</td>
<td>1</td>
<td>Transmit Data Valid; Enables clocking in corresponding module</td>
</tr>
<tr>
<td>TXTRK</td>
<td>1</td>
<td>Transmit Track signal</td>
</tr>
<tr>
<td>TXCKP</td>
<td>1</td>
<td>Transmit Clock Phase-1</td>
</tr>
<tr>
<td>TXCKN</td>
<td>1</td>
<td>Transmit Clock Phase-2</td>
</tr>
<tr>
<td>TXCKRD</td>
<td>1</td>
<td>Redundant for Clock and Track Lane repair</td>
</tr>
<tr>
<td>TXDATARD [ 3 : 0]</td>
<td>4</td>
<td>Redundant for Data Lane repair</td>
</tr>
<tr>
<td>TXVLDRD</td>
<td>1</td>
<td>Redundant for Valid</td>
</tr>
<tr>
<td>RXDATA [ 63 : 0]</td>
<td>64</td>
<td>Receive Data</td>
</tr>
</table>

<table>
<caption>Table 5-18. x64 Advanced Package Module Signal List (Sheet 2 of 2)ª</caption>
<tr>
<th>Signal Name</th>
<th>Count</th>
<th>Description</th>
</tr>
<tr>
<td>RXVLD</td>
<td>1</td>
<td>Receive Data Valid; Enables clocking in corresponding module</td>
</tr>
<tr>
<td>RXTRK</td>
<td>1</td>
<td>Receive Track.</td>
</tr>
<tr>
<td>RXCKP</td>
<td>1</td>
<td>Receive Clock Phase-1</td>
</tr>
<tr>
<td>RXCKN</td>
<td>1</td>
<td>Receive Clock Phase-2</td>
</tr>
<tr>
<td>RXDATARD [3 : 0]</td>
<td>4</td>
<td>Redundant for Data Lane repair</td>
</tr>
<tr>
<td>RXCKRD</td>
<td>1</td>
<td>Redundant for Clock Lane repair</td>
</tr>
<tr>
<td>RXVLDRD</td>
<td>1</td>
<td>Redundant for Valid</td>
</tr>
<tr>
<td colspan="3">Sideband</td>
</tr>
<tr>
<td>TXDATASB</td>
<td>1</td>
<td>$S i d e b a n d \quad T r a n s m i t \quad D a t a$</td>
</tr>
<tr>
<td>RXDATASB</td>
<td>1</td>
<td>$S i d e b a n d$ Receiver Data</td>
</tr>
<tr>
<td>TXCKSB</td>
<td>1</td>
<td>Sideband Transmit Clock</td>
</tr>
<tr>
<td>RXCKSB</td>
<td>1</td>
<td>Sideband Receive Clock</td>
</tr>
<tr>
<td>TXDATASBRD</td>
<td>1</td>
<td>Redundant Sideband Transmit Data</td>
</tr>
<tr>
<td>RXDATASBRD</td>
<td>1</td>
<td>Redundant Sideband Receiver Data</td>
</tr>
<tr>
<td>TXCKSBRD</td>
<td>1</td>
<td>Redundant Sideband Transmit Clock</td>
</tr>
<tr>
<td>RXCKSBRD</td>
<td>1</td>
<td>Redundant Sideband Receive Clock</td>
</tr>
<tr>
<td colspan="3">Power and Voltage</td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>Ground Reference</td>
</tr>
<tr>
<td>VCCIO</td>
<td></td>
<td>I/O supply</td>
</tr>
<tr>
<td>VCCFWDIO</td>
<td></td>
<td>Forwarded power supply from remote Transmitter supply to local Receiver AFE (see Tightly Coupled mode in Section 5.8)</td>
</tr>
<tr>
<td>VCCAON</td>
<td></td>
<td>Always on Aux supply (sideband)</td>
</tr>
</table>

a. For x32 Advanced Package module, the TXDATA [ 63 : 32], TXRD $\left[ 3 : 2 \right] ,$ RXDATA [ 63 : 32], and RXRD [ 3 : 2]
signals do not apply. All other signals are the same as the x64 Advanced Package Module signals.

### 5.7.2.1 Loss and Crosstalk Mask

Loss and crosstalk are specified by a mask defined by the $L \left( f _ { N } \right)$ and $X T \left( f _ { N } \right)$ at Nyquist frequency. It is
a linear mask from DC to $f _ { N }$ for loss and flat mask for crosstalk, illustrated by Figure 5-21. Loss from
DC to $f _ { N }$ needs to be above the spec line. Crosstalk from DC to $f _ { N }$ needs to be below the spec line. The
green line in Figure 5-21 is a representative passing signal.

<figure>
<figcaption>Figure 5-21. Loss and Crosstalk Mask</figcaption>

Loss Spec

Crosstalk Spec

$f _ { N }$

Freq (GHz)

$f _ { \lambda }$

Freq (GHz)

0

0

$L \left( 0 \right)$

$L \left( f _ { N } \right)$

$X T \left( f _ { N } \right)$

</figure>

### 5.7.2.2 x64 Advanced Package Module Bump Map

All bump matrices in this section and hereinafter are defined with "dead bug" view which means the
viewer is looking directly at the UCIe micro bumps facing up, with the die flipped like a "dead bug" as
illustrated in Figure 5-22.

<figure>
<figcaption>Figure 5-22. Viewer Orientation Looking at the Defined UCIe Bump Matrix</figcaption>
</figure>

Figure 5-23, Figure 5-24, and Figure 5-25 show the reference bump matrix for the 10-column, 16-
column, and 8-column x64 Advanced Package Modules, respectively. The lower left corner of the
bump map will be considered "origin" of a bump matrix and the leftmost column is Column 0.

It is strongly recommended to follow the bump matrices provided in Figure 5-23, Figure 5-24, and
Figure 5-25 for x64 Advanced Package interfaces.

The 10-column bump matrix is optimal for bump pitch range of 38 to 50 um. To achieve optimal area
scaling with different bump pitches, the optional 16-column and 8-column bump matrices are defined
for bump ranges of 25 to 37 um and 51 to 55 um, respectively, which will result in optimal Module
depth while maintaining Module width of 388.8 um, as shown in Figure 5-24 and Figure 5-25,
respectively.

The following rule must be followed for the 10-column x64 Advanced Package bump matrix:

· The signal order within a column must be preserved. For example, Column 0 must contain the
signals: txdataRD0, txdata0, txdata1, txdata2, txdata3, txdata4, ... , rxdata59,
rxdata60, rxdata61, rxdata62, rxdata63, rxdataRD3, and txdatasbRD. Similarly, 16-
column and 8-column x64 Advanced Packages must preserve the signal order within a column of
the respective bump matrices.

It is strongly recommended to follow the supply and ground pattern shown in the bump matrices. It
must be ensured that sufficient supply and ground bumps are provided to meet channel
characteristics (FEXT and NEXT) and power-delivery requirements.

The following rules must be followed when instantiating multiple modules of Advanced Package bump
matrix:

· Modules must be stepped in the same orientation and abutted.

· Horizontal or vertical mirroring is not permitted.

· Module stacking is not permitted.

Additionally, in multi-module instantiations it is strongly recommended to add one column of vss
bumps on each outside edge of the multi-module instantiation.

Mirror die implementation may necessitate a jog or additional metal layers for proper connectivity.

<table>
<caption>Figure 5-23. 10-column x64 Advanced Package Bump Map for $< = 3 2 \quad G T / s$</caption>
<tr>
<th></th>
<th>Column0</th>
<th>Column1</th>
<th>Column2</th>
<th>Column3</th>
<th>Column4</th>
<th>Column5</th>
<th>$C o l u m n 6$</th>
<th>Column7</th>
<th>Column8</th>
<th>Column9</th>
</tr>
<tr>
<td rowspan="5"></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td></td>
<td>rxcksbRD</td>
<td></td>
<td>rxcksb</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdatasb</td>
<td></td>
<td>rxdatasbRD</td>
</tr>
<tr>
<td>txdatasbRD</td>
<td></td>
<td>txdatasb</td>
<td></td>
<td>vccio</td>
<td></td>
<td>txcksb</td>
<td></td>
<td>txcksbRD</td>
<td></td>
</tr>
<tr>
<td rowspan="6"></td>
<td></td>
<td>rxdata50</td>
<td></td>
<td>rxdata35</td>
<td></td>
<td>rxdata29</td>
<td></td>
<td>rxdata14</td>
<td></td>
<td>rxdataRD0</td>
</tr>
<tr>
<td>rxdataRD3</td>
<td></td>
<td>rxdata49</td>
<td></td>
<td>rxdata34</td>
<td></td>
<td>rxdata28</td>
<td></td>
<td>rxdata13</td>
<td></td>
</tr>
<tr>
<td></td>
<td>rxdata51</td>
<td></td>
<td>rxdata36</td>
<td></td>
<td>rxdata30</td>
<td></td>
<td>rxdata15</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>rxdata63</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdata33</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdata12</td>
<td></td>
</tr>
<tr>
<td></td>
<td>rxdata52</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata31</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata0</td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>rxdata48</td>
<td></td>
<td>rxdata32</td>
<td></td>
<td>rxdata27</td>
<td></td>
<td>rxdata11</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>rxdata53</td>
<td></td>
<td>rxdata37</td>
<td></td>
<td>rxdataRD1</td>
<td></td>
<td>rxdata16</td>
<td></td>
<td>rxdata1</td>
</tr>
<tr>
<td></td>
<td>rxdata62</td>
<td></td>
<td>rxdata47</td>
<td></td>
<td>rxdataRD2</td>
<td></td>
<td>rxdata26</td>
<td></td>
<td>rxdata10</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>rxdata54</td>
<td></td>
<td>rxdata38</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata17</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td></td>
<td>rxdata61</td>
<td></td>
<td>rxdata46</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdata25</td>
<td></td>
<td>rxdata9</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>rxdata55</td>
<td></td>
<td>rxdata39</td>
<td></td>
<td>rxckRD</td>
<td></td>
<td>rxdata18</td>
<td></td>
<td>rxdata2</td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata45</td>
<td></td>
<td>rxvldRD</td>
<td></td>
<td>rxdata24</td>
<td></td>
<td>rxdata8</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>rxdata56</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxckn</td>
<td></td>
<td>rxdata19</td>
<td></td>
<td>rxdata3</td>
</tr>
<tr>
<td></td>
<td>rxdata60</td>
<td></td>
<td>rxdata44</td>
<td></td>
<td>rxvld</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata7</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>rxdata57</td>
<td></td>
<td>rxdata40</td>
<td></td>
<td>rxckp</td>
<td></td>
<td>rxdata20</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td></td>
<td>rxdata59</td>
<td></td>
<td>rxdata43</td>
<td></td>
<td>rxtrk</td>
<td></td>
<td>rxdata23</td>
<td></td>
<td>rxdata6</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>rxdata58</td>
<td></td>
<td>rxdata41</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata21</td>
<td></td>
<td>rxdata4</td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata42</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdata22</td>
<td></td>
<td>rxdata5</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
</tr>
<tr>
<td></td>
<td>vccio</td>
<td></td>
<td>txdata21</td>
<td></td>
<td>vccio</td>
<td></td>
<td>txdata41</td>
<td></td>
<td>txdata58</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata5</td>
<td></td>
<td>txdata22</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata42</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td></td>
<td>txdata4</td>
<td></td>
<td>txdata20</td>
<td></td>
<td>txckp</td>
<td></td>
<td>txdata40</td>
<td></td>
<td>txdata57</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata6</td>
<td></td>
<td>txdata23</td>
<td></td>
<td>txtrk</td>
<td></td>
<td>txdata43</td>
<td></td>
<td>txdata59</td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata19</td>
<td></td>
<td>txckn</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata56</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata7</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txvld</td>
<td></td>
<td>txdata44</td>
<td></td>
<td>txdata60</td>
</tr>
<tr>
<td></td>
<td>txdata3</td>
<td></td>
<td>txdata18</td>
<td></td>
<td>txckRD</td>
<td></td>
<td>txdata39</td>
<td></td>
<td>txdata55</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata8</td>
<td></td>
<td>txdata24</td>
<td></td>
<td>txvldRD</td>
<td></td>
<td>txdata45</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td></td>
<td>txdata2</td>
<td></td>
<td>txdata17</td>
<td></td>
<td>vccio</td>
<td></td>
<td>txdata38</td>
<td></td>
<td>txdata54</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata9</td>
<td></td>
<td>txdata25</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata46</td>
<td></td>
<td>txdata61</td>
</tr>
<tr>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata10</td>
<td></td>
<td>txdata26</td>
<td></td>
<td>txdataRD2</td>
<td></td>
<td>txdata47</td>
<td></td>
<td>txdata62</td>
</tr>
<tr>
<td></td>
<td>txdata1</td>
<td></td>
<td>txdata16</td>
<td></td>
<td>txdataRD1</td>
<td></td>
<td>txdata37</td>
<td></td>
<td>txdata53</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata11</td>
<td></td>
<td>txdata27</td>
<td></td>
<td>txdata32</td>
<td></td>
<td>txdata48</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td></td>
<td>txdata0</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata31</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata52</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata12</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata33</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata63</td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata15</td>
<td></td>
<td>txdata30</td>
<td></td>
<td>txdata36</td>
<td></td>
<td>txdata51</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata13</td>
<td></td>
<td>txdata28</td>
<td></td>
<td>txdata34</td>
<td></td>
<td>txdata49</td>
<td></td>
<td>txdataRD3</td>
</tr>
<tr>
<td></td>
<td>txdataRD0</td>
<td></td>
<td>txdata14</td>
<td></td>
<td>txdata29</td>
<td></td>
<td>txdata35</td>
<td></td>
<td>txdata50</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
</tr>
<tr>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
</tr>
</table>

Die Edge

Note:
In Figure 5-23, at 45-um pitch, the module depth of the 10-column reference bump
matrix as shown is approximately 1043 um.

<table>
<caption>Figure 5-24. 16-column x64 Advanced Package Bump Map for $< = 3 2 \quad G T / s$</caption>
<tr>
<th></th>
<th>Column0</th>
<th>Column1</th>
<th>Column2</th>
<th>Column3</th>
<th>Column4</th>
<th>Column5</th>
<th>Column6</th>
<th>Column7</th>
<th>Column8</th>
<th>Column9</th>
<th>Column10</th>
<th>Column11</th>
<th>Column12</th>
<th>Column13</th>
<th>Column14</th>
<th>Column15</th>
</tr>
<tr>
<td></td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxcksbRD</td>
<td></td>
<td>rxcksb</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdatasb</td>
<td></td>
<td>rxdatasbRD</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>txdatasbRD</td>
<td></td>
<td>txdatasb</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txcksb</td>
<td></td>
<td>txcksbRD</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>rxdata54</td>
<td></td>
<td>rxdata50</td>
<td></td>
<td>rxdata35</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata29</td>
<td></td>
<td>rxdata 14</td>
<td></td>
<td>rxdata11</td>
<td></td>
<td>rxdataRD0</td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata52</td>
<td></td>
<td>rxdata49</td>
<td></td>
<td>rxdata34</td>
<td></td>
<td>rxdataRD1</td>
<td></td>
<td>rxdata28</td>
<td></td>
<td>rxdata13</td>
<td></td>
<td>rxdata9</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>rxdata55</td>
<td></td>
<td>rxdata51</td>
<td></td>
<td>rxdata36</td>
<td></td>
<td>rxdataRD2</td>
<td></td>
<td>rxdata30</td>
<td></td>
<td>rxdata 15</td>
<td></td>
<td>rxdata 10</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td></td>
<td>rxdataRD3</td>
<td></td>
<td>rxdata53</td>
<td></td>
<td>rxdata48</td>
<td></td>
<td>rxdata33</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata27</td>
<td></td>
<td>rxdata 12</td>
<td></td>
<td>rxdata8</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>rxdata 61</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata37</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata31</td>
<td></td>
<td>rxdata16</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata0</td>
</tr>
<tr>
<td></td>
<td>rxdata63</td>
<td></td>
<td>rxdata56</td>
<td></td>
<td>rxdata47</td>
<td></td>
<td>rxdata32</td>
<td></td>
<td>rxckRD</td>
<td></td>
<td>rxdata26</td>
<td></td>
<td>rxdata 17</td>
<td></td>
<td>rxdata2</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>rxdata60</td>
<td></td>
<td>rxdata46</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxvldRD</td>
<td></td>
<td>rxdata25</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata7</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata57</td>
<td></td>
<td>rxdata43</td>
<td></td>
<td>rxdata38</td>
<td></td>
<td>rxckn</td>
<td></td>
<td>rxdata23</td>
<td></td>
<td>rxdata18</td>
<td></td>
<td>rxdata3</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>rxdata59</td>
<td></td>
<td>rxdata45</td>
<td></td>
<td>rxdata40</td>
<td></td>
<td>rxvld</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata20</td>
<td></td>
<td>rxdata6</td>
<td></td>
<td>rxdata1</td>
</tr>
<tr>
<td></td>
<td>rxdata62</td>
<td></td>
<td>rxdata58</td>
<td></td>
<td>rxdata42</td>
<td></td>
<td>rxdata39</td>
<td></td>
<td>rxckp</td>
<td></td>
<td>rxdata22</td>
<td></td>
<td>rxdata19</td>
<td></td>
<td>rxdata4</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata44</td>
<td></td>
<td>rxdata41</td>
<td></td>
<td>rxtrk</td>
<td></td>
<td>rxdata24</td>
<td></td>
<td>rxdata21</td>
<td></td>
<td>rxdata5</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata5</td>
<td></td>
<td>txdata21</td>
<td></td>
<td>txdata24</td>
<td></td>
<td>txtrk</td>
<td></td>
<td>txdata41</td>
<td></td>
<td>txdata44</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata4</td>
<td></td>
<td>txdata19</td>
<td></td>
<td>txdata22</td>
<td></td>
<td>txckp</td>
<td></td>
<td>txdata39</td>
<td></td>
<td>txdata42</td>
<td></td>
<td>txdata58</td>
<td></td>
<td>txdata62</td>
</tr>
<tr>
<td></td>
<td>txdata1</td>
<td></td>
<td>txdata6</td>
<td></td>
<td>txdata20</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txvld</td>
<td></td>
<td>txdata40</td>
<td></td>
<td>txdata45</td>
<td></td>
<td>txdata59</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata3</td>
<td></td>
<td>txdata18</td>
<td></td>
<td>txdata23</td>
<td></td>
<td>txckn</td>
<td></td>
<td>txdata38</td>
<td></td>
<td>txdata43</td>
<td></td>
<td>txdata57</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata7</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata25</td>
<td></td>
<td>txvldRD</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata46</td>
<td></td>
<td>txdata60</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata2</td>
<td></td>
<td>txdata17</td>
<td></td>
<td>txdata26</td>
<td></td>
<td>txckRD</td>
<td></td>
<td>txdata32</td>
<td></td>
<td>txdata47</td>
<td></td>
<td>txdata56</td>
<td></td>
<td>txdata63</td>
</tr>
<tr>
<td></td>
<td>txdata0</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata16</td>
<td></td>
<td>txdata31</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata37</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata61</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata8</td>
<td></td>
<td>txdata12</td>
<td></td>
<td>txdata27</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata33</td>
<td></td>
<td>txdata48</td>
<td></td>
<td>txdata53</td>
<td></td>
<td>txdataRD3</td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata10</td>
<td></td>
<td>txdata15</td>
<td></td>
<td>txdata30</td>
<td></td>
<td>txdataRD2</td>
<td></td>
<td>txdata36</td>
<td></td>
<td>txdata51</td>
<td></td>
<td>txdata55</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata9</td>
<td></td>
<td>txdata13</td>
<td></td>
<td>txdata28</td>
<td></td>
<td>txdataRD1</td>
<td></td>
<td>txdata34</td>
<td></td>
<td>txdata49</td>
<td></td>
<td>txdata52</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td></td>
<td>txdataRD0</td>
<td></td>
<td>txdata11</td>
<td></td>
<td>txdata14</td>
<td></td>
<td>txdata29</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata35</td>
<td></td>
<td>txdata50</td>
<td></td>
<td>txdata54</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
</tr>
<tr>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
</tr>
</table>

Die Edge

Note:
In Figure $5 - 2 4 ,$ at 25-um pitch, the module width of the 16-column reference bump
matrix as shown is approximately 388.8 um.

<table>
<caption>Figure 5-25. 8-column x64 Advanced Package Bump Map for $< = 3 2 \quad G T / s$</caption>
<tr>
<th></th>
<th>Column0</th>
<th>Column1</th>
<th>Column2</th>
<th>Column3</th>
<th>Column4</th>
<th>Column5</th>
<th>$\mathrm { c o l u m n 6 }$</th>
<th>Column7</th>
</tr>
<tr>
<td rowspan="39"></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td></td>
<td>rxcksbRD</td>
<td></td>
<td>rxcksb</td>
<td></td>
<td>rxdatasb</td>
<td></td>
<td>rxdatasbRD</td>
</tr>
<tr>
<td>txdatasbRD</td>
<td></td>
<td>txdatasb</td>
<td></td>
<td>txcksb</td>
<td></td>
<td>txcksbRD</td>
<td></td>
</tr>
<tr>
<td></td>
<td>rxdata50</td>
<td></td>
<td>rxdata36</td>
<td></td>
<td>rxdata14</td>
<td></td>
<td>rxdataRD0</td>
</tr>
<tr>
<td>rxdataRD3</td>
<td></td>
<td>rxdata49</td>
<td></td>
<td>rxdata27</td>
<td></td>
<td>rxdata13</td>
<td></td>
</tr>
<tr>
<td></td>
<td>rxdata51</td>
<td></td>
<td>rxdata35</td>
<td></td>
<td>rxdata15</td>
<td></td>
<td>rxdata0</td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>rxdata48</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata12</td>
<td></td>
</tr>
<tr>
<td></td>
<td>rxdata52</td>
<td></td>
<td>rxdata34</td>
<td></td>
<td>rxdata16</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>rxdata63</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata28</td>
<td></td>
<td>rxdata11</td>
<td></td>
</tr>
<tr>
<td></td>
<td>rxdata53</td>
<td></td>
<td>rxdata33</td>
<td></td>
<td>rxdata17</td>
<td></td>
<td>rxdata1</td>
</tr>
<tr>
<td>rxdata62</td>
<td></td>
<td>rxdata47</td>
<td></td>
<td>rxdata29</td>
<td></td>
<td>rxdata10</td>
<td></td>
</tr>
<tr>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
</tr>
<tr>
<td>rxdata61</td>
<td></td>
<td>rxdata46</td>
<td></td>
<td>rxdata30</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata26</td>
<td></td>
<td>rxdata2</td>
</tr>
<tr>
<td>rxdata60</td>
<td></td>
<td>rxdata37</td>
<td></td>
<td>rxdata31</td>
<td></td>
<td>rxdata9</td>
<td></td>
</tr>
<tr>
<td></td>
<td>rxdata54</td>
<td></td>
<td>rxdata32</td>
<td></td>
<td>rxdata25</td>
<td></td>
<td>rxdata3</td>
</tr>
<tr>
<td>rxdata59</td>
<td></td>
<td>rxdata38</td>
<td></td>
<td>rxdataRD1</td>
<td></td>
<td>rxdata8</td>
<td></td>
</tr>
<tr>
<td></td>
<td>rxdata55</td>
<td></td>
<td>rxdataRD2</td>
<td></td>
<td>rxdata24</td>
<td></td>
<td>rxdata4</td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>rxdata39</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td></td>
<td>rxdata45</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata23</td>
<td></td>
<td>rxdata7</td>
</tr>
<tr>
<td>rxdata56</td>
<td></td>
<td>rxdata40</td>
<td></td>
<td>rxckRD</td>
<td></td>
<td>rxdata18</td>
<td></td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>rxvldRD</td>
<td></td>
<td>rxdata22</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>rxdata57</td>
<td></td>
<td>rxdata41</td>
<td></td>
<td>rxckn</td>
<td></td>
<td>rxdata19</td>
<td></td>
</tr>
<tr>
<td></td>
<td>rxdata44</td>
<td></td>
<td>rxvld</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata6</td>
</tr>
<tr>
<td>rxdata58</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxckp</td>
<td></td>
<td>rxdata20</td>
<td></td>
</tr>
<tr>
<td></td>
<td>rxdata43</td>
<td></td>
<td>rxtrk</td>
<td></td>
<td>rxdata21</td>
<td></td>
<td>rxdata5</td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>rxdata42</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
</tr>
<tr>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata42</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>txdata5</td>
<td></td>
<td>txdata21</td>
<td></td>
<td>txtrk</td>
<td></td>
<td>txdata43</td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata20</td>
<td></td>
<td>txckp</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata58</td>
</tr>
<tr>
<td>txdata6</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txvld</td>
<td></td>
<td>txdata44</td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata19</td>
<td></td>
<td>txckn</td>
<td></td>
<td>txdata41</td>
<td></td>
<td>txdata57</td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>txdata22</td>
<td></td>
<td>txvldRD</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata18</td>
<td></td>
<td>txckRD</td>
<td></td>
<td>txdata40</td>
<td></td>
<td>txdata56</td>
</tr>
<tr>
<td>txdata7</td>
<td></td>
<td>txdata23</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata45</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata39</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td></td>
<td>txdata4</td>
<td></td>
<td>txdata24</td>
<td></td>
<td>txdataRD2</td>
<td></td>
<td>txdata55</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata8</td>
<td></td>
<td>txdataRD1</td>
<td></td>
<td>txdata38</td>
<td></td>
<td>txdata59</td>
</tr>
<tr>
<td rowspan="2"></td>
<td>txdata3</td>
<td></td>
<td>txdata25</td>
<td></td>
<td>txdata32</td>
<td></td>
<td>txdata54</td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata9</td>
<td></td>
<td>txdata31</td>
<td></td>
<td>txdata37</td>
<td></td>
<td>txdata60</td>
</tr>
<tr>
<td rowspan="2"></td>
<td>txdata2</td>
<td></td>
<td>txdata26</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata30</td>
<td></td>
<td>txdata46</td>
<td></td>
<td>txdata61</td>
</tr>
<tr>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata10</td>
<td></td>
<td>txdata29</td>
<td></td>
<td>txdata47</td>
<td></td>
<td>txdata62</td>
</tr>
<tr>
<td rowspan="5"></td>
<td>txdata1</td>
<td></td>
<td>txdata17</td>
<td></td>
<td>txdata33</td>
<td></td>
<td>txdata53</td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata11</td>
<td></td>
<td>txdata28</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata63</td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>txdata16</td>
<td></td>
<td>txdata34</td>
<td></td>
<td>txdata52</td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata12</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata48</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>txdata0</td>
<td></td>
<td>txdata15</td>
<td></td>
<td>txdata35</td>
<td></td>
<td>txdata51</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata13</td>
<td></td>
<td>txdata27</td>
<td></td>
<td>txdata49</td>
<td></td>
<td>txdataRD3</td>
</tr>
<tr>
<td></td>
<td>txdataRD0</td>
<td></td>
<td>txdata14</td>
<td></td>
<td>txdata36</td>
<td></td>
<td>txdata50</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
</tr>
<tr>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td colspan="3">Die Edge</td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td colspan="3"></td>
<td></td>
<td></td>
<td></td>
</tr>
</table>

Note:
In Figure 5-25, at 55-um pitch, the module depth of the 8-column reference bump
matrix as shown is approximately 1,585 um.

<table>
<caption>Figure 5-26 shows the signal exit order for the 10-column x64 Advanced Package bump map. Figure 5-26. 10-column x64 Advanced Package Bump map: Signal exit order</caption>
<tr>
<th colspan="20"></th>
</tr>
<tr>
<th rowspan="12"></th>
<th rowspan="6">Tx Breakout</th>
<th>Left to Right</th>
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
<th></th>
<th>txdataRD0</th>
<th>txdata0</th>
<th>txdata1</th>
<th>txdata2</th>
<th>txdata3</th>
<th>txdata4</th>
<th>txdata5</th>
<th>txdata6</th>
<th>txdata7</th>
<th>txdata8</th>
<th>txdata9</th>
<th>txdata10</th>
<th>txdata11</th>
<th>txdata12</th>
<th>txdata13</th>
<th>Cont ...</th>
<th rowspan="11"></th>
</tr>
<tr>
<td>Cont ...</td>
<td>txdata14</td>
<td>txdata15</td>
<td>txdata16</td>
<td>txdata17</td>
<td>txdata18</td>
<td>txdata19</td>
<td>txdata20</td>
<td>txdata21</td>
<td>txdata22</td>
<td>txdata23</td>
<td>txdata24</td>
<td>txdata25</td>
<td>txdata26</td>
<td>txdata27</td>
<td>txdata28</td>
<td>Cont1 ...</td>
</tr>
<tr>
<td>Cont1 ...</td>
<td>txdata29</td>
<td>txdata30</td>
<td>txdata31</td>
<td>txdataRD1</td>
<td>txckRD</td>
<td>txckn</td>
<td>txckp</td>
<td>txtrk</td>
<td>txvld</td>
<td>txvldRD</td>
<td>txdataRD2</td>
<td>txdata32</td>
<td>txdata33</td>
<td>txdata34</td>
<td>txdata35</td>
<td>Cont2 ...</td>
</tr>
<tr>
<td>Cont2 ...</td>
<td>txdata36</td>
<td>txdata37</td>
<td>txdata38</td>
<td>txdata39</td>
<td>txdata40</td>
<td>txdata41</td>
<td>txdata42</td>
<td>txdata43</td>
<td>txdata44</td>
<td>txdata45</td>
<td>txdata46</td>
<td>txdata47</td>
<td>txdata48</td>
<td>txdata49</td>
<td>txdata50</td>
<td>Cont3 ...</td>
</tr>
<tr>
<td>Cont3 ...</td>
<td>txdata51</td>
<td>txdata52</td>
<td>txdata53</td>
<td>txdata54</td>
<td>txdata55</td>
<td>txdata56</td>
<td>txdata57</td>
<td>txdata58</td>
<td>txdata59</td>
<td>txdata60</td>
<td>txdata61</td>
<td>txdata62</td>
<td>txdata63</td>
<td>txdataRD3</td>
<td></td>
<td></td>
</tr>
<tr>
<td rowspan="6">Rx Breakout</td>
<td>Left to Right</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
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
<td>rxdataRD3</td>
<td>rxdata63</td>
<td>rxdata62</td>
<td>rxdata61</td>
<td>rxdata60</td>
<td>rxdata59</td>
<td>rxdata58</td>
<td>rxdata57</td>
<td>rxdata56</td>
<td>rxdata55</td>
<td>rxdata54</td>
<td>rxdata53</td>
<td>rxdata52</td>
<td>rxdata51</td>
<td>rxdata50</td>
<td>Cont ...</td>
</tr>
<tr>
<td>Cont ...</td>
<td>rxdata49</td>
<td>rxdata48</td>
<td>rxdata47</td>
<td>rxdata46</td>
<td>rxdata45</td>
<td>rxdata44</td>
<td>rxdata43</td>
<td>rxdata42</td>
<td>rxdata41</td>
<td>rxdata40</td>
<td>rxdata39</td>
<td>rxdata38</td>
<td>rxdata37</td>
<td>rxdata36</td>
<td>rxdata35</td>
<td>Cont1 ...</td>
</tr>
<tr>
<td>Cont1 ...</td>
<td>rxdata34</td>
<td>rxdata33</td>
<td>rxdata32</td>
<td>rxdataRD2</td>
<td>rxvldRD</td>
<td>rxvld</td>
<td>rxtrk</td>
<td>rxckp</td>
<td>rxckn</td>
<td>rxckRD</td>
<td>rxdataRD1</td>
<td>rxdata31</td>
<td>rxdata30</td>
<td>rxdata29</td>
<td>rxdata28</td>
<td>Cont2 ...</td>
</tr>
<tr>
<td>Cont2 ...</td>
<td>rxdata27</td>
<td>rxdata26</td>
<td>rxdata25</td>
<td>rxdata24</td>
<td>rxdata23</td>
<td>rxdata22</td>
<td>rxdata21</td>
<td>rxdata20</td>
<td>rxdata19</td>
<td>rxdata18</td>
<td>rxdata17</td>
<td>rxdata16</td>
<td>rxdata15</td>
<td>rxdata14</td>
<td>rxdata13</td>
<td>Cont3 ...</td>
</tr>
<tr>
<td>Cont3 ...</td>
<td>rxdata12</td>
<td>rxdata11</td>
<td>rxdata10</td>
<td>rxdata9</td>
<td>rxdata8</td>
<td>rxdata7</td>
<td>rxdata6</td>
<td>rxdata5</td>
<td>rxdata4</td>
<td>rxdata3</td>
<td>rxdata2</td>
<td>rxdata1</td>
<td>rxdata0</td>
<td>rxdataRD0</td>
<td></td>
<td></td>
</tr>
</table>

#### IMPLEMENTATION NOTE

##### High-speed Considerations for x64 Bump Maps

Three reference bump maps in Figure 5-23, Figure 5-24, and Figure 5-25 are recommended for
different ranges of bump pitch, while PHY implementations have the flexibility to adjust the power
and ground bumps to meet channel characteristics and power delivery requirements, which largely
depend on the target speed and the advanced packaging technology capabilities.

At higher speeds, the PHY circuits draw larger current through the bumps and require better signal
and power integrity of the packaging solution. This typically requires adding power and ground
bumps and optimizing the distribution of them, but the implementation also needs to minimize the
lane-to-lane length skew and preserve the assignment and relative order of the signals in each
column to comply with the bump matrix rules in Section 5.7.2.2.

<table>
<caption>Table 5-19. Bump Map Options and the Recommended Bump Pitch Range and Corresponding Max Speed</caption>
<tr>
<th>Bump Map</th>
<th>Bump Pitch (um)</th>
<th>Max Speed $\left( \mathrm { G T } / \mathrm { s } \right)$</th>
</tr>
<tr>
<td rowspan="2">16 column</td>
<td>25-30</td>
<td>12</td>
</tr>
<tr>
<td>31-37</td>
<td>16</td>
</tr>
<tr>
<td rowspan="2">10 column</td>
<td>38-44</td>
<td>24</td>
</tr>
<tr>
<td>45-50</td>
<td>32</td>
</tr>
<tr>
<td>8 column</td>
<td>51-55</td>
<td>32</td>
</tr>
</table>

This Implementation Note is formulated to provide PHY implementations a set of reference x64
bump maps to encompass the max speed specified. Table 5-19 summarizes the corresponding max
speed for these bump map options and their recommended bump pitch ranges.

Bump maps in Figure 5-27, Figure 5-28, and Figure 5-29 are the x64 implementation references for
the corresponding max speed with an enhancement of the power and ground bumps. They all
comply with the bump matrix rules in Section 5.7.2.2, and they maintain the backward compatibility
in terms of signal exit order. These reference examples have been optimized for signal integrity,
power integrity, lane-to-lane skew, electro-migration stress and bump area based on most of the
advanced packaging technologies in the industry. Please note that technology requirements vary,
and it is still required to verify the bump map with the technology provider for actual implementation
requirements and performance targets.

# IMPLEMENTATION NOTE

## Continued

<table>
<caption>$F i g u r e \quad 5 - 2 7 .$ Enhanced 10-column x64 Advanced Package Bump Map Example for 32 GT/s Implementation</caption>
<tr>
<th></th>
<th>1</th>
<th>2</th>
<th>3</th>
<th>4</th>
<th>5</th>
<th>6</th>
<th>7</th>
<th>8</th>
<th>9</th>
<th>10</th>
</tr>
<tr>
<td>1</td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td>2</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>3</td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td>4</td>
<td></td>
<td>rxcksbRD</td>
<td></td>
<td>rxcksb</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdatasb</td>
<td></td>
<td>rxdatasbRD</td>
</tr>
<tr>
<td>5</td>
<td>txdatasbRD</td>
<td></td>
<td>txdatasb</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txcksb</td>
<td></td>
<td>txcksbRD</td>
<td></td>
</tr>
<tr>
<td>6</td>
<td></td>
<td>rxdata50</td>
<td></td>
<td>rxdata35</td>
<td></td>
<td>rxdata29</td>
<td></td>
<td>rxdata14</td>
<td></td>
<td>rxdataRD0</td>
</tr>
<tr>
<td>7</td>
<td>rxdataRD3</td>
<td></td>
<td>rxdata49</td>
<td></td>
<td>rxdata34</td>
<td></td>
<td>rxdata28</td>
<td></td>
<td>rxdata13</td>
<td></td>
</tr>
<tr>
<td>8</td>
<td></td>
<td>rxdata51</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
</tr>
<tr>
<td>9</td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata33</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata12</td>
<td></td>
</tr>
<tr>
<td>10</td>
<td></td>
<td>rxdata52</td>
<td></td>
<td>rxdata36</td>
<td></td>
<td>rxdata30</td>
<td></td>
<td>rxdata15</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>11</td>
<td>VSS</td>
<td></td>
<td>rxdata48</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata27</td>
<td></td>
<td>rxdata11</td>
<td></td>
</tr>
<tr>
<td>12</td>
<td></td>
<td>rxdata53</td>
<td></td>
<td>rxdata37</td>
<td></td>
<td>rxdata31</td>
<td></td>
<td>rxdata16</td>
<td></td>
<td>rxdata0</td>
</tr>
<tr>
<td>13</td>
<td>rxdata63</td>
<td></td>
<td>rxdata47</td>
<td></td>
<td>rxdata32</td>
<td></td>
<td>rxdata26</td>
<td></td>
<td>rxdata10</td>
<td></td>
</tr>
<tr>
<td>14</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
</tr>
<tr>
<td>15</td>
<td>rxdata62</td>
<td></td>
<td>rxdata46</td>
<td></td>
<td>rxdataRD2</td>
<td></td>
<td>rxdata25</td>
<td></td>
<td>rxdata9</td>
<td></td>
</tr>
<tr>
<td>16</td>
<td></td>
<td>rxdata54</td>
<td></td>
<td>rxdata38</td>
<td></td>
<td>rxdataRD1</td>
<td></td>
<td>rxdata17</td>
<td></td>
<td>rxdata1</td>
</tr>
<tr>
<td>17</td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td>18</td>
<td></td>
<td>rxdata55</td>
<td></td>
<td>rxdata39</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdata18</td>
<td></td>
<td>rxdata2</td>
</tr>
<tr>
<td>19</td>
<td>rxdata61</td>
<td></td>
<td>rxdata45</td>
<td></td>
<td>rxvldRD</td>
<td></td>
<td>rxdata24</td>
<td></td>
<td>rxdata8</td>
<td></td>
</tr>
<tr>
<td>20</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
</tr>
<tr>
<td>21</td>
<td>rxdata60</td>
<td></td>
<td>rxdata44</td>
<td></td>
<td>rxvld</td>
<td></td>
<td>rxdata23</td>
<td></td>
<td>rxdata7</td>
<td></td>
</tr>
<tr>
<td>22</td>
<td></td>
<td>rxdata56</td>
<td></td>
<td>rxdata40</td>
<td></td>
<td>rxckRD</td>
<td></td>
<td>rxdata19</td>
<td></td>
<td>rxdata3</td>
</tr>
<tr>
<td>23</td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td>24</td>
<td></td>
<td>rxdata57</td>
<td></td>
<td>rxdata41</td>
<td></td>
<td>rxckn</td>
<td></td>
<td>rxdata20</td>
<td></td>
<td>rxdata4</td>
</tr>
<tr>
<td>25</td>
<td>rxdata59</td>
<td></td>
<td>rxdata43</td>
<td></td>
<td>rxtrk</td>
<td></td>
<td>rxdata22</td>
<td></td>
<td>rxdata6</td>
<td></td>
</tr>
<tr>
<td>26</td>
<td></td>
<td>rxdata58</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxckp</td>
<td></td>
<td>rxdata21</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>27</td>
<td>VSS</td>
<td></td>
<td>rxdata42</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata5</td>
<td></td>
</tr>
<tr>
<td>28</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
</tr>
<tr>
<td>29</td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td>30</td>
<td></td>
<td>txdata5</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>txdata42</td>
<td></td>
<td>vccio</td>
</tr>
<tr>
<td>31</td>
<td>vccio</td>
<td></td>
<td>txdata21</td>
<td></td>
<td>txckp</td>
<td></td>
<td>vccio</td>
<td></td>
<td>txdata58</td>
<td></td>
</tr>
<tr>
<td>32</td>
<td></td>
<td>txdata6</td>
<td></td>
<td>txdata22</td>
<td></td>
<td>txtrk</td>
<td></td>
<td>txdata43</td>
<td></td>
<td>txdata59</td>
</tr>
<tr>
<td>33</td>
<td>txdata4</td>
<td></td>
<td>txdata20</td>
<td></td>
<td>txckn</td>
<td></td>
<td>txdata41</td>
<td></td>
<td>txdata57</td>
<td></td>
</tr>
<tr>
<td>34</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
</tr>
<tr>
<td>35</td>
<td>txdata3</td>
<td></td>
<td>txdata19</td>
<td></td>
<td>txckRD</td>
<td></td>
<td>txdata40</td>
<td></td>
<td>txdata56</td>
<td></td>
</tr>
<tr>
<td>36</td>
<td></td>
<td>txdata7</td>
<td></td>
<td>txdata23</td>
<td></td>
<td>txvld</td>
<td></td>
<td>txdata44</td>
<td></td>
<td>txdata60</td>
</tr>
<tr>
<td>37</td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td>38</td>
<td></td>
<td>txdata8</td>
<td></td>
<td>txdata24</td>
<td></td>
<td>txvldRD</td>
<td></td>
<td>txdata45</td>
<td></td>
<td>txdata61</td>
</tr>
<tr>
<td>39</td>
<td>txdata2</td>
<td></td>
<td>txdata18</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata39</td>
<td></td>
<td>txdata55</td>
<td></td>
</tr>
<tr>
<td>40</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
</tr>
<tr>
<td>41</td>
<td>txdata1</td>
<td></td>
<td>txdata17</td>
<td></td>
<td>txdataRD1</td>
<td></td>
<td>txdata38</td>
<td></td>
<td>txdata54</td>
<td></td>
</tr>
<tr>
<td>42</td>
<td></td>
<td>txdata9</td>
<td></td>
<td>txdata25</td>
<td></td>
<td>txdataRD2</td>
<td></td>
<td>txdata46</td>
<td></td>
<td>txdata62</td>
</tr>
<tr>
<td>43</td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td>44</td>
<td></td>
<td>txdata10</td>
<td></td>
<td>txdata26</td>
<td></td>
<td>txdata32</td>
<td></td>
<td>txdata47</td>
<td></td>
<td>txdata63</td>
</tr>
<tr>
<td>45</td>
<td>txdata0</td>
<td></td>
<td>txdata16</td>
<td></td>
<td>txdata31</td>
<td></td>
<td>txdata37</td>
<td></td>
<td>txdata53</td>
<td></td>
</tr>
<tr>
<td>46</td>
<td></td>
<td>txdata11</td>
<td></td>
<td>txdata27</td>
<td></td>
<td>vccio</td>
<td></td>
<td>txdata48</td>
<td></td>
<td>vccio</td>
</tr>
<tr>
<td>47</td>
<td>vccio</td>
<td></td>
<td>txdata15</td>
<td></td>
<td>txdata30</td>
<td></td>
<td>txdata36</td>
<td></td>
<td>txdata52</td>
<td></td>
</tr>
<tr>
<td>48</td>
<td></td>
<td>txdata12</td>
<td></td>
<td>vccio</td>
<td></td>
<td>txdata33</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>49</td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata51</td>
<td></td>
</tr>
<tr>
<td>50</td>
<td></td>
<td>txdata13</td>
<td></td>
<td>txdata28</td>
<td></td>
<td>txdata34</td>
<td></td>
<td>txdata49</td>
<td></td>
<td>txdataRD3</td>
</tr>
<tr>
<td>51</td>
<td>txdataRD0</td>
<td></td>
<td>txdata14</td>
<td></td>
<td>txdata29</td>
<td></td>
<td>txdata35</td>
<td></td>
<td>txdata50</td>
<td></td>
</tr>
<tr>
<td>52</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
</tr>
<tr>
<td>53</td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
</tr>
<tr>
<td></td>
<td colspan="2"></td>
<td></td>
<td></td>
<td colspan="3">Die Edge</td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td colspan="10"></td>
<td></td>
</tr>
</table>

Note:
In Figure 5-27, at 45-um pitch, the module depth of the 10-column bump map as
shown is approximately 1225 um. Rows 1, 2, and 53 are required for packaging
solutions using floating bridges without through-silicon vias (TSVs). They can be
optional for packaging solutions with TSVs.

# IMPLEMENTATION NOTE

## Continued

<table>
<caption>Figure 5-28. Enhanced 16-column x64 Advanced Package Bump Map Example for 16 GT/s Implementation</caption>
<tr>
<th></th>
<th>1</th>
<th>2</th>
<th>3</th>
<th>4</th>
<th>5</th>
<th>6</th>
<th>7</th>
<th>8</th>
<th>9</th>
<th>10</th>
<th>11</th>
<th>12</th>
<th>13</th>
<th>14</th>
<th>15</th>
<th>16</th>
</tr>
<tr>
<td>1</td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td>2</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>3</td>
<td>txdatasbRD</td>
<td></td>
<td>rxcksbRD</td>
<td></td>
<td>txdatasb</td>
<td></td>
<td>rxcksb</td>
<td></td>
<td>txcksb</td>
<td></td>
<td>rxdatasb</td>
<td></td>
<td>txcksbRD</td>
<td></td>
<td>$r x d a t a s b R D$</td>
<td></td>
</tr>
<tr>
<td>4</td>
<td></td>
<td>rxdata54</td>
<td></td>
<td>rxdata50</td>
<td></td>
<td>rxdata35</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata29</td>
<td></td>
<td>rxdata14</td>
<td></td>
<td>rxdata11</td>
<td></td>
<td>rxdataRD0</td>
</tr>
<tr>
<td>5</td>
<td>rxdataRD3</td>
<td></td>
<td>rxdata52</td>
<td></td>
<td>rxdata49</td>
<td></td>
<td>rxdata34</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata28</td>
<td></td>
<td>rxdata13</td>
<td></td>
<td>rxdata9</td>
<td></td>
</tr>
<tr>
<td>6</td>
<td></td>
<td>rxdata55</td>
<td></td>
<td>rxdata51</td>
<td></td>
<td>rxdata36</td>
<td></td>
<td>rxdataRD2</td>
<td></td>
<td>rxdata30</td>
<td></td>
<td>rxdata15</td>
<td></td>
<td>rxdata10</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>7</td>
<td>VSS</td>
<td></td>
<td>rxdata53</td>
<td></td>
<td>rxdata48</td>
<td></td>
<td>rxdata33</td>
<td></td>
<td>rxdataRD1</td>
<td></td>
<td>rxdata27</td>
<td></td>
<td>rxdata12</td>
<td></td>
<td>rxdata8</td>
<td></td>
</tr>
<tr>
<td>8</td>
<td></td>
<td>rxdata61</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata37</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata31</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata7</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>9</td>
<td>rxdata63</td>
<td></td>
<td>rxdata56</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata32</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata26</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata2</td>
<td></td>
</tr>
<tr>
<td>10</td>
<td></td>
<td>vccio</td>
<td></td>
<td>$r x d a t a 4 6$</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxvldRD</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdata16</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdata0</td>
</tr>
<tr>
<td>11</td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdata47</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxckRD</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdata17</td>
<td></td>
<td>vccio</td>
<td></td>
</tr>
<tr>
<td>12</td>
<td></td>
<td>rxdata60</td>
<td></td>
<td>rxdata45</td>
<td></td>
<td>rxdata40</td>
<td></td>
<td>rxvld</td>
<td></td>
<td>rxdata25</td>
<td></td>
<td>rxdata20</td>
<td></td>
<td>rxdata6</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>13</td>
<td>rxdata62</td>
<td></td>
<td>rxdata57</td>
<td></td>
<td>rxdata43</td>
<td></td>
<td>rxdata38</td>
<td></td>
<td>rxckn</td>
<td></td>
<td>rxdata23</td>
<td></td>
<td>rxdata 18</td>
<td></td>
<td>rxdata3</td>
<td></td>
</tr>
<tr>
<td>14</td>
<td></td>
<td>rxdata59</td>
<td></td>
<td>rxdata44</td>
<td></td>
<td>rxdata41</td>
<td></td>
<td>rxtrk</td>
<td></td>
<td>rxdata24</td>
<td></td>
<td>rxdata21</td>
<td></td>
<td>rxdata5</td>
<td></td>
<td>rxdata1</td>
</tr>
<tr>
<td>15</td>
<td>VSS</td>
<td></td>
<td>rxdata58</td>
<td></td>
<td>rxdata42</td>
<td></td>
<td>rxdata39</td>
<td></td>
<td>rxckp</td>
<td></td>
<td>rxdata22</td>
<td></td>
<td>rxdata 19</td>
<td></td>
<td>rxdata4</td>
<td></td>
</tr>
<tr>
<td>16</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>17</td>
<td>VSS</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccfwdio</td>
<td></td>
</tr>
<tr>
<td>18</td>
<td></td>
<td>txdata4</td>
<td></td>
<td>txdata19</td>
<td></td>
<td>txdata22</td>
<td></td>
<td>txckp</td>
<td></td>
<td>txdata39</td>
<td></td>
<td>txdata42</td>
<td></td>
<td>txdata58</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>19</td>
<td>txdata1</td>
<td></td>
<td>txdata5</td>
<td></td>
<td>txdata21</td>
<td></td>
<td>txdata24</td>
<td></td>
<td>$t x t r k$</td>
<td></td>
<td>txdata41</td>
<td></td>
<td>txdata44</td>
<td></td>
<td>txdata59</td>
<td></td>
</tr>
<tr>
<td>20</td>
<td></td>
<td>txdata3</td>
<td></td>
<td>txdata18</td>
<td></td>
<td>txdata23</td>
<td></td>
<td>txckn</td>
<td></td>
<td>txdata38</td>
<td></td>
<td>txdata43</td>
<td></td>
<td>txdata57</td>
<td></td>
<td>txdata62</td>
</tr>
<tr>
<td>21</td>
<td>VSS</td>
<td></td>
<td>txdata6</td>
<td></td>
<td>txdata20</td>
<td></td>
<td>txdata25</td>
<td></td>
<td>txvld</td>
<td></td>
<td>txdata40</td>
<td></td>
<td>txdata45</td>
<td></td>
<td>txdata60</td>
<td></td>
</tr>
<tr>
<td>22</td>
<td></td>
<td>vccio</td>
<td></td>
<td>txdata17</td>
<td></td>
<td>vccio</td>
<td></td>
<td>txckRD</td>
<td></td>
<td>vccio</td>
<td></td>
<td>txdata47</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>23</td>
<td>txdata0</td>
<td></td>
<td>vccio</td>
<td></td>
<td>txdata16</td>
<td></td>
<td>vccio</td>
<td></td>
<td>txvldRD</td>
<td></td>
<td>vccio</td>
<td></td>
<td>txdata46</td>
<td></td>
<td>vccio</td>
<td></td>
</tr>
<tr>
<td>24</td>
<td></td>
<td>txdata2</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata26</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata32</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata56</td>
<td></td>
<td>txdata63</td>
</tr>
<tr>
<td>25</td>
<td>VSS</td>
<td></td>
<td>txdata7</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata31</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata37</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata61</td>
<td></td>
</tr>
<tr>
<td>26</td>
<td></td>
<td>txdata8</td>
<td></td>
<td>txdata12</td>
<td></td>
<td>txdata27</td>
<td></td>
<td>txdataRD1</td>
<td></td>
<td>txdata33</td>
<td></td>
<td>txdata48</td>
<td></td>
<td>txdata53</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>27</td>
<td>VSS</td>
<td></td>
<td>txdata10</td>
<td></td>
<td>txdata15</td>
<td></td>
<td>txdata30</td>
<td></td>
<td>txdataRD2</td>
<td></td>
<td>txdata36</td>
<td></td>
<td>txdata51</td>
<td></td>
<td>txdata55</td>
<td></td>
</tr>
<tr>
<td>28</td>
<td></td>
<td>txdata9</td>
<td></td>
<td>txdata13</td>
<td></td>
<td>txdata28</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata34</td>
<td></td>
<td>txdata49</td>
<td></td>
<td>txdata52</td>
<td></td>
<td>txdataRD3</td>
</tr>
<tr>
<td>29</td>
<td>txdataRD0</td>
<td></td>
<td>txdata11</td>
<td></td>
<td>txdata14</td>
<td></td>
<td>txdata29</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata35</td>
<td></td>
<td>txdata50</td>
<td></td>
<td>txdata54</td>
<td></td>
</tr>
<tr>
<td>30</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
</tr>
<tr>
<td>31</td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
</tr>
<tr>
<td colspan="17">Die Edge</td>
</tr>
</table>

Note:
In Figure 5-28, at 25-um pitch, the module depth of the 16-column bump map as
shown is approximately 400 um. Rows 1 and 31 are required for packaging solutions
using floating bridges without TSVs. They can be optional for packaging solutions
with TSVs.

# IMPLEMENTATION NOTE

## Continued

Figure 5-29.

<figure>
<figcaption>Enhanced 8-column x64 Advanced Package Bump Map Example for 32 GT/s Implementation</figcaption>
</figure>

<table>
<tr>
<th></th>
<th>1</th>
<th>2</th>
<th>3</th>
<th>4</th>
<th>5</th>
<th>6</th>
<th>7</th>
<th>8</th>
</tr>
<tr>
<th>1</th>
<th>VSS</th>
<th></th>
<th>vccio</th>
<th></th>
<th>vccio</th>
<th></th>
<th>VSS</th>
<th></th>
</tr>
<tr>
<td>2</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>3</td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td>4</td>
<td></td>
<td>rxcksbRD</td>
<td></td>
<td>rxcksb</td>
<td></td>
<td>rxdatasb</td>
<td></td>
<td>rxdatasbRD</td>
</tr>
<tr>
<td>5</td>
<td>txdatasbRD</td>
<td></td>
<td>txdatasb</td>
<td></td>
<td>txcksb</td>
<td></td>
<td>txcksbRD</td>
<td></td>
</tr>
<tr>
<td>6</td>
<td></td>
<td>rxdata50</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata14</td>
<td></td>
<td>rxdataRD0</td>
</tr>
<tr>
<td>7</td>
<td>$r x d a t a R D 3$</td>
<td></td>
<td>rxdata49</td>
<td></td>
<td>rxdata27</td>
<td></td>
<td>rxdata13</td>
<td></td>
</tr>
<tr>
<td>8</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdata36</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
</tr>
<tr>
<td>9</td>
<td>rxdata63</td>
<td></td>
<td>rxdata48</td>
<td></td>
<td>rxdata28</td>
<td></td>
<td>rxdata12</td>
<td></td>
</tr>
<tr>
<td>10</td>
<td></td>
<td>$r x d a t a 5 1$</td>
<td></td>
<td>rxdata35</td>
<td></td>
<td>rxdata15</td>
<td></td>
<td>rxdata0</td>
</tr>
<tr>
<td>11</td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td>12</td>
<td></td>
<td>rxdata52</td>
<td></td>
<td>rxdata34</td>
<td></td>
<td>$r x d a t a 1 6$</td>
<td></td>
<td>rxdata1</td>
</tr>
<tr>
<td>13</td>
<td>$r x d a t a 6 2$</td>
<td></td>
<td>$r x d a t a 4 7$</td>
<td></td>
<td>rxdata29</td>
<td></td>
<td>rxdata11</td>
<td></td>
</tr>
<tr>
<td>14</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
</tr>
<tr>
<td>15</td>
<td>rxdata61</td>
<td></td>
<td>rxdata46</td>
<td></td>
<td>rxdata30</td>
<td></td>
<td>rxdata10</td>
<td></td>
</tr>
<tr>
<td>16</td>
<td></td>
<td>rxdata53</td>
<td></td>
<td>rxdata33</td>
<td></td>
<td>rxdata17</td>
<td></td>
<td>rxdata2</td>
</tr>
<tr>
<td>17</td>
<td>rxdata60</td>
<td></td>
<td>rxdata37</td>
<td></td>
<td>rxdata31</td>
<td></td>
<td>rxdata9</td>
<td></td>
</tr>
<tr>
<td>18</td>
<td></td>
<td>rxdata54</td>
<td></td>
<td>rxdata32</td>
<td></td>
<td>rxdata26</td>
<td></td>
<td>rxdata3</td>
</tr>
<tr>
<td>19</td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td>20</td>
<td></td>
<td>rxdata55</td>
<td></td>
<td>rxdataRD2</td>
<td></td>
<td>rxdata25</td>
<td></td>
<td>rxdata4</td>
</tr>
<tr>
<td>21</td>
<td>$r x d a t a 5 9$</td>
<td></td>
<td>rxdata38</td>
<td></td>
<td>rxdataRD1</td>
<td></td>
<td>rxdata8</td>
<td></td>
</tr>
<tr>
<td>22</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdata24</td>
<td></td>
<td>vccio</td>
</tr>
<tr>
<td>23</td>
<td>rxdata56</td>
<td></td>
<td>rxdata39</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdata18</td>
<td></td>
</tr>
<tr>
<td>24</td>
<td></td>
<td>rxdata45</td>
<td></td>
<td>rxvldRD</td>
<td></td>
<td>rxdata23</td>
<td></td>
<td>rxdata7</td>
</tr>
<tr>
<td>25</td>
<td>VSS</td>
<td></td>
<td>rxdata40</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td>26</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxvld</td>
<td></td>
<td>rxdata22</td>
<td></td>
<td>rxdata6</td>
</tr>
<tr>
<td>27</td>
<td>rxdata57</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxckRD</td>
<td></td>
<td>rxdata19</td>
<td></td>
</tr>
<tr>
<td>28</td>
<td></td>
<td>rxdata44</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
</tr>
<tr>
<td>29</td>
<td>rxdata58</td>
<td></td>
<td>rxdata41</td>
<td></td>
<td>rxckn</td>
<td></td>
<td>rxdata20</td>
<td></td>
</tr>
<tr>
<td>30</td>
<td></td>
<td>rxdata43</td>
<td></td>
<td>rxtrk</td>
<td></td>
<td>rxdata21</td>
<td></td>
<td>rxdata5</td>
</tr>
<tr>
<td>31</td>
<td>VSS</td>
<td></td>
<td>rxdata42</td>
<td></td>
<td>rxckp</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td>32</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
</tr>
<tr>
<td>33</td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td>34</td>
<td></td>
<td>vccio</td>
<td></td>
<td>txckp</td>
<td></td>
<td>txdata42</td>
<td></td>
<td>vccio</td>
</tr>
<tr>
<td>35</td>
<td>txdata5</td>
<td></td>
<td>txdata21</td>
<td></td>
<td>txtrk</td>
<td></td>
<td>txdata43</td>
<td></td>
</tr>
<tr>
<td>36</td>
<td></td>
<td>txdata20</td>
<td></td>
<td>txckn</td>
<td></td>
<td>txdata41</td>
<td></td>
<td>txdata58</td>
</tr>
<tr>
<td>37</td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata44</td>
<td></td>
</tr>
<tr>
<td>38</td>
<td></td>
<td>txdata19</td>
<td></td>
<td>$\mathrm { t x c k R D }$</td>
<td></td>
<td>vccio</td>
<td></td>
<td>txdata57</td>
</tr>
<tr>
<td>39</td>
<td>txdata6</td>
<td></td>
<td>txdata22</td>
<td></td>
<td>txvld</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td>40</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>txdata40</td>
<td></td>
<td>vccio</td>
</tr>
<tr>
<td>41</td>
<td>txdata7</td>
<td></td>
<td>txdata23</td>
<td></td>
<td>txvldRD</td>
<td></td>
<td>txdata45</td>
<td></td>
</tr>
<tr>
<td>42</td>
<td></td>
<td>txdata18</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata39</td>
<td></td>
<td>txdata56</td>
</tr>
<tr>
<td>43</td>
<td>VSS</td>
<td></td>
<td>txdata24</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td>44</td>
<td></td>
<td>txdata8</td>
<td></td>
<td>txdataRD1</td>
<td></td>
<td>txdata38</td>
<td></td>
<td>txdata59</td>
</tr>
<tr>
<td>45</td>
<td>txdata4</td>
<td></td>
<td>txdata25</td>
<td></td>
<td>txdataRD2</td>
<td></td>
<td>txdata55</td>
<td></td>
</tr>
<tr>
<td>46</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
</tr>
<tr>
<td>47</td>
<td>txdata3</td>
<td></td>
<td>txdata26</td>
<td></td>
<td>txdata32</td>
<td></td>
<td>txdata54</td>
<td></td>
</tr>
<tr>
<td>48</td>
<td></td>
<td>txdata9</td>
<td></td>
<td>txdata31</td>
<td></td>
<td>txdata37</td>
<td></td>
<td>txdata60</td>
</tr>
<tr>
<td>49</td>
<td>txdata2</td>
<td></td>
<td>txdata17</td>
<td></td>
<td>txdata33</td>
<td></td>
<td>txdata53</td>
<td></td>
</tr>
<tr>
<td>50</td>
<td></td>
<td>txdata10</td>
<td></td>
<td>txdata30</td>
<td></td>
<td>txdata46</td>
<td></td>
<td>txdata61</td>
</tr>
<tr>
<td>51</td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td>52</td>
<td></td>
<td>txdata11</td>
<td></td>
<td>txdata29</td>
<td></td>
<td>txdata47</td>
<td></td>
<td>txdata62</td>
</tr>
<tr>
<td>53</td>
<td>txdata1</td>
<td></td>
<td>txdata16</td>
<td></td>
<td>txdata34</td>
<td></td>
<td>txdata52</td>
<td></td>
</tr>
<tr>
<td>54</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
</tr>
<tr>
<td>55</td>
<td>txdata0</td>
<td></td>
<td>txdata15</td>
<td></td>
<td>txdata35</td>
<td></td>
<td>txdata51</td>
<td></td>
</tr>
<tr>
<td>56</td>
<td></td>
<td>txdata12</td>
<td></td>
<td>txdata28</td>
<td></td>
<td>txdata48</td>
<td></td>
<td>txdata63</td>
</tr>
<tr>
<td>57</td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata36</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td>58</td>
<td></td>
<td>txdata13</td>
<td></td>
<td>txdata27</td>
<td></td>
<td>txdata49</td>
<td></td>
<td>txdataRD3</td>
</tr>
<tr>
<td>59</td>
<td>txdataRD0</td>
<td></td>
<td>txdata14</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata50</td>
<td></td>
</tr>
<tr>
<td>60</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
</tr>
<tr>
<td>61</td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td colspan="2"></td>
<td colspan="4">Die Edge</td>
<td></td>
</tr>
<tr>
<td></td>
<td colspan="8"></td>
</tr>
</table>

Note:
In Figure 5-29, at 55-um pitch, the module depth of the 8-column bump map as
shown is approximately 1705 um. Rows 1, 2, and 61 are required for packaging
solutions using floating bridges without TSVs. They can be optional for packaging
solutions with TSVs.

### 5.7.2.2.1 x64 Advanced Package Module Bump Map for 48 GT/s and 64 GT/s

Figure 5-30 illustrates bump configurations for Advanced Package modules that operate at data rates
of 48 GT/s and 64 GT/s. In comparison to the configuration for 32 GT/s, additional power and ground
bumps have been incorporated. This is designed to mitigate the impact of increased crosstalk at
higher data rates and to accommodate the higher total current. It should be noted that additional
bump maps or further optimizations may be introduced in subsequent updates to this specification.

<table>
<caption>Figure 5-30. 10-column x64 Advanced Package Bump Map for 48 GT/s and 64 GT/s</caption>
<tr>
<th rowspan="69"></th>
<th>Column 1</th>
<th>Column 2</th>
<th>Column 3</th>
<th>Column 4</th>
<th>Column 5</th>
<th>Column 6</th>
<th>Column 7</th>
<th>Column 8</th>
<th>Column 9</th>
<th>Column 10</th>
<th></th>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>rxcksbRD</td>
<td></td>
<td>rxcksb</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdatasb</td>
<td></td>
<td>rxdatasbRD</td>
<td></td>
</tr>
<tr>
<td>txdatasbRD</td>
<td></td>
<td>txdatasb</td>
<td></td>
<td>vccio</td>
<td></td>
<td>txcksb</td>
<td></td>
<td>txcksbRD</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>rxdata50</td>
<td></td>
<td>rxdata35</td>
<td></td>
<td>rxdata29</td>
<td></td>
<td>rxdata14</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td>rxdataRD3</td>
<td></td>
<td>rxdata49</td>
<td></td>
<td>rxdata34</td>
<td></td>
<td>rxdata28</td>
<td></td>
<td>rxdata13</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata 12</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>rxdata51</td>
<td></td>
<td>rxdata36</td>
<td></td>
<td>rxdata30</td>
<td></td>
<td>rxdata15</td>
<td></td>
<td>rxdataRD0</td>
<td></td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>rxdata48</td>
<td></td>
<td>rxdata33</td>
<td></td>
<td>rxdata27</td>
<td></td>
<td>VSS</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>rxdata52</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
</tr>
<tr>
<td>rxdata63</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata11</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdata37</td>
<td></td>
<td>rxdata31</td>
<td></td>
<td>rxdata16</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>rxdata47</td>
<td></td>
<td>rxdata32</td>
<td></td>
<td>rxdata26</td>
<td></td>
<td>rxdata10</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>rxdata53</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdata0</td>
<td></td>
</tr>
<tr>
<td>rxdata62</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdata38</td>
<td></td>
<td>rxdataRD1</td>
<td></td>
<td>rxdata17</td>
<td></td>
<td>vccio</td>
<td></td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>rxdata46</td>
<td></td>
<td>rxdataRD2</td>
<td></td>
<td>rxdata25</td>
<td></td>
<td>rxdata9</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>rxdata54</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdata1</td>
<td></td>
</tr>
<tr>
<td>rxdata61</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdata39</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdata18</td>
<td></td>
<td>vccio</td>
<td></td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>rxdata45</td>
<td></td>
<td>rxvldRD</td>
<td></td>
<td>rxdata24</td>
<td></td>
<td>rxdata8</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>rxdata55</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdata2</td>
<td></td>
</tr>
<tr>
<td>rxdata60</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxvld</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdata40</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdata19</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td>vccio</td>
<td></td>
<td>rxdata44</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata23</td>
<td></td>
<td>rxdata7</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>rxdata56</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxckRD</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdata3</td>
<td></td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxtrk</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata6</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>rxdata57</td>
<td></td>
<td>rxdata41</td>
<td></td>
<td>rxckn</td>
<td></td>
<td>rxdata20</td>
<td></td>
<td>vccio</td>
<td></td>
</tr>
<tr>
<td>rxdata59</td>
<td></td>
<td>rxdata43</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxckp</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdata4</td>
<td></td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>rxdata42</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata22</td>
<td></td>
<td>rxdata5</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>rxdata58</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata21</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>txdata21</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata58</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata5</td>
<td></td>
<td>txdata22</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata42</td>
<td></td>
<td>vccio</td>
<td></td>
</tr>
<tr>
<td>txdata4</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txckp</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>txdata43</td>
<td></td>
<td>txdata59</td>
<td></td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>txdata20</td>
<td></td>
<td>txckn</td>
<td></td>
<td>txdata41</td>
<td></td>
<td>txdata57</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata6</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txtrk</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td>txdata3</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txckRD</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata56</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata7</td>
<td></td>
<td>txdata23</td>
<td></td>
<td>vccio</td>
<td></td>
<td>txdata44</td>
<td></td>
<td>vccio</td>
<td></td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>txdata19</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata40</td>
<td></td>
<td>VSS</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>txvld</td>
<td></td>
<td>vccio</td>
<td></td>
<td>txdata60</td>
<td></td>
</tr>
<tr>
<td>txdata2</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata55</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata8</td>
<td></td>
<td>txdata24</td>
<td></td>
<td>txvldRD</td>
<td></td>
<td>txdata45</td>
<td></td>
<td>vccio</td>
<td></td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>txdata18</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata39</td>
<td></td>
<td>VSS</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>txdata61</td>
<td></td>
</tr>
<tr>
<td>txdata1</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata54</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata9</td>
<td></td>
<td>txdata25</td>
<td></td>
<td>txdataRD2</td>
<td></td>
<td>txdata46</td>
<td></td>
<td>vccio</td>
<td></td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>txdata17</td>
<td></td>
<td>txdataRD1</td>
<td></td>
<td>txdata38</td>
<td></td>
<td>VSS</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>txdata62</td>
<td></td>
</tr>
<tr>
<td>txdata0</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata53</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata10</td>
<td></td>
<td>txdata26</td>
<td></td>
<td>txdata32</td>
<td></td>
<td>txdata47</td>
<td></td>
<td>vccio</td>
<td></td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>txdata16</td>
<td></td>
<td>txdata31</td>
<td></td>
<td>txdata37</td>
<td></td>
<td>VSS</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata11</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>txdata63</td>
<td></td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata52</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>vccio</td>
<td></td>
<td>txdata27</td>
<td></td>
<td>txdata33</td>
<td></td>
<td>txdata48</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td>txdataRD0</td>
<td></td>
<td>txdata15</td>
<td></td>
<td>txdata30</td>
<td></td>
<td>txdata36</td>
<td></td>
<td>txdata51</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata12</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata13</td>
<td></td>
<td>txdata28</td>
<td></td>
<td>txdata34</td>
<td></td>
<td>txdata49</td>
<td></td>
<td>txdataRD3</td>
<td></td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>txdata14</td>
<td></td>
<td>txdata29</td>
<td></td>
<td>txdata35</td>
<td></td>
<td>txdata50</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
</tr>
<tr>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td colspan="11">Die Edge</td>
</tr>
<tr>
<td></td>
<td colspan="11"></td>
</tr>
</table>

### 5.7.2.3 x32 Advanced Package Module Bump Map

UCIe also defines a x32 Advanced Package Module that supports 32 Tx and 32 Rx data signals and
two redundant bumps each for Tx and two for Rx (total of four) for lane-repair functions. All other
signals, including the sidebands, are the same as those of the x64 Advanced Package.

Figure 5-31, Figure 5-32, and Figure 5-33 show the reference bump matrix for the 10-column, 16-
column, and 8-column x32 Advanced Package Modules, respectively. The lower left corner of the
bump map will be considered "origin" of a bump matrix and the leftmost column is Column 0.

It is strongly recommended to follow the bump matrices provided in Figure 5-31, Figure 5-32, and
Figure 5-33 for x32 Advanced Package Modules.

The following rule must be followed for the 10-column x32 Advanced Package bump matrix:

· The signals order within a column must be preserved. For example, Column 0 must contain the
signals: txdataRD0, txdata0, txdata1, txdata2, txdata3, txdata4, and txdatasbRD.
Similarly, 16-column and 8-column x32 Advanced Packages must preserve the signal order within
a column of the respective bump matrices.

It is strongly recommended to follow the supply and ground pattern shown in the bump matrices. It
must be ensured that sufficient supply and ground bumps are provided to meet channel
characteristics (FEXT and NEXT) and power-delivery requirements.

When instantiating multiple x32 Advanced Package Modules, the same rules as defined in
Section 5.7.2.2 must be followed.

<table>
<caption>Figure 5-31. 10-column x32 Advanced Package Bump Map for $< = 3 2 \quad G T / s$</caption>
<tr>
<th>Column0</th>
<th>Column1</th>
<th>Column2</th>
<th>Column3</th>
<th>Column4</th>
<th>Column5</th>
<th>Column6</th>
<th>Column7</th>
<th>Column8</th>
<th>Column9</th>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td></td>
<td>rxcksbRD</td>
<td></td>
<td>rxcksb</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdatasb</td>
<td></td>
<td>rxdatasbRD</td>
</tr>
<tr>
<td>txdatasbRD</td>
<td></td>
<td>txdatasb</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txcksb</td>
<td></td>
<td>txcksbRD</td>
<td></td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata22</td>
<td></td>
<td>rxdata31</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>txdata21</td>
<td></td>
<td>txckp</td>
<td></td>
<td>rxdata30</td>
<td></td>
<td>rxdata13</td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata5</td>
<td></td>
<td>txdata23</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata14</td>
<td></td>
<td>vccio</td>
</tr>
<tr>
<td>vccio</td>
<td></td>
<td>txdata20</td>
<td></td>
<td>txckn</td>
<td></td>
<td>rxdata29</td>
<td></td>
<td>rxdata12</td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata6</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdataRD1</td>
<td></td>
<td>rxdata15</td>
<td></td>
<td>rxdataRD0</td>
</tr>
<tr>
<td>txdata4</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txckRD</td>
<td></td>
<td>rxdata28</td>
<td></td>
<td>rxdata11</td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata7</td>
<td></td>
<td>txdata24</td>
<td></td>
<td>rxvldRD</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>txdata19</td>
<td></td>
<td>txtrk</td>
<td></td>
<td>rxdata27</td>
<td></td>
<td>rxdata10</td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata8</td>
<td></td>
<td>txdata25</td>
<td></td>
<td>rxvld</td>
<td></td>
<td>rxdata16</td>
<td></td>
<td>rxdata0</td>
</tr>
<tr>
<td>txdata3</td>
<td></td>
<td>txdata18</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata26</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata26</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata17</td>
<td></td>
<td>rxdata1</td>
</tr>
<tr>
<td>txdata2</td>
<td></td>
<td>txdata17</td>
<td></td>
<td>txvld</td>
<td></td>
<td>$r x d a t a 2 5$</td>
<td></td>
<td>rxdata9</td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata9</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxtrk</td>
<td></td>
<td>$r x d a t a 1 8$</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata10</td>
<td></td>
<td>txdata27</td>
<td></td>
<td>rxckRD</td>
<td></td>
<td>rxdata19</td>
<td></td>
<td>rxdata2</td>
</tr>
<tr>
<td>txdata1</td>
<td></td>
<td>txdata16</td>
<td></td>
<td>txvldRD</td>
<td></td>
<td>rxdata24</td>
<td></td>
<td>rxdata8</td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata11</td>
<td></td>
<td>txdata28</td>
<td></td>
<td>rxckn</td>
<td></td>
<td>rxdata20</td>
<td></td>
<td>rxdata3</td>
</tr>
<tr>
<td>txdata0</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata7</td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata12</td>
<td></td>
<td>txdata29</td>
<td></td>
<td>rxckp</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>txdata15</td>
<td></td>
<td>txdataRD1</td>
<td></td>
<td>rxdata23</td>
<td></td>
<td>rxdata6</td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata13</td>
<td></td>
<td>txdata30</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata21</td>
<td></td>
<td>rxdata4</td>
</tr>
<tr>
<td>txdataRD0</td>
<td></td>
<td>txdata14</td>
<td></td>
<td>txdata31</td>
<td></td>
<td>rxdata22</td>
<td></td>
<td>rxdata5</td>
<td></td>
</tr>
<tr>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
</tr>
<tr>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
</tr>
</table>

Die Edge

Note:
In Figure 5-31, at 45-um pitch, the module depth of the 10-column reference bump
matrix as shown is approximately 680.5 um.

<table>
<caption>Figure 5-32. 16-column x32 Advanced Package Bump Map for $< = 3 2 \quad G T / s$</caption>
<tr>
<th></th>
<th>Column0</th>
<th>Column1</th>
<th>Column2</th>
<th>Column3</th>
<th>Column4</th>
<th>Column5</th>
<th>Column6</th>
<th>Column7</th>
<th>Column8</th>
<th>Column9</th>
<th>Column10</th>
<th>Column11</th>
<th>Column12</th>
<th>Column13</th>
<th>Column14</th>
<th>Column15</th>
</tr>
<tr>
<th></th>
<th></th>
<th>VSS</th>
<th></th>
<th>VSS</th>
<th></th>
<th>VSS</th>
<th></th>
<th>VSS</th>
<th></th>
<th>VSS</th>
<th></th>
<th>VSS</th>
<th></th>
<th>VSS</th>
<th></th>
<th>VSS</th>
</tr>
<tr>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdatasbRD</td>
<td></td>
<td>rxcksbRD</td>
<td></td>
<td>txdatasb</td>
<td></td>
<td>rxcksb</td>
<td></td>
<td>txcksb</td>
<td></td>
<td>rxdatasb</td>
<td></td>
<td>txcksbRD</td>
<td></td>
<td>rxdatasbRD</td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata5</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata4</td>
<td></td>
<td>txdata20</td>
<td></td>
<td>txdata22</td>
<td></td>
<td>txtrk</td>
<td></td>
<td>rxdata30</td>
<td></td>
<td>rxdata26</td>
<td></td>
<td>rxdata13</td>
<td></td>
<td>rxdataRD0</td>
</tr>
<tr>
<td></td>
<td>txdata2</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata21</td>
<td></td>
<td>txckp</td>
<td></td>
<td>rxdata31</td>
<td></td>
<td>rxdata27</td>
<td></td>
<td>rxdata 14</td>
<td></td>
<td>rxdata11</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata3</td>
<td></td>
<td>txdata17</td>
<td></td>
<td>txdata23</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata29</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata 12</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td></td>
<td>txdata1</td>
<td></td>
<td>txdata6</td>
<td></td>
<td>txdata19</td>
<td></td>
<td>txckn</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata28</td>
<td></td>
<td>rxdata15</td>
<td></td>
<td>rxdata10</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata8</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txvld</td>
<td></td>
<td>rxdataRD1</td>
<td></td>
<td>rxdata25</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata0</td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata7</td>
<td></td>
<td>txdata18</td>
<td></td>
<td>txckRD</td>
<td></td>
<td>rxvldRD</td>
<td></td>
<td>rxdata24</td>
<td></td>
<td>rxdata16</td>
<td></td>
<td>rxdata9</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata9</td>
<td></td>
<td>txdata16</td>
<td></td>
<td>txdata24</td>
<td></td>
<td>txvldRD</td>
<td></td>
<td>rxckRD</td>
<td></td>
<td>rxdata18</td>
<td></td>
<td>rxdata7</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td></td>
<td>txdata0</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata25</td>
<td></td>
<td>txdataRD1</td>
<td></td>
<td>rxvld</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata17</td>
<td></td>
<td>rxdata8</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata10</td>
<td></td>
<td>txdata15</td>
<td></td>
<td>txdata28</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxckn</td>
<td></td>
<td>rxdata19</td>
<td></td>
<td>rxdata6</td>
<td></td>
<td>rxdata1</td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata12</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata29</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata23</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata3</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata11</td>
<td></td>
<td>txdata14</td>
<td></td>
<td>txdata27</td>
<td></td>
<td>txdata31</td>
<td></td>
<td>rxckp</td>
<td></td>
<td>rxdata21</td>
<td></td>
<td>rxdata5</td>
<td></td>
<td>rxdata2</td>
</tr>
<tr>
<td></td>
<td>txdataRD0</td>
<td></td>
<td>txdata13</td>
<td></td>
<td>txdata26</td>
<td></td>
<td>txdata30</td>
<td></td>
<td>rxtrk</td>
<td></td>
<td>rxdata22</td>
<td></td>
<td>rxdata20</td>
<td></td>
<td>rxdata4</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
</tr>
<tr>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
</tr>
<tr>
<td></td>
<td colspan="4"></td>
<td></td>
<td></td>
<td colspan="4">Die Edge</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
</table>

Note:
In Figure $5 - 3 2 ,$ at 25-um pitch, the module depth of the 16-column reference bump
matrix as shown is approximately 237.5 um.

<table>
<caption>Figure 5-33. 8-column x32 Advanced Package Bump Map for $< = 3 2 \quad G T / s$</caption>
<tr>
<th></th>
<th>Column0</th>
<th>Column1</th>
<th>Column2</th>
<th>Column3</th>
<th>Column4</th>
<th>Column5</th>
<th>Column6</th>
<th>Column7</th>
</tr>
<tr>
<th rowspan="2"></th>
<th></th>
<th>VSS</th>
<th></th>
<th>VSS</th>
<th></th>
<th>VSS</th>
<th></th>
<th>VSS</th>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
</tr>
<tr>
<td></td>
<td>rxcksbRD</td>
<td></td>
<td>rxcksb</td>
<td></td>
<td>rxdatasb</td>
<td></td>
<td>rxdatasbRD</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdatasbRD</td>
<td></td>
<td>txdatasb</td>
<td></td>
<td>txcksb</td>
<td></td>
<td>txcksbRD</td>
</tr>
<tr>
<td></td>
<td>txdata5</td>
<td></td>
<td>txdata23</td>
<td></td>
<td>rxdata30</td>
<td></td>
<td>rxdata13</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata22</td>
<td></td>
<td>txckp</td>
<td></td>
<td>rxdata14</td>
<td></td>
<td>rxdataRD0</td>
</tr>
<tr>
<td></td>
<td>txdata6</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata12</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata21</td>
<td></td>
<td>txckn</td>
<td></td>
<td>rxdata15</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td></td>
<td>txdata7</td>
<td></td>
<td>txdata24</td>
<td></td>
<td>rxdata31</td>
<td></td>
<td>rxdata11</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata20</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata0</td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata25</td>
<td></td>
<td>rxdataRD1</td>
<td></td>
<td>rxdata10</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata19</td>
<td></td>
<td>txckRD</td>
<td></td>
<td>rxdata16</td>
<td></td>
<td>rxdata1</td>
</tr>
<tr>
<td></td>
<td>txdata4</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata9</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata18</td>
<td></td>
<td>txtrk</td>
<td></td>
<td>rxdata29</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td></td>
<td>txdata3</td>
<td></td>
<td>txdata26</td>
<td></td>
<td>rxvldRD</td>
<td></td>
<td>rxdata8</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata17</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata28</td>
<td></td>
<td>rxdata2</td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata27</td>
<td></td>
<td>rxvld</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata8</td>
<td></td>
<td>txvld</td>
<td></td>
<td>rxdata27</td>
<td></td>
<td>rxdata3</td>
</tr>
<tr>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata9</td>
<td></td>
<td>txvldRD</td>
<td></td>
<td>rxdata26</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td></td>
<td>txdata2</td>
<td></td>
<td>txdata28</td>
<td></td>
<td>rxtrk</td>
<td></td>
<td>rxdata17</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata10</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata4</td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata29</td>
<td></td>
<td>rxckRD</td>
<td></td>
<td>rxdata18</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata11</td>
<td></td>
<td>txdataRD1</td>
<td></td>
<td>rxdata25</td>
<td></td>
<td>rxdata7</td>
</tr>
<tr>
<td></td>
<td>txdata1</td>
<td></td>
<td>txdata16</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata19</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata31</td>
<td></td>
<td>rxdata24</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td></td>
<td>txdata0</td>
<td></td>
<td>txdata15</td>
<td></td>
<td>rxckn</td>
<td></td>
<td>rxdata20</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata12</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata6</td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata14</td>
<td></td>
<td>rxckp</td>
<td></td>
<td>rxdata21</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata13</td>
<td></td>
<td>txdata30</td>
<td></td>
<td>rxdata23</td>
<td></td>
<td>rxdata5</td>
</tr>
<tr>
<td></td>
<td>txdataRD0</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata22</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
</tr>
<tr>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
</tr>
<tr>
<td></td>
<td colspan="8">Die Edge</td>
</tr>
</table>

Note:
In Figure 5-33, at 55-um pitch, the module depth of the 8-column reference bump
matrix as shown is approximately 962.5 um.

<table>
<caption>Figure 5-34 shows the signal exit order for the 10-column x32 Advanced Package bump map. Figure 5-34. 10-column x32 Advanced Package Bump Map: Signal Exit Order</caption>
<tr>
<td rowspan="5">$T x$ Breakout</td>
<td>Left to Right</td>
<td></td>
<td></td>
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
<td>txdataRD0</td>
<td>txdata0</td>
<td>txdata1</td>
<td>txdata2</td>
<td>txdata3</td>
<td>txdata4</td>
<td>txdata5</td>
<td>txdata6</td>
<td>txdata7</td>
<td>txdata8</td>
<td>Cont ...</td>
</tr>
<tr>
<td>Cont ...</td>
<td>txdata9</td>
<td>txdata10</td>
<td>txdata11</td>
<td>txdata12</td>
<td>txdata13</td>
<td>txdata14</td>
<td>txdata15</td>
<td>txdata16</td>
<td>txdata17</td>
<td>txdata18</td>
<td>Cont1 ..</td>
</tr>
<tr>
<td>Cont1 ...</td>
<td>txdata19</td>
<td>txdata20</td>
<td>txdata21</td>
<td>txdata22</td>
<td>txdata23</td>
<td>txdata24</td>
<td>txdata25</td>
<td>txdata26</td>
<td>txdata27</td>
<td>txdata28</td>
<td>Cont2 ...</td>
</tr>
<tr>
<td>$\mathrm { c o n t 2 } .$</td>
<td>txdata29</td>
<td>txdata30</td>
<td>txdata31</td>
<td>txdataRD1</td>
<td>txvldRD</td>
<td>txvld</td>
<td>txtrk</td>
<td>txckRD</td>
<td>txckn</td>
<td>txckp</td>
<td></td>
</tr>
<tr>
<td rowspan="5">Rx Breakout</td>
<td>Left to Right</td>
<td></td>
<td></td>
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
<td>rxckp</td>
<td>rxckn</td>
<td>rxckRD</td>
<td>rxtrk</td>
<td>rxvld</td>
<td>rxvldRD</td>
<td>rxdataRD1</td>
<td>rxdata31</td>
<td>rxdata30</td>
<td>rxdata29</td>
<td>Cont ...</td>
</tr>
<tr>
<td>Cont ...</td>
<td>rxdata28</td>
<td>rxdata27</td>
<td>rxdata26</td>
<td>rxdata25</td>
<td>rxdata24</td>
<td>rxdata23</td>
<td>rxdata22</td>
<td>rxdata21</td>
<td>rxdata20</td>
<td>rxdata19</td>
<td>$\cot 1 .$</td>
</tr>
<tr>
<td>Cont1 ...</td>
<td>rxdata18</td>
<td>$r x d a t a 1 7$</td>
<td>rxdata16</td>
<td>rxdata15</td>
<td>rxdata14</td>
<td>rxdata13</td>
<td>rxdata12</td>
<td>rxdata11</td>
<td>rxdata10</td>
<td>rxdata9</td>
<td>$\cot 2 \ldots .$</td>
</tr>
<tr>
<td>Cont2 ...</td>
<td>rxdata8</td>
<td>rxdata7</td>
<td>rxdata6</td>
<td>rxdata5</td>
<td>rxdata4</td>
<td>rxdata3</td>
<td>rxdata2</td>
<td>rxdata1</td>
<td>rxdata0</td>
<td>rxdataRD0</td>
<td></td>
</tr>
</table>

# IMPLEMENTATION NOTE

## High-speed Considerations for x32 Bump Maps

This Implementation Note is formulated to provide PHY implementations a set of reference x32
bump maps to encompass the max speed specified.

Bump maps in Figure 5-35, Figure 5-36, and Figure 5-37 are the x32 implementation references for
the corresponding max speed with an enhancement of the power and ground bumps. They all
comply with the bump matrix rules in Section 5.7.2.3, and they maintain the backward compatibility
in terms of signal exit order. These reference examples have been optimized for signal integrity,
power integrity, lane-to-lane skew, electro-migration stress and bump area based on most of the
advanced packaging technologies in the industry. Please note that technology requirements vary,
and it is still required to verify the bump map with the technology provider for actual implementation
requirements and performance targets.

These bump maps have been optimized to minimize the lane to-lane routing mismatch, which is not
avoidable when two different bumps at different bump pitches interoperate. Table 5-20 summarizes
the max skew due to bump locations for the representative cases. As a rule of thumb, each 150-um
mismatch causes about 1-ps timing skew. This skew can be reduced or eliminated by the length
matching effort in package channel layout design.

<table>
<caption>Table 5-20. Maximum Systematic Lane-to-lane Length Mismatch in um between the Reference Bump Maps in the Implementation Note</caption>
<tr>
<th>Rx</th>
<th rowspan="2">$\begin{array}{} { 1 6 - c o l u m n } \\ { \times 6 4 a t 2 5 u n } \end{array}$</th>
<th rowspan="2">16-column x32 at 25 um</th>
<th rowspan="2">10-column x64 at 45 um</th>
<th rowspan="2">10-column x32 at 45 um</th>
<th rowspan="2">$\begin{array}{} { 8 - \mathrm { c o l u m n } } \\ { \times 6 4 \text { at } 5 5 \text { um } } \end{array}$</th>
<th rowspan="2">$8 - \mathrm { c o l u m n }$</th>
</tr>
<tr>
<th>Tx</th>
</tr>
<tr>
<td>$\begin{array}{} { 1 6 - \mathrm { c o l u m n } x 6 4 } \\ { \text { at } 2 5 \text { um } } \end{array}$</td>
<td>0</td>
<td>125</td>
<td>351</td>
<td>399</td>
<td>560</td>
<td>605</td>
</tr>
<tr>
<td>$\begin{array}{} { 1 6 - c 0 l u m n \times 3 2 } \\ { a t 2 5 u m } \end{array}$</td>
<td></td>
<td>0</td>
<td>351</td>
<td>393</td>
<td>563</td>
<td>618</td>
</tr>
<tr>
<td>$1 0 - \mathrm { c o l u m } n \times 6 4$</td>
<td></td>
<td></td>
<td>0</td>
<td>159</td>
<td>351</td>
<td>463</td>
</tr>
<tr>
<td>$1 0 - \mathrm { c o l u m n } \times 3 2$</td>
<td></td>
<td></td>
<td></td>
<td>0</td>
<td>428</td>
<td>398</td>
</tr>
<tr>
<td>$8 - \mathrm { c o l u m n } \times 6 4$</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>0</td>
<td>468</td>
</tr>
<tr>
<td>$\begin{array}{} { 8 - \mathrm { c o l u m } n \times 3 2 } \\ { \text { at } 5 5 \text { um } } \end{array}$</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>0</td>
</tr>
</table>

# IMPLEMENTATION NOTE

## Continued

<table>
<caption>Figure 5-35. Enhanced 10-column x32 Advanced Package Bump Map Example for 32 GT/s Implementation</caption>
<tr>
<th rowspan="2">1</th>
<th>1</th>
<th>2</th>
<th>3</th>
<th>4</th>
<th>5</th>
<th>6</th>
<th>7</th>
<th>8</th>
<th>9</th>
<th colspan="2">10</th>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
<td></td>
</tr>
<tr>
<td>2</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
<td colspan="2">VSS</td>
</tr>
<tr>
<td>3</td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
<td></td>
</tr>
<tr>
<td>4</td>
<td></td>
<td>rxcksbRD</td>
<td></td>
<td>rxcksb</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdatasb</td>
<td></td>
<td>rxdatasbRD</td>
<td></td>
</tr>
<tr>
<td>5</td>
<td>txdatasbRD</td>
<td></td>
<td>txdatasb</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txcksb</td>
<td></td>
<td>txcksbRD</td>
<td></td>
<td></td>
</tr>
<tr>
<td>6</td>
<td></td>
<td>txdata5</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata14</td>
<td></td>
<td>vccio</td>
<td></td>
</tr>
<tr>
<td>7</td>
<td>txdata4</td>
<td></td>
<td>txdata21</td>
<td></td>
<td>txckp</td>
<td></td>
<td>rxdata30</td>
<td></td>
<td>rxdata13</td>
<td></td>
<td></td>
</tr>
<tr>
<td>8</td>
<td></td>
<td>txdata6</td>
<td></td>
<td>txdata22</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdataRD0</td>
<td></td>
</tr>
<tr>
<td>9</td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txckn</td>
<td></td>
<td>rxdata29</td>
<td></td>
<td>rxdata12</td>
<td></td>
<td></td>
</tr>
<tr>
<td>10</td>
<td></td>
<td>txdata7</td>
<td></td>
<td>txdata23</td>
<td></td>
<td>rxdata31</td>
<td></td>
<td>rxdata15</td>
<td></td>
<td>vccio</td>
<td></td>
</tr>
<tr>
<td>11</td>
<td>vccio</td>
<td></td>
<td>txdata20</td>
<td></td>
<td>txckRD</td>
<td></td>
<td>rxdata28</td>
<td></td>
<td>VSS</td>
<td></td>
<td></td>
</tr>
<tr>
<td>12</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdata16</td>
<td></td>
<td>rxdata0</td>
<td></td>
</tr>
<tr>
<td>13</td>
<td>txdata3</td>
<td></td>
<td>txdata19</td>
<td></td>
<td>txtrk</td>
<td></td>
<td>rxdata27</td>
<td></td>
<td>rxdata11</td>
<td></td>
<td></td>
</tr>
<tr>
<td>14</td>
<td></td>
<td>txdata8</td>
<td></td>
<td>txdata24</td>
<td></td>
<td>rxdataRD1</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdata1</td>
<td></td>
</tr>
<tr>
<td>15</td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata10</td>
<td></td>
<td></td>
</tr>
<tr>
<td>16</td>
<td></td>
<td>txdata9</td>
<td></td>
<td>txdata25</td>
<td></td>
<td>rxvldRD</td>
<td></td>
<td>rxdata17</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td>17</td>
<td>txdata2</td>
<td></td>
<td>txdata18</td>
<td></td>
<td>txvld</td>
<td></td>
<td>rxdata26</td>
<td></td>
<td>VSS</td>
<td></td>
<td></td>
</tr>
<tr>
<td>18</td>
<td></td>
<td>vccio</td>
<td></td>
<td>txdata26</td>
<td></td>
<td>rxvld</td>
<td></td>
<td>rxdata18</td>
<td></td>
<td>rxdata2</td>
<td></td>
</tr>
<tr>
<td>19</td>
<td>vccio</td>
<td></td>
<td>txdata17</td>
<td></td>
<td>txvldRD</td>
<td></td>
<td>rxdata25</td>
<td></td>
<td>rxdata9</td>
<td></td>
<td></td>
</tr>
<tr>
<td>20</td>
<td></td>
<td>txdata10</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
</tr>
<tr>
<td>21</td>
<td>txdata1</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdataRD1</td>
<td></td>
<td>rxdata24</td>
<td></td>
<td>rxdata8</td>
<td></td>
<td></td>
</tr>
<tr>
<td>22</td>
<td></td>
<td>txdata11</td>
<td></td>
<td>txdata27</td>
<td></td>
<td>rxtrk</td>
<td></td>
<td>rxdata19</td>
<td></td>
<td>rxdata3</td>
<td></td>
</tr>
<tr>
<td>23</td>
<td>txdata0</td>
<td></td>
<td>txdata16</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td></td>
</tr>
<tr>
<td>24</td>
<td></td>
<td>vccio</td>
<td></td>
<td>txdata28</td>
<td></td>
<td>rxckRD</td>
<td></td>
<td>rxdata20</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td>25</td>
<td>VSS</td>
<td></td>
<td>txdata15</td>
<td></td>
<td>txdata31</td>
<td></td>
<td>rxdata23</td>
<td></td>
<td>rxdata7</td>
<td></td>
<td></td>
</tr>
<tr>
<td>26</td>
<td></td>
<td>txdata12</td>
<td></td>
<td>txdata29</td>
<td></td>
<td>rxckn</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td>27</td>
<td>txdataRD0</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata22</td>
<td></td>
<td>rxdata6</td>
<td></td>
<td></td>
</tr>
<tr>
<td>28</td>
<td></td>
<td>txdata13</td>
<td></td>
<td>txdata30</td>
<td></td>
<td>rxckp</td>
<td></td>
<td>rxdata21</td>
<td></td>
<td>rxdata4</td>
<td></td>
</tr>
<tr>
<td>29</td>
<td>VSS</td>
<td></td>
<td>txdata14</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata5</td>
<td></td>
<td></td>
</tr>
<tr>
<td>30</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
</tr>
<tr>
<td>31</td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td colspan="2">Die Edge</td>
<td></td>
<td></td>
<td></td>
<td colspan="2"></td>
</tr>
</table>

Note:
In Figure 5-35, at 45-um pitch, the module depth of the 10-column bump map as
shown is approximately 725 um. Rows 1, 2, and 31 are required for packaging
solutions using floating bridges without through-silicon vias (TSVs). They can be
optional for packaging solutions with TSVs. The vccfwdio bumps are required for the
tightly coupled mode up to 16 GT/s. For higher speeds, the vccfwdio bumps may be
connected to the vccio bumps in package.

# IMPLEMENTATION NOTE

## Continued

<table>
<caption>Figure 5-36. Enhanced 16-column x32 Advanced Package Bump Map Example for 16 GT/s Implementation</caption>
<tr>
<th></th>
<th>1</th>
<th>2</th>
<th>3</th>
<th>4</th>
<th>5</th>
<th>6</th>
<th>7</th>
<th>8</th>
<th>9</th>
<th>10</th>
<th>11</th>
<th>12</th>
<th>13</th>
<th>14</th>
<th>15</th>
<th>16</th>
<th></th>
</tr>
<tr>
<td>1</td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
<td></td>
</tr>
<tr>
<td>2</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td>3</td>
<td>txdatasbRD</td>
<td></td>
<td>rxcksbRD</td>
<td></td>
<td>txdatasb</td>
<td></td>
<td>rxcksb</td>
<td></td>
<td>txcksb</td>
<td></td>
<td>rxdatasb</td>
<td></td>
<td>txcksbRD</td>
<td></td>
<td>rxdatasbRD</td>
<td></td>
<td></td>
</tr>
<tr>
<td>4</td>
<td></td>
<td>txdata4</td>
<td></td>
<td>txdata20</td>
<td></td>
<td>txdata22</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata30</td>
<td></td>
<td>rxdata26</td>
<td></td>
<td>rxdata13</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td>5</td>
<td>VSS</td>
<td></td>
<td>txdata5</td>
<td></td>
<td>txdata21</td>
<td></td>
<td>txckp</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata27</td>
<td></td>
<td>rxdata 14</td>
<td></td>
<td>rxdata11</td>
<td></td>
<td></td>
</tr>
<tr>
<td>6</td>
<td></td>
<td>txdata3</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata23</td>
<td></td>
<td>txtrk</td>
<td></td>
<td>rxdata29</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata12</td>
<td></td>
<td>rxdataRD0</td>
<td></td>
</tr>
<tr>
<td>7</td>
<td>txdata2</td>
<td></td>
<td>txdata6</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txckn</td>
<td></td>
<td>rxdata31</td>
<td></td>
<td>rxdata28</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata10</td>
<td></td>
<td></td>
</tr>
<tr>
<td>8</td>
<td></td>
<td>vccio</td>
<td></td>
<td>txdata17</td>
<td></td>
<td>txdata24</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdataRD1</td>
<td></td>
<td>rxdata25</td>
<td></td>
<td>rxdata7</td>
<td></td>
<td>rxdata0</td>
<td></td>
</tr>
<tr>
<td>9</td>
<td>txdata1</td>
<td></td>
<td>vccio</td>
<td></td>
<td>txdata19</td>
<td></td>
<td>txckRD</td>
<td></td>
<td>rxvldRD</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdata15</td>
<td></td>
<td>rxdata9</td>
<td></td>
<td></td>
</tr>
<tr>
<td>10</td>
<td></td>
<td>txdata8</td>
<td></td>
<td>txdata16</td>
<td></td>
<td>vccio</td>
<td></td>
<td>txvld</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdata18</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td>11</td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>txdata18</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxvld</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdata16</td>
<td></td>
<td>rxdata8</td>
<td></td>
<td></td>
</tr>
<tr>
<td>12</td>
<td></td>
<td>txdata9</td>
<td></td>
<td>txdata15</td>
<td></td>
<td>vccio</td>
<td></td>
<td>txvldRD</td>
<td></td>
<td>rxckRD</td>
<td></td>
<td>rxdata19</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdata1</td>
<td></td>
</tr>
<tr>
<td>13</td>
<td>txdata0</td>
<td></td>
<td>txdata7</td>
<td></td>
<td>txdata25</td>
<td></td>
<td>txdataRD1</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata24</td>
<td></td>
<td>rxdata17</td>
<td></td>
<td>vccio</td>
<td></td>
<td></td>
</tr>
<tr>
<td>14</td>
<td></td>
<td>txdata10</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata28</td>
<td></td>
<td>txdata31</td>
<td></td>
<td>rxckn</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata6</td>
<td></td>
<td>rxdata2</td>
<td></td>
</tr>
<tr>
<td>15</td>
<td>txdataRD0</td>
<td></td>
<td>txdata12</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata29</td>
<td></td>
<td>rxtrk</td>
<td></td>
<td>rxdata23</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata3</td>
<td></td>
<td></td>
</tr>
<tr>
<td>16</td>
<td></td>
<td>txdata11</td>
<td></td>
<td>txdata14</td>
<td></td>
<td>txdata27</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxckp</td>
<td></td>
<td>rxdata21</td>
<td></td>
<td>rxdata5</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td>17</td>
<td>VSS</td>
<td></td>
<td>txdata13</td>
<td></td>
<td>txdata26</td>
<td></td>
<td>txdata30</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata22</td>
<td></td>
<td>rxdata20</td>
<td></td>
<td>rxdata4</td>
<td></td>
<td></td>
</tr>
<tr>
<td>18</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
</tr>
<tr>
<td>19</td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
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
<td colspan="4">Die Edge</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td colspan="2"></td>
</tr>
</table>

Note:
In Figure 5-36, at 25-um pitch, the module depth of the 16-column bump map as
shown is approximately 250 um. Rows 1 and 19 are required for packaging solutions
using floating bridges without TSVs. They can be optional for packaging solutions with
TSVs. The vccfwdio bumps are required for the tightly coupled mode up to 16 GT/s.
For higher speeds, the vccfwdio bumps may be connected to the vccio bumps
in package.

# IMPLEMENTATION NOTE

## Continued

<figure>
</figure>

<table>
<tr>
<th colspan="9">Figure 5-37. Enhanced 8-column x32 Advanced Package Bump Map Example for 32 GT/s Implementation</th>
</tr>
<tr>
<th></th>
<th>1</th>
<th>2</th>
<th>3</th>
<th>4</th>
<th>5</th>
<th>6</th>
<th>7</th>
<th>8</th>
</tr>
<tr>
<td>1</td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td>2</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>3</td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td>4</td>
<td></td>
<td>txdatasbRD</td>
<td></td>
<td>txdatasb</td>
<td></td>
<td>txcksb</td>
<td></td>
<td>txcksbRD</td>
</tr>
<tr>
<td>5</td>
<td>rxcksbRD</td>
<td></td>
<td>rxcksb</td>
<td></td>
<td>rxdatasb</td>
<td></td>
<td>rxdatasbRD</td>
<td></td>
</tr>
<tr>
<td>6</td>
<td></td>
<td>txdata22</td>
<td></td>
<td>txckp</td>
<td></td>
<td>rxdata14</td>
<td></td>
<td>rxdataRD0</td>
</tr>
<tr>
<td>7</td>
<td>VSS</td>
<td></td>
<td>txdata23</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata13</td>
<td></td>
</tr>
<tr>
<td>8</td>
<td></td>
<td>txdata21</td>
<td></td>
<td>txckn</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
</tr>
<tr>
<td>9</td>
<td>txdata5</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata30</td>
<td></td>
<td>rxdata12</td>
<td></td>
</tr>
<tr>
<td>10</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdata15</td>
<td></td>
<td>rxdata0</td>
</tr>
<tr>
<td>11</td>
<td>txdata6</td>
<td></td>
<td>txdata24</td>
<td></td>
<td>rxdata31</td>
<td></td>
<td>rxdata11</td>
<td></td>
</tr>
<tr>
<td>12</td>
<td></td>
<td>txdata20</td>
<td></td>
<td>txckRD</td>
<td></td>
<td>rxdata16</td>
<td></td>
<td>rxdata1</td>
</tr>
<tr>
<td>13</td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td>14</td>
<td></td>
<td>txdata19</td>
<td></td>
<td>txtrk</td>
<td></td>
<td>rxdata29</td>
<td></td>
<td>rxdata2</td>
</tr>
<tr>
<td>15</td>
<td>txdata7</td>
<td></td>
<td>txdata25</td>
<td></td>
<td>rxdataRD1</td>
<td></td>
<td>rxdata10</td>
<td></td>
</tr>
<tr>
<td>16</td>
<td></td>
<td>txdata18</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdata28</td>
<td></td>
<td>rxdata3</td>
</tr>
<tr>
<td>17</td>
<td>vccio</td>
<td></td>
<td>txdata26</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata9</td>
<td></td>
</tr>
<tr>
<td>18</td>
<td></td>
<td>txdata17</td>
<td></td>
<td>txvld</td>
<td></td>
<td>rxdata27</td>
<td></td>
<td>vccio</td>
</tr>
<tr>
<td>19</td>
<td>txdata4</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxvldRD</td>
<td></td>
<td>rxdata8</td>
<td></td>
</tr>
<tr>
<td>20</td>
<td></td>
<td>txdata8</td>
<td></td>
<td>txvldRD</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdata4</td>
</tr>
<tr>
<td>21</td>
<td>VSS</td>
<td></td>
<td>txdata27</td>
<td></td>
<td>rxvld</td>
<td></td>
<td>rxdata17</td>
<td></td>
</tr>
<tr>
<td>22</td>
<td></td>
<td>txdata9</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdata26</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>23</td>
<td>txdata3</td>
<td></td>
<td>txdata28</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata18</td>
<td></td>
</tr>
<tr>
<td>24</td>
<td></td>
<td>txdata10</td>
<td></td>
<td>txdataRD1</td>
<td></td>
<td>rxdata25</td>
<td></td>
<td>rxdata7</td>
</tr>
<tr>
<td>25</td>
<td>txdata2</td>
<td></td>
<td>txdata29</td>
<td></td>
<td>rxtrk</td>
<td></td>
<td>rxdata19</td>
<td></td>
</tr>
<tr>
<td>26</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccfwdio</td>
</tr>
<tr>
<td>27</td>
<td>txdata1</td>
<td></td>
<td>txdata16</td>
<td></td>
<td>rxckRD</td>
<td></td>
<td>rxdata20</td>
<td></td>
</tr>
<tr>
<td>28</td>
<td></td>
<td>txdata11</td>
<td></td>
<td>txdata31</td>
<td></td>
<td>rxdata24</td>
<td></td>
<td>rxdata6</td>
</tr>
<tr>
<td>29</td>
<td>txdata0</td>
<td></td>
<td>txdata15</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td>30</td>
<td></td>
<td>txdata12</td>
<td></td>
<td>txdata30</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>rxdata5</td>
</tr>
<tr>
<td>31</td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxckn</td>
<td></td>
<td>rxdata21</td>
<td></td>
</tr>
<tr>
<td>32</td>
<td></td>
<td>txdata13</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata23</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>33</td>
<td>txdataRD0</td>
<td></td>
<td>txdata14</td>
<td></td>
<td>rxckp</td>
<td></td>
<td>rxdata22</td>
<td></td>
</tr>
<tr>
<td>34</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
</tr>
<tr>
<td>35</td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td colspan="3">Die Edge</td>
<td></td>
<td></td>
<td></td>
</tr>
</table>

Note:
In Figure 5-37, at 55-um pitch, the module depth of the 8-column bump map as
shown is approximately 990 um. Rows 1, 2, and 35 are required for packaging
solutions using floating bridges without TSVs. They can be optional for packaging
solutions with TSVs. The vccfwdio bumps are required for the tightly coupled mode up
to 16 GT/s. For higher speeds, the vccfwdio bumps may be connected to the vccio
bumps in package.

### 5.7.2.4 x64 and x32 Advanced Package Module Interoperability

x64 and x32 Advanced Package Module bump maps enable interoperability between all $\mathrm { T x }$ and Rx
combinations of x64 or x32, 10-column, 16-column, or 8-column Modules, in both Normal-to-Normal
module orientation or Normal-to-Mirrored module orientation.

However, if x64 to x32 modules or x32 to x32 modules have normal and mirrored orientation as
shown in Figure 5-38 and Figure 5-39, respectively, signal traces between the TX half and RX half will
crisscross and require swizzling technique which refers to rearranging the physical connections
between signal bumps of two chiplets to optimize the layout and routing on the interposer or
substrate. It involves changing the order of the connections or route on different layers without
altering the netlist or the electrical functionality of the design. Moreover, connections between 8-
column, 16-column, and 10-column modules may need to be routed to adjacent columns (swizzle and
go across). In all cases, the electrical spec must be met for all these connections.

It is optional for a x64 Module to support interoperability with a x32 Module. The following
requirements apply when a x64 module supports x32 interoperability:

. When a x64 module connects to x32 module, the connection shall always be contained to the
lower half of the x64 module. This must be followed even with x32 lane reversal described below.

· Electrical specifications must be met for combinations that require signal-routing swizzling.

· Lane reversal will not be permitted on CKP-, CKN-, CKRD-, VLD-, VLDRD-, TRK-, and sideband-
related pins. These pins need to be connected appropriately. Swizzling for these connections is
acceptable.

· x64 module must support a lane-reversal mode in a x32 manner (i.e., TD_P [31 : 0] =
TD_L [0 : 31]. When a x64 module is connected to a x32 module, in either Normal or Mirrored
orientation, the upper 32 bits are not used and should be disabled.

. It is not permitted for a single module of larger width to simultaneously interop with two or more
modules of a lower width. For example, a x64 Advanced Package module physically connected to
two x32 Advanced Package modules is prohibited.

Additional technological capabilities or layers may be needed to accomplish swizzling on data/auxiliary
signals.

Table 5-21 summarizes the connections between combinations of x64 and x32 modules in both
Normal-to-Normal and Normal-to-Mirrored module orientations. The table applies to all combinations
of 10-column, 16-column, or 8-column modules on either side of the Link.

<table>
<caption>Table 5-21. x64 and x32 Advanced Package Connectivity Matrix</caption>
<tr>
<th rowspan="3">Normal Module Tx</th>
<th colspan="2">Normal Module</th>
<th colspan="2">Mirrored Module</th>
</tr>
<tr>
<th colspan="4">Rx</th>
</tr>
<tr>
<th>x64</th>
<th>x32</th>
<th>x64</th>
<th>x32</th>
</tr>
<tr>
<td>x64</td>
<td>TX[63:0] - RX[63:0]ª</td>
<td>TX[31:0] - RX[31:0]b</td>
<td>rTX[63:0] - RX[0:63]c d</td>
<td>rTX[31:0] - RX[0:31]ce</td>
</tr>
<tr>
<td>x32</td>
<td>TX[31:0] - RX[31:0]b</td>
<td>TX[31:0] - RX[31:0]b</td>
<td>rTX[31:0] - RX[0:31]ce</td>
<td>rTX[31:0] - RX[0:31]c e</td>
</tr>
</table>

a. Entry "TX[63:0] - RX[63:0]" is for Normal Module connections between two x64 modules without lane reversal.
This applies to x64-to-x64 combination.

b. Entry "TX[31:0] - RX[31:0]" is for Normal Module connections between lower 32-bit half without lane reversal.
This applies to x64-to-x32, x32-to-x64, and x32-to-x32 combinations.

c. The prefix "r" means lane reversal is enabled on the Transmitter lanes, and:
. "rTX[63:0]" means TD_P[63:0] = TD_L[0:63], to be connected with RD_P[0: 63]

. "rTX[31:0]" means TD_P[31:0] = TD_L[0:31], to be connected with RD_P[0:31].

d. Entry "rTX[63:0] - RX[0:63]" = Normal-to-Mirrored Module connections between two x64 modules with TX lane reversal.
This applies to x64-to-x64 Normal-to-Mirrored combinations.

e. Entry "rTX[31:0] - RX[0:31]" = Normal-to-Mirrored Module connections between lower 32-bit half with TX lane reversal. This
applies to x64-to-x32, x32-to-x64, and x32-to-x32 Normal-to-Mirrored combinations.

The defined bump matrices can achieve optimal skew between bump matrices of differing depths,
and the worst-case trace-reach skews are expected to be within the maximum lane-to-lane skew limit
for the corresponding data rates as defined in Section 5.3 and Section 5.4.

Figure 5-38 and Figure 5-39 show examples of normal and mirrored x64-to-x32 and x32-to-x32
Advanced Package Module connections, respectively.

<figure>
<figcaption>Figure 5-38. Example of Normal and Mirrored x64-to-x32 Advanced Package Module Connection</figcaption>

x64 Normal

x64 Normal

VSS

VS5

vccio

vccio

VSS

VSS

vccio

vccio

V55

VSS

VSS

VSS

vccio

vccio

VSS

rxcksbRD

rxcksb

vccio

rxdatasb

rxdatasbRD

txdatasbRD

txdatasb

vccio

txcksb

txcksbRD

rxdata29

rxdata14

rxdataRD0

rxdata28

rxdata13

rxdata30

rxdata15

VSS

vccio

vccio

rxdata12

VSS

rxdata31

VSS

rxdata0

VSS

rxdata27

rxdata11

rxdat RD1

rxdata16

rxda a1

rxdata26

rxdata10

VIS

rxdata17

VS

vccio

rxdata25

rxdata9

rxcl RD

rxdata18

rxda

a2

VSS

rxvldRD

rxdata24

rxdata8

VSS

rxcken

rxdata19

rxda

a3

rxvld

VSS

rxdata7

rxckp

rxdata20

VS

rxtrk

rxdata23

rxdata6

v.

rxdata21

rxda

a4

VSS

vccio

rxdata22

rxdata5

vccfwdio

vccfwdio

vccf
dio

vccfwdio

vccfv

dio

vccio

txdata21

vccio

txdata5

txdata22

V.

VS

txdata4

txdata20

txckp

txdata6

txdata23

txt

k

VSS

txdata19

txckn

VSS

txdata7

VSS

txv d

txdata3

txdata18

txckRD

txdata8

txdata24

txvl

RD

VS

txdata2

txdata17

vccio

txdata9

txdata25

VI

vccio

vccio

vccio

vccio

vccio

txdata10

txdata26

txdata1

txdata16

txdataRD1

txdata11

txdata27

VS

txdata0

VSS

txdata31

VSS

txdata12

VSS

VSS

VSS

txdata15

txdat 30

txdata13

txdata28

txdata DO

txdata14

txdat 29

vccio

vccio

vcdo

vccio

vcalo

vcci

vccio

vcci

vccio

vccio

Die Edge

Die Edge

De Edge

vccfwdio

vccfwdio

vcdo

vccio

vcdo

vccio

vccio

vccig

vccfwa.

vccfwdio

vccfw

io

vccfwdio

vccfw

lio

vccio

vccio

vccio

vccio

vccfwdio

vccfwdio

vccfwdio

rxdata5

rxdata22

txdata31

txdata14

txdat: RDO

txdataRD0

txdat 14

txdata31

rxdata22

rxdata5

rxdat 4

rxdata21

VSS

txdata30

txdata13

txdata 13

txdata30

VSS

rx Nata21

rxdata4

rxdata6

rxdata23

txdataRD1

txdata15

VS

VSS

txdata15

txdataRD1

rxdata23

rxdata6

VSS

VSS

rxcko

txdata29

txdata12

txdata12

txdata29

rxckp

VSS

VSS

rxdata7

VSS

VSS

VSS

txdata0

txdata0

VSS

VSS

VS5

rxdata7

rxdat 3

rxdata20

rxck

txdata28

txdata11

txdata11

txcata28

rxckn

rxdata20

rxdata3

rxdata8

rxdata24

txvldRD

txdata16

txdata1

txdata1

txdata16

txvldRD

rxdata24

data8

rxdat
2

rxdata19

rxckHD

txdata27

txdata10

txdata10

txdata.

rxckRD

rxdata19

rxdata2

vccfwdio

vccfwdio

vccio

vccio

vccio

vccio

vccio

vccio

vccfwdio

vccfwdı

VSS

rxdata18

rxtr

VSS

txdata9

txdata9

VSS

rxtrk

rxdata18

VSS

rxdata9

rxdata25

txvld

txdata17

txdata2

txdata2

txdata17

txvld

rxdata25

rxdata9

rxdat 1

rxdata17

VSS

txdata26

VSS

VSS

txdata26

VSS

rxdata17

xdata1

VSS

rxdata26

VSS

txdata18

txdata3

txdata3

txdata18

SS

rxdata26

VSS

rxdata0

rxdata16

rxvl

txdata25

txdata8

txdata8

txdata25

rxvld

rxdata16

rxdata0

rxdata10

rxdata27

txtrk

txdata19

VSS

VSS

txdata19

txtrk

rxdata27

rxdata10

VSS

VSS

rxvid D

txdata24

txdata7

txdata7

txdata24

rxvldRD

VSS

VSS

rxdata11

rxdata28

txckRD

V55

txdata4

txdata4

VSS

txckRD

rxdata28

rxdata11

rxdataRD0

rxdata15

rxdataRD1

VSS

txdata6

txdata6

VSS

xdataRD1

rxdata15

rxdataRD0

rxdata12

rxdata29

txckn

txdata20

vccio

vccio

txdata20

txckn

rxdata29

rxdata12

vccio

rxdata14

VSS

txdata23

txdata5

txdata5

txdata23

Ş

rxdata14

vccio

rxdata13

rxdata30

txckp

txdata21

VSS

VSS

txdata21

txckp

rxdata30

rxdata13

vccio

vccio

rxdata31

txdata22

VSS

VSS

txdata22

rxdata31

vccio

vccio

txcksbRD

txcksb

VSS

txdatasb

txdatasbRD

txdatasbRD

txdatasb

VSS

txcksb

txcksbRD

rxdatasbRD

rxdatasb

vccio

rxcksb

rxcksbRD

rxcksbRD

rxcksb

vccio

rxdatasb

rxdatasbRD

VSS

vccio

vccio

VSS

VSS

VSS

VSS

vccio

vccio

VSS

VSS

VSS

vccio

vccio

VSS

VSS

vccio

vccio

VSS

VSS

VSS

vccio

vccio

VSS

VSS

VSS

VSS

vccio

vccio

VSS

x32 Normal

x32 Mirrored w/Lane Reversal

</figure>

<table>
<tr>
<th colspan="10"></th>
</tr>
<tr>
<th>VSS</th>
<th></th>
<th>VSS</th>
<th></th>
<th>vccio</th>
<th></th>
<th>vccio</th>
<th></th>
<th>VSS</th>
<th></th>
</tr>
<tr>
<th></th>
<th>VSS</th>
<th></th>
<th>vccio</th>
<th></th>
<th>vccio</th>
<th></th>
<th>VSS</th>
<th></th>
<th>VSS</th>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td></td>
<td>rxcksbRD</td>
<td></td>
<td>rxcksb</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdatasb</td>
<td></td>
<td>rxdatasbRD</td>
</tr>
<tr>
<td>txdatasbRD</td>
<td></td>
<td>txdatasb</td>
<td></td>
<td>vccio</td>
<td></td>
<td>txcksb</td>
<td></td>
<td>txcksbRD</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>rxdata29</td>
<td></td>
<td>rxdata14</td>
<td></td>
<td>rxdataRD0</td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>rxdata28</td>
<td></td>
<td>rxdata13</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>rxdata30</td>
<td></td>
<td>rxdata15</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td></td>
<td></td>
<td>vccio</td>
<td></td>
<td></td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdata12</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata31</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata0</td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>rxdata27</td>
<td></td>
<td>rxdata11</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>r dataRD1</td>
<td></td>
<td>rxdata16</td>
<td></td>
<td>data1</td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>rxdata26</td>
<td></td>
<td>rxdata10</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata17</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdata25</td>
<td></td>
<td>rxdata9</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>rxckRD</td>
<td></td>
<td>rxdata18</td>
<td></td>
<td>rxdata2</td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td></td>
<td></td>
<td>rxvldRD</td>
<td></td>
<td>rxdata24</td>
<td></td>
<td>rxdata8</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxckn</td>
<td></td>
<td>rxdata19</td>
<td></td>
<td>rxdata3</td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td>rxv)</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxda a7</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>rxckp</td>
<td></td>
<td>rxdata20</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td>xtrk</td>
<td></td>
<td>rxdata23</td>
<td></td>
<td>data6</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata21</td>
<td></td>
<td>rxdata4</td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td></td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdata22</td>
<td></td>
<td>rxdata5</td>
<td></td>
</tr>
<tr>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
<td></td>
<td>vccfwdio</td>
</tr>
<tr>
<td>vccio</td>
<td></td>
<td>txdata21</td>
<td></td>
<td>vccio</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata5</td>
<td></td>
<td>txdata22</td>
<td></td>
<td>VSS</td>
<td></td>
<td></td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>txdata4</td>
<td></td>
<td>txdata20</td>
<td></td>
<td>txckp</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata6</td>
<td></td>
<td>txdat 23</td>
<td></td>
<td>txtrk</td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>txdata19</td>
<td></td>
<td>txckn</td>
<td></td>
<td>VSS</td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata7</td>
<td></td>
<td>ISS</td>
<td></td>
<td>txvld</td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td>txdata3</td>
<td></td>
<td>txdata18</td>
<td></td>
<td>txckRD</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata8</td>
<td></td>
<td>txdata24</td>
<td></td>
<td>txvldRD</td>
<td></td>
<td></td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>txdata2</td>
<td></td>
<td>txdata17</td>
<td></td>
<td>vccio</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata9</td>
<td></td>
<td>txdata25</td>
<td></td>
<td>VSS</td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vCC</td>
<td></td>
<td>vccio</td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata10</td>
<td></td>
<td>txdata26</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td>txdata1</td>
<td></td>
<td>txdat 16</td>
<td></td>
<td>txdataRD1</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata11</td>
<td></td>
<td>txdata27</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>txdata0</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata31</td>
<td></td>
<td>VSS</td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata12</td>
<td></td>
<td>VSS</td>
<td></td>
<td></td>
<td></td>
<td>VSS</td>
<td></td>
<td></td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>txdata15</td>
<td></td>
<td>txdata36</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata13</td>
<td></td>
<td>txdata28</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td>txdataRD0</td>
<td></td>
<td>txdata14</td>
<td></td>
<td>txdata29</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>AIO</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
</tr>
<tr>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td>Die</td>
<td>Edg</td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
</table>

<figure>
<figcaption>Figure 5-39. Example of Normal and Mirrored x32-to-x32 Advanced Package Module Connection</figcaption>

x32 Normal

x32 Normal

VSS

VSS

vccio

vccio

VSS

VSS

VSS

vccio

vccio

VSS

VSS

vccio

vccio

VSS

VSS

VSS

vccio

vccio

VSS

VSS

VSS

VSS

vccio

vccio

VSS

VSS

VSS

vccio

vccio

VSS

rxcksbRD

rxcksb

vccio

rxdatasb

rxdatasbRD

rxcksbRD

rxcksb

vccio

rxdatasb

rxdatasbRD

txdatasbRD

txdatasb

VSS

txcksb

txcksbRD

txdatasbRD

txdatasb

VSS

txcksb

txcksbRD

VSS

txdata22

rxdata31

vccio

vccio

VSS

txdata22

rxdata31

vccio

vccio

VSS

txdata21

txckp

rxdata30

rxdata13

VSS

txdata21

txckp

rxdata30

rxdata13

txdata5

txdata23

Ss

rxdata14

vccio

txdata5

txdata23

VSS

rxdata14

vccio

vccio

txdata20

txckn

rxdata29

rxdata12

vccio

txdata20

txckn

rxdata29

rxdata12

txdata6

VSS

rxda aRD1

rxdata15

rxdataRD0

txdata6

VSS

/xdataRD1

rxdata15

rxdataRD0

txdata4

VSS

txckRD

rxdata28

rxdata11

txdata4

VSS

txckRD

rxdata28

rxdata11

txdata7

txdata24

rxv dRD

VSS

VSS

txdata7

txdata24

rxvldRD

VSS

VSS

VSS

txdata19

txtrk

rxdata27

rxdata10

VSS

txdata19

txtrk

rxdata27

rxdata10

txdata8

txdata25

n vid

rxdata16

rxdata0

txdata8

txdata25

rxvld

rxdata16

rxdata0

txdata3

txdata18

VSS

rxdata26

VSS

txdata3

txdata18

SS

rxdata26

VSS

VSS

txdata26

SS

rxdata17

rxq ata1

VSS

txdata26

VSS

rxdata17

ry ata1

txdata2

txdata17

txvld

rxdata25

rxdata9

txdata2

txdata17

txvld

rxdata25

rxdata9

txdata9

VSS

n trk

rxdata18

SS

txdata9

VSS

rxtrk

rxdata18

VSS

vccio

vccio

vccio

vccfwdio

vccfwdio

vccio

vccio

vccio

vccfwdio

vccfwdir

txdata10

txdata27

rx

KRD

rxdata19

rxd ata2

txdata10

txdata _7

rxckRD

rxdata19

$r x d a t a 2$

txdata1

txdata16

txvldRD

rxdata24

rxdata8

txdata1

txdata16

txvldRD

rxdata24

rx ata8

txdata11

txdata28

DEkn

rxdata20

rxdata3

txdata11

txdata28

rxckn

rxdata20

rxdata3

txdata0

VSS

VSS

VSS

rxdata7

txdata0

VSS

VSS

VSS

rxdata7

txdata12

txdata29

rkp

VSS

SS

$t x d a t a 1 2$

cxdata29

rxckp

VSS

VSS

txdata15

txdataRD1

rxdata23

rxdata6

VS.

txdata15

txdataRD1

rxdata23

rxdata6

txdata13

txdata30

SS

rxdata21

rxd ata4

txdata13

txdata30

VSS

ry Jata21

rxdata4

txda aRDO

txdata14

txdata31

rxdata22

rxdata5

txdataRD

txdata14

txdata31

$r \times d a t a 2 2$

rxdata5

vccio

vccio

vcc

wdio

vccfwdio

vcc wdio

vccio

vccio

vccfwdio

vccfwdio

vccfwdio

votio

vccio

vcci

vccfwdio

vccfwdio

vccio

uccio

vccio

vccfw Mo

vccfwdio

Die Edge

Die Edge

Die Edge

Die Edg

vccfwdio

vccfwdio

vicio

vccio

vocio

vccio

ccio

vccio

vouwdio

vccfwdio

vccf vdio

vccfwdio

vccfw dic

vccio

vccio

vccio

vccio

vccfwdio

vccfwdio

vccfwdio

rxdata5

rxdata22

txdata31

txdata14

txda aRDO

txdataRD0

txda14

$r x d a t a 2$

rxdata5

rxd

ta4

rxdata21

VSS

txdata30

txdata13

txdata13

$\mathrm { t r d a t a } 3 1$

VSS

rxdata21

rxdata4

rxdata6

rxdata23

txdataRD1

txdata15

IS

VSS

txdata1.

txdataRD1

$r x d a t a 2 3$

$r x d a t a 6$

VIS

VSS

rxcko

txdata29

txdata12

txdata12

txdata29

$r x c k p$

VSS

rxdata7

VSS

VSS

VSS

txdata0

txdata0

VSS

VSS

VSS

$r x d a t a 7$

rxd

ta3

rxdata20

rxck

txdata28

txdata11

txdata11

txouta28

$r x c k n$

rxdata20

rxdata3

rxdata8

rxdata24

txvldRD

txdata16

txdata1

txdata1

txdata16

txvldRD

rxdata24

xdata8

rxd: ta2

rxdata19

rxck
D

txdata27

txdata10

txdata10

$t x d a t a$ 7

rxckRD

rxdata19

rxdata2

vccfwdio

vccfwdio

vccio

vccio

vccio

vccio

vccio

vccio

vccfwdio

vccfwio

VIS

rxdata18

rxtik

VSS

txdata9

txdata9

VSS

rxtrk

rxdata18

VSS

rxdata9

rxdata25

txvld

txdata17

txdata2

txdata2

txdata17

txvld

rxdata25

rxdata9

rxd: ta1

rxdata17

VS

txdata26

VSS

VSS

VSS

rxdata17

xdata1

VSS

rxdata26

VSS

txdata18

txdata3

txdata3

$\begin{array}{} { \text { thata a } 1 6 } \\ { \text { txdata } 1 8 } \end{array}$

rxdata26

VSS

rxdata0

rxdata16

rxvid

txdata25

txdata8

txdata8

txdata25

rxvld

rxdata16

rxdata0

rxdata10

rxdata27

txtrk

txdata19

VSS

VSS

txdata19

txtrk

rxdata27

$r x d a t a 1 0$

VSS

VSS

rxvlaRD

txdata24

txdata7

txdata7

txdata24

rxvldRD

VSS

VSS

rxdata11

rxdata28

txckRD

VSS

txdata4

txdata4

VSS

txckRD

rxdata28

rxdata11

rxdataRD0

rxdata15

rxdata RD1

VSS

txdata6

txdata6

VSS

dataRD1

rxdata15

rxdataRD0

rxdata12

rxdata29

txckn

txdata20

vccio

vccio

txdata20

txckn

rxdata29

rxdata12

vccio

rxdata14

VS

txdata23

txdata5

txdata5

txdata23

ES

rxdata14

vccio

rxdata13

rxdata30

txckp

txdata21

VSS

VSS

txdata21

txckp

rxdata30

rxdata13

vccio

vccio

rxdata31

txdata22

VSS

VSS

txdata22

rxdata31

vccio

vccio

txcksbRD

txcksb

VSS

txdatasb

txdatasbRD

txdatasbRD

txdatasb

VSS

txcksb

txcksbRD

rxdatasbRD

rxdatasb

vccio

rxcksb

rxcksbRD

rxcksbRD

rxcksb

vccio

rxdatasb

rxdatasbRD

VSS

vccio

vccio

VSS

VSS

VSS

VSS

vccio

vccio

VSS

VSS

VSS

vccio

vccio

VSS

VSS

vccio

vccio

VSS

VSS

VSS

vccio

vccio

VSS

VSS

VSS

VSS

vccio

vccio

VSS

x32 Normal

x32 Mirrored w/Lane Reversal

</figure>

Although the depth of the bump map for 48 GT/s and 64 GT/s is greater than that for lower data
rates, the module width and signal exit order remain unchanged. As a result, the bump maps for 48
GT/s and 64 GT/s are interoperable with those for lower speeds.

### 5.7.2.5 Module Naming of Advanced Package Modules

This section describes the Module naming convention of x64 and x32 Advanced Package modules in a
multi-module configuration.

The Module naming is defined to help with connecting the Modules deterministically which, in turn,
will help minimize the multiplexing requirements in the Multi-module PHY Logic (MMPL).

The naming of M0, M1, M2, and M3 will apply to 1, 2, or 4 Advanced Package modules that are
aggregated through the MMPL.

Figure 5-40 shows the naming convention for 1, 2, or 4 Advanced Package Modules when they are
connected to their "Standard Die Rotate" Module counterparts that have same number of Advanced
Package Modules.

Note:
The double-ended arrows in Figure 5-40 through Figure 5-43 indicate Module-to-
Module connections.

<figure>
<figcaption>Figure 5-40. Naming Convention for One-, Two-, and Four-module Advanced Package Paired with "Standard Die Rotate" Configurations</figcaption>

$R x$
(x64)

Rx
(x64)

$R x$
(x64)

Rx
(x64)

$R x$
(x64)

Rx
(x64)

Rx
(x64)

MO

MO

M1

M1

MO

M2

M̧3

$T x$
(x64)

$T x$
$\left( x 6 4 \right)$

Tx
(x6 )

$T x$
(x64)

TX
$\left( \times 6 \right)$

Tx
$\left( x 6 4 \right)$

TX
(x6 )

(tax)
1

(t|9x)
T:

$\left( \log x \right)$
TX

(tax)
T

( 9x)

(tex)
1

( 9x)
T:

T:

OW

M1

OW

M3

M2

OW

M1

(x64)
XH

(x64)
Rx

(x64)
Rx

(x64)
Rx

(×64)
Rx

(x64)
Rx

(79X)
Rx

</figure>

Figure 5-41 shows the naming convention for 1, 2, or 4 Advanced Package modules when they are
connected to their "Mirrored Die Rotate" counterparts with the same number of Advanced Package
modules.

<figure>
<figcaption>Figure 5-41. Naming Convention for One-, Two-, and Four-module Advanced Package Paired with "Mirrored Die Rotate" Configurations</figcaption>

$R x$
(x64)

Rx
(x64)

Rx

Rx
(x64)

Rx
(x64)

Rx
(x64)

Rx
(x64)

(x64)

H

MO

MO

M1

M1

MO

M2

M̧3

Tx
(x64)

Tx
(x64)

Tx
(x6)

Tx
(x64)

TX
(x6 )

Tx
(x64)

TX
(x6)

(xps
xT

(xes)
1X

(xe :)
ET

[xed
XT

(xe-)
XT

(xed
$1 ^ { x }$

(xeso
xT

WO

WO

WJ

IM

OM

WS

W3

(xe4)
хЯ

(Aax)
хЯ

(x2)
$B ^ { x }$

(xe9)
ХЯ

(xe4)
$8 x$

(xe4)
$8 x$

(xp=)
хЯ

</figure>

Table 5-22 summarizes the connections between the combinations shown in Figure 5-40 and
Figure 5-41.

<table>
<caption>Table 5-22. Summary of Advanced Package Module Connection Combinations with Same Number of Modules on Both Sides</caption>
<tr>
<th>Advanced Package Module Connections (Same # of Modules on Both Sides)</th>
<th>Standard Die Rotate Counterpart</th>
<th>Mirrored Die Rotate Counterpart</th>
</tr>
<tr>
<td>$1 \quad - \quad x 1$</td>
<td>· MO - MO</td>
<td>· $M O \quad - \quad M O$</td>
</tr>
<tr>
<td rowspan="2">$2 \quad - \quad x 2$</td>
<td>· MO - M1</td>
<td>· $M O \quad - \quad M O$</td>
</tr>
<tr>
<td>· $M 1 \quad - \quad M O$</td>
<td>· M1 - M1</td>
</tr>
<tr>
<td rowspan="4">×4 - x4</td>
<td>· MO - M2</td>
<td>· $M O \quad - \quad M O$</td>
</tr>
<tr>
<td>· M1 - M3</td>
<td>· $M 1 \quad - \quad M 1$</td>
</tr>
<tr>
<td>· M3 - M1</td>
<td>· $M 2 \quad - \quad M 2$</td>
</tr>
<tr>
<td>· M2 - MO</td>
<td>· M3 - M3</td>
</tr>
</table>

Figure 5-42 shows the naming convention for 1, 2, or 4 Advanced Package modules when they are
connected to their "Standard Die Rotate" counterparts that have a different number of Advanced
Package modules.

<figure>
<figcaption>Figure 5-42. Examples for Advanced Package Configurations Paired with "Standard Die Rotate" Counterparts, with a Different Number of Modules</figcaption>

Rx
(x64)

$R x$
(x64)

Rx
(x64)

$R x$
(x64)

$R x$
(x64)

$R x$
(x64)

Rx
(x64)

$R x$
(x64)

Rx
(x64)

$R x$
(x64)

MO

M1

M1

MO

M2

M3

M1

MO

M2

M3

TX
(x6 )

$T x$
(x64)

T
(x6|)

Tx
(x64

$T x$
(x64)

$T x$
(x64)

$T x$
(x64)

TX
(x6)

$T x$
(x64)

Tx
(x64)

(9%)
KL

(|9x)
KI

(tex)
1

(|9x)
1

MO

M1

MO

0W

(x64)
Rx

(x64)
Rx

(x64)
Rx

(19x)
Rx

</figure>

Figure 5-43 shows the naming convention for 1, 2, or 4 Advanced Package modules when they are
connected to their "Mirrored Die Rotate" counterparts that have a different number of Advanced
Package modules.

<figure>
<figcaption>Figure 5-43. Examples for Advanced Package Configurations Paired with "Mirrored Die Rotate" Counterparts, with a Different Number of Modules</figcaption>

Rx
(x64)

Rx
(x64)

Rx
(x64)

Rx
(x64)

Rx
(x64)

Rx
(x64)

Rx
(x64)

Rx
(x64)

Rx
(x64)

Rx
(x64)

Rx
(x64)

M0

MO

M1

M1

MO

M2

M3

M1

MO

M2

M3

TK
(x6 4)

TX
(x6-
)

Tx
(x64)

T
(x6 )

Tx
(x64

$T x$
(x64)

Tx
(x64)

Tx
(x64)

TX
(x6.
)

$T x$
$\left( \times 6 4 \right)$

Tx
$\left( x 6 4 \right)$

(x64)
x

(xe 6)
KT

(xe
J

[xed
XT

(xe
KT

ST

O'W

WO

WO

WJ

WO

(x64)

(xev)
хЯ

(XP)
ХЯ

(xe+)
BX

(xe4)
ХЯ

Rx

</figure>

Table 5-23 summarizes the connections between the combinations shown in Figure 5-42 and
Figure 5-43.

<table>
<caption>Table 5-23. Summary of Advanced Package Module Connection Combinations with Different Number of Modules on Both Sides</caption>
<tr>
<th>Advanced Package Module Connections (Different # of Modules on Both Sides)</th>
<th>Standard Die Rotate Counterpartª</th>
<th>Mirrored Die Rotate Counterpartª</th>
</tr>
<tr>
<td rowspan="2">×2 - x1</td>
<td>· $M O \quad - \quad M O$</td>
<td>· $M O \quad - \quad M O$</td>
</tr>
<tr>
<td>· M1 - NC</td>
<td>· $M 1 \quad - \quad N C$</td>
</tr>
<tr>
<td rowspan="4">$4 \quad - \quad x 2$</td>
<td>· $M O \quad - \quad M O$</td>
<td>· $M O \quad - \quad M 1$</td>
</tr>
<tr>
<td>· $M 1 \quad - \quad M 1$</td>
<td>· $M 1 \quad - \quad M O$</td>
</tr>
<tr>
<td>· M3 - NC</td>
<td>· $M 2 \quad - \quad N C$</td>
</tr>
<tr>
<td>· $M 2 \quad - \quad N C$</td>
<td>· M3 - NC</td>
</tr>
<tr>
<td rowspan="4">$4 \quad - \quad x 1$</td>
<td>· $M O \quad - \quad M O$</td>
<td>· $M O \quad - \quad M O$</td>
</tr>
<tr>
<td>· $M 1 \quad - \quad N C$</td>
<td>· $M 1 \quad - \quad N C$</td>
</tr>
<tr>
<td>· M3 - NC</td>
<td>· $M 2 \quad - \quad N C$</td>
</tr>
<tr>
<td>· M2 - NC</td>
<td>· M3 - NC</td>
</tr>
</table>

a. NC indicates no connection.

### 5.7.3 Standard Package

Interconnect channel should be designed with 50-ohm characteristic impedance. Insertion loss and
crosstalk for requirement at Nyquist frequency with Receiver termination is defined in Table 5-24.

<table>
<caption>Table 5-24. IL and Crosstalk for Standard Package: With Receiver Termination Enabled</caption>
<tr>
<th>Data Rate</th>
<th>4, 8 GT/s</th>
<th>12, 16 GT/s</th>
<th>24, 32 GT/s</th>
</tr>
<tr>
<td>VTF Loss (dB)a b c</td>
<td>$L \left( 0 \right) > - 4 . 5$ $L \left( f _ { N } \right) > - 7 . 5$</td>
<td>$L \left( 0 \right) > - 4 . 5$ $L \left( f _ { N } \right) > - 6 . 5$</td>
<td>$L \left( 0 \right) > - 4 . 5$ $L \left( f _ { N } \right) > - 7 . 5$</td>
</tr>
<tr>
<td>VTF Crosstalk (dB)</td>
<td>$X T \left( f _ { N } \right) < 3 * L \left( f _ { N } \right)$ - 11.5 and $x T \left( f _ { N } \right) < - 2 5$</td>
<td>$X T \left( f _ { N } \right) < 3 * L \left( f _ { N } \right) - 1 1 . 5$ $x T \left( f _ { N } \right) < - 2 5$</td>
<td>$X T \left( f _ { N } \right) < 2 . 5 * L \left( f _ { N } \right) - 1 0$ and $X T \left( f _ { N } \right) < - 2 6$</td>
</tr>
</table>

a. Voltage Transfer Function for 4 GT/s and 8 GT/s (Tx: 30 ohm / 0.3pF; Rx: 50 ohm / 0.3pF).

b. Voltage Transfer Function for 12 GT/s and 16 GT/s (Tx: 30 ohm / 0.2pF; Rx: 50 ohm / 0.2pF).

c. Voltage Transfer Function for 24 GT/s and 32 GT/s (Tx: 30 ohm / 0.125pF; Rx: 50 ohm / 0.125pF).

IL and crosstalk for requirement at Nyquist frequency without Receiver termination is defined by
Table 5-25. Loss and crosstalk specifications between DC and Nyquist fy follow the same methodology
defined in Section 5.7.2.1.

<table>
<caption>Table 5-25. IL and Crosstalk for Standard Package: No Rx Termination</caption>
<tr>
<th>Data Rate</th>
<th>4-12 GT/s</th>
<th>16 GT/s</th>
</tr>
<tr>
<td>VTF Loss (dB)a b</td>
<td>$L \left( f _ { N } \right) > - 1 . 2 5$</td>
<td>$L \left( f _ { N } \right) > - 1 . 1 5$</td>
</tr>
<tr>
<td>VTF Crosstalk (dB)</td>
<td>$X T \left( f _ { N } \right) < 7 * L \left( f _ { N } \right) - 1 2 . 5$ and $\check { X } T \left( f _ { N } \right) < - 1 5$</td>
<td>$X T \left( f _ { N } \right) < 4 * L \left( f _ { N } \right) - 1 3 . 5$ $x \left( f _ { N } \right) < - 1 7$</td>
</tr>
</table>

a. Voltage Transfer Function for 4 GT/s and 8 GT/s (Tx: 30 ohm / 0.3pF; Rx: 0.2 pF).

b. Voltage Transfer Function for 12 GT/s and 16 GT/s (Tx: 30 ohm / 0.2pF; Rx: 0.2 pF).

<table>
<caption>Table 5-26. Standard Package Module Signal List (Sheet 1 of 2)</caption>
<tr>
<th>Signal Name</th>
<th>Count</th>
<th>Description</th>
</tr>
<tr>
<td colspan="3">Data</td>
</tr>
<tr>
<td>TXDATA [ 15 : 0]</td>
<td>16</td>
<td>Transmit Data</td>
</tr>
<tr>
<td>TXVLD</td>
<td>1</td>
<td>Transmit Data Valid; Enables clocking in corresponding module</td>
</tr>
<tr>
<td>TXTRK</td>
<td>1</td>
<td>Transmit Track signal</td>
</tr>
<tr>
<td>TXCKP</td>
<td>1</td>
<td>Transmit Clock Phase-1</td>
</tr>
<tr>
<td>TXCKN</td>
<td>1</td>
<td>Transmit Clock Phase-2</td>
</tr>
<tr>
<td>RXDATA [ 15 : 0]</td>
<td>16</td>
<td>Receive Data</td>
</tr>
<tr>
<td>RXVLD</td>
<td>1</td>
<td>Receive Data Valid; Enables clocking in corresponding module</td>
</tr>
<tr>
<td>RXTRK</td>
<td>1</td>
<td>Receive Track</td>
</tr>
<tr>
<td>RXCKP</td>
<td>1</td>
<td>Receive Clock Phase-1</td>
</tr>
<tr>
<td>RXCKN</td>
<td>1</td>
<td>Receive Clock Phase-2</td>
</tr>
<tr>
<td colspan="3">Sideband</td>
</tr>
<tr>
<td>TXDATASB</td>
<td>1</td>
<td>Sideband Transmit Data</td>
</tr>
<tr>
<td>RXDATASB</td>
<td>1</td>
<td>Sideband Receiver Data</td>
</tr>
<tr>
<td>TXCKSB</td>
<td>1</td>
<td>Sideband Transmit Clock</td>
</tr>
</table>

<table>
<caption>Table 5-26. Standard Package Module Signal List (Sheet 2 of 2)</caption>
<tr>
<th>Signal Name</th>
<th>Count</th>
<th>Description</th>
</tr>
<tr>
<td>RXCKSB</td>
<td>1</td>
<td>Sideband Receive Clock</td>
</tr>
<tr>
<td colspan="3">Power and Voltage</td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>Ground Reference</td>
</tr>
<tr>
<td>VCCIO</td>
<td></td>
<td>I/O supply</td>
</tr>
<tr>
<td>VCCAON</td>
<td></td>
<td>Always on Aux supply (sideband)</td>
</tr>
</table>

#### 5.7.3.1 x16 Standard Package Module Bump Map

Figure 5-44 and Figure 5-46 show the reference bump matrices for x16 (one module) and x32 (two
module) Standard Packages, respectively, for data rates up to 32 GT/s.

It is strongly recommended to follow the bump matrices provided in Figure 5-44 for one module and
Figure 5-46 for two module Standard Packages. The lower left corner of the bump map will be
considered "origin" of a bump matrix.

Signal exit order for x16 and x32 Standard Package bump matrices are shown in Figure 5-45 and
Figure 5-47, respectively.

The following rules must be followed for Standard Package bump matrices:

· The signals within a column must be preserved. For example, for a x16 (one module Standard
Package) shown in Figure 5-44, Column 1 must contain the signals: txdata0, txdata1,
txdata4, txdata5, and txdatasb.

· The signals must exit the bump field in the order shown in Figure 5-45. Layer 1 and Layer 2 are
two different signal routing layers in a Standard Package.

It is strongly recommended to follow the supply and ground pattern shown in the bump matrices. It
must be ensured that sufficient supply and ground bumps are provided to meet channel
characteristics (FEXT and NEXT) and power-delivery requirements.

The following rules must be followed for instantiating multiple modules of Standard Package bump
matrix:

· When looking at a die such that the UCIe Modules are on the south side, Tx should always
precede Rx within a module along the die's edge when going from left to right.

· When instantiating multiple modules, the modules must be stepped in the same orientation and
abutted. Horizontal or vertical mirroring is not permitted.

If more Die Edge Bandwidth density is required, it is permitted to stack two modules before abutting.
If two modules are stacked, the package may need to support at least four routing layers for UCIe
signal routing. An example of stacked Standard Package Module instantiations is shown in
Figure 5-46.

. If only one stacked module is instantiated, when looking at a die such that the UCIe Modules are
on the south side, Tx should always precede Rx within a module along the die's edge when going
from left to right.

· When instantiating multiple stacked modules, the modules must be stepped in the same
orientation and abutted. Horizontal or vertical mirroring is not permitted.

Note:
An example of signal routing for stacked module is shown in Figure 5-48.

Figure 5-44. Standard Package Bump Map: x16 interface

<table>
<tr>
<th>Column 0</th>
<th>Column 1</th>
<th>Column 2</th>
<th>Column 3</th>
<th>Column 4</th>
<th>Column 5</th>
<th>Column 6</th>
<th>Column 7</th>
<th>Column 8</th>
<th>Column 9</th>
<th>Column 10</th>
<th colspan="2">Column 11</th>
</tr>
<tr>
<th></th>
<th>txdatasb</th>
<th></th>
<th>txcksb</th>
<th></th>
<th>vccaon</th>
<th></th>
<th>vccaon</th>
<th></th>
<th>rxcksb</th>
<th></th>
<th>rxdatasb</th>
<th></th>
</tr>
<tr>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
</tr>
<tr>
<td>vccio</td>
<td></td>
<td>txdata7</td>
<td></td>
<td>txdata9</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdata8</td>
<td></td>
<td>rxdata6</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata5</td>
<td></td>
<td>txckn</td>
<td></td>
<td>txdata11</td>
<td></td>
<td>rxdata10</td>
<td></td>
<td>rxckp</td>
<td></td>
<td>rxdata4</td>
<td></td>
</tr>
<tr>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata4</td>
<td></td>
<td>txckp</td>
<td></td>
<td>$t x d a t a 1 0$</td>
<td></td>
<td>rxdata11</td>
<td></td>
<td>rxckn</td>
<td></td>
<td>rxdata5</td>
<td></td>
</tr>
<tr>
<td>V55</td>
<td></td>
<td>txdata6</td>
<td></td>
<td>txdata8</td>
<td></td>
<td>V55</td>
<td></td>
<td>rxdata9</td>
<td></td>
<td>rxdata7</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
</tr>
<tr>
<td>vccio</td>
<td></td>
<td>txdata3</td>
<td></td>
<td>txdata13</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdata12</td>
<td></td>
<td>rxdata2</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata1</td>
<td></td>
<td>txvld</td>
<td></td>
<td>txdata15</td>
<td></td>
<td>rxdata14</td>
<td></td>
<td>rxtrk</td>
<td></td>
<td colspan="2">rxdata0</td>
</tr>
<tr>
<td>vccio</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>vccio</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td colspan="2"></td>
</tr>
<tr>
<td></td>
<td>txdata0</td>
<td></td>
<td>txtrk</td>
<td></td>
<td>txdata14</td>
<td></td>
<td>rxdata15</td>
<td></td>
<td>rxvld</td>
<td></td>
<td colspan="2">rxdata1</td>
</tr>
<tr>
<td>V55</td>
<td></td>
<td>txdata2</td>
<td></td>
<td>txdata12</td>
<td></td>
<td>V55</td>
<td></td>
<td>rxdata13</td>
<td></td>
<td>rxdata3</td>
<td colspan="2"></td>
</tr>
</table>

Die Edge

<table>
<caption>Figure 5-45. Standard Package x16 interface: Signal exit order</caption>
<tr>
<th rowspan="3"></th>
<th>Layer 1</th>
<th rowspan="2">Tx Module dule</th>
<th>0</th>
<th>1</th>
<th>2</th>
<th>3</th>
<th>trk</th>
<th>vld</th>
<th>12</th>
<th>13</th>
<th>14</th>
<th>15</th>
<th>15</th>
<th>14</th>
<th>13</th>
<th>12</th>
<th>vld</th>
<th>trk</th>
<th>3</th>
<th>2</th>
<th>1</th>
<th>0</th>
<th rowspan="2">$R x$ Module</th>
</tr>
<tr>
<th>Layer 2</th>
<th>4</th>
<th>5</th>
<th>6</th>
<th>7</th>
<th>ckp</th>
<th>ckn</th>
<th>8</th>
<th>9</th>
<th>10</th>
<th>11</th>
<th>11</th>
<th>10</th>
<th>9</th>
<th>8</th>
<th>ckn</th>
<th>ckp</th>
<th>7</th>
<th>6</th>
<th>5</th>
<th>4</th>
</tr>
<tr>
<td>Sideband</td>
<td></td>
<td></td>
<td colspan="2">txdatasb</td>
<td></td>
<td></td>
<td></td>
<td>txcksb</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>rxcksb</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td colspan="2">rxdatasb</td>
<td></td>
</tr>
</table>

<table>
<caption>Figure 5-46. Standard Package Bump Map: x32 interface</caption>
<tr>
<th>Column 0</th>
<th>Column 1</th>
<th>Column 2</th>
<th>Column 3</th>
<th>Column 4</th>
<th>Column 5</th>
<th>Column 6</th>
<th>Column 7</th>
<th>Column 8</th>
<th>Column 9</th>
<th>Column 10</th>
<th>Column 11</th>
</tr>
<tr>
<th></th>
<th>m2rxdatasb</th>
<th></th>
<th>m2rxcksb</th>
<th></th>
<th>vccaon</th>
<th></th>
<th>m2txcksb</th>
<th></th>
<th>m2txdatasb</th>
<th></th>
<th>vccaon</th>
</tr>
<tr>
<td>m1txdatasb</td>
<td></td>
<td>m1txcksb</td>
<td></td>
<td>vccaon</td>
<td></td>
<td>vccaon</td>
<td></td>
<td>m1rxcksb</td>
<td></td>
<td>m1rxdatasb</td>
<td></td>
</tr>
<tr>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
</tr>
<tr>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
</tr>
<tr>
<td></td>
<td>m2rxdata6</td>
<td></td>
<td>m2rxdata8</td>
<td></td>
<td>V55</td>
<td></td>
<td>m2txdata9</td>
<td></td>
<td>m2txdata7</td>
<td></td>
<td>V55</td>
</tr>
<tr>
<td>m2rxdata4</td>
<td></td>
<td>m2rxckp</td>
<td></td>
<td>m2rxdata10</td>
<td></td>
<td>m2txdata11</td>
<td></td>
<td>m2txckn</td>
<td></td>
<td>m2txdata5</td>
<td></td>
</tr>
<tr>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
</tr>
<tr>
<td>m2rxdata5</td>
<td></td>
<td>m2rxckn</td>
<td></td>
<td>m2rxdata11</td>
<td></td>
<td>m2txdata10</td>
<td></td>
<td>m2txckp</td>
<td></td>
<td>m2txdata4</td>
<td></td>
</tr>
<tr>
<td></td>
<td>m2rxdata7</td>
<td></td>
<td>m2rxdata9</td>
<td></td>
<td>V55</td>
<td></td>
<td>$m 2 t x d a t a 8$</td>
<td></td>
<td>m2txdata6</td>
<td></td>
<td>V55</td>
</tr>
<tr>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
</tr>
<tr>
<td></td>
<td>m2rxdata2</td>
<td></td>
<td>m2rxdata12</td>
<td></td>
<td>V55</td>
<td></td>
<td>m2txdata13</td>
<td></td>
<td>m2txdata3</td>
<td></td>
<td>V55</td>
</tr>
<tr>
<td>m2rxdata0</td>
<td></td>
<td>$m 2 r x t r k$</td>
<td></td>
<td>$n 2 r \times d a t a 1 4$</td>
<td></td>
<td>m2txdata15</td>
<td></td>
<td>$m 2 t x v l d$</td>
<td></td>
<td>$m 2 t x d a t a 1$</td>
<td></td>
</tr>
<tr>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
</tr>
<tr>
<td>m2rxdata1</td>
<td></td>
<td>$m 2 r x v l d$</td>
<td></td>
<td>m2rxdata15</td>
<td></td>
<td>m2txdata14</td>
<td></td>
<td>m2txtrk</td>
<td></td>
<td>m2txdata0</td>
<td></td>
</tr>
<tr>
<td></td>
<td>$m 2 r \times d a t a 3$</td>
<td></td>
<td>$m 2 r x d a t a 1 3$</td>
<td></td>
<td>vccio</td>
<td></td>
<td>$m 2 t x d a t a 1 2$</td>
<td></td>
<td>$m 2 t x d a t a 2$</td>
<td></td>
<td>vccio</td>
</tr>
<tr>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
</tr>
<tr>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>vccio</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>vccio</td>
</tr>
<tr>
<td>vccio</td>
<td></td>
<td>m1txdata7</td>
<td></td>
<td>m1txdata9</td>
<td></td>
<td>vccio</td>
<td></td>
<td>m1rxdata8</td>
<td></td>
<td>m1rxdata6</td>
<td></td>
</tr>
<tr>
<td></td>
<td>m1txdata5</td>
<td></td>
<td>$m 1 t x c k n$</td>
<td></td>
<td>m1txdata11</td>
<td></td>
<td>m1rxdata10</td>
<td></td>
<td>m1rxckp</td>
<td></td>
<td>m1rxdata4</td>
</tr>
<tr>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
</tr>
<tr>
<td></td>
<td>m1txdata4</td>
<td></td>
<td>m1txckp</td>
<td></td>
<td>m1txdata10</td>
<td></td>
<td>m1rxdata11</td>
<td></td>
<td>m1rxckn</td>
<td></td>
<td>m1rxdata5</td>
</tr>
<tr>
<td>V55</td>
<td></td>
<td>m1txdata6</td>
<td></td>
<td>m1txdata8</td>
<td></td>
<td>V55</td>
<td></td>
<td>m1rxdata9</td>
<td></td>
<td>m1rxdata7</td>
<td></td>
</tr>
<tr>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
</tr>
<tr>
<td>vccio</td>
<td></td>
<td>m1txdata3</td>
<td></td>
<td>m1txdata13</td>
<td></td>
<td>vccio</td>
<td></td>
<td>m1rxdata12</td>
<td></td>
<td>m1rxdata2</td>
<td></td>
</tr>
<tr>
<td></td>
<td>m1txdata1</td>
<td></td>
<td>m1txvld</td>
<td></td>
<td>m1txdata15</td>
<td></td>
<td>m1rxdata14</td>
<td></td>
<td>m1rxtrk</td>
<td></td>
<td>m1rxdataO</td>
</tr>
<tr>
<td>vccio</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
<td>vccio</td>
<td></td>
<td>V55</td>
<td></td>
<td>V55</td>
<td></td>
</tr>
<tr>
<td></td>
<td>m1txdataO</td>
<td></td>
<td>m1txtrk</td>
<td></td>
<td>m1txdata14</td>
<td></td>
<td>m1rxdata15</td>
<td></td>
<td>m1rxvld</td>
<td></td>
<td>m1rxdata1</td>
</tr>
<tr>
<td>V55</td>
<td></td>
<td>m1txdata2</td>
<td></td>
<td>m1txdata12</td>
<td></td>
<td>V55</td>
<td></td>
<td>m1rxdata13</td>
<td></td>
<td>m1rxdata3</td>
<td></td>
</tr>
</table>

Die Edge

<table>
<caption>Figure 5-47. Standard Package x32 interface: Signal exit routing</caption>
<tr>
<th rowspan="5"></th>
<th>Layer 1</th>
<th>Tx</th>
<th>0</th>
<th>1</th>
<th>2</th>
<th>3</th>
<th>trk</th>
<th>vld</th>
<th>12</th>
<th>13</th>
<th>14</th>
<th>15</th>
<th>15</th>
<th>14</th>
<th>13</th>
<th>12</th>
<th>vld</th>
<th>trk</th>
<th>3</th>
<th>2</th>
<th>1</th>
<th>0</th>
<th>$R x$</th>
<th></th>
</tr>
<tr>
<td>Layer 2</td>
<td>Module 1</td>
<td>4</td>
<td>5</td>
<td>6</td>
<td>7</td>
<td>ckp</td>
<td>ckn</td>
<td>8</td>
<td>9</td>
<td>10</td>
<td>11</td>
<td>11</td>
<td>10</td>
<td>9</td>
<td>8</td>
<td>ckn</td>
<td>ckp</td>
<td>7</td>
<td>6</td>
<td>5</td>
<td>4</td>
<td>Module 1</td>
<td></td>
</tr>
<tr>
<td>Layer 3</td>
<td>Rx</td>
<td>0</td>
<td>1</td>
<td>2</td>
<td>3</td>
<td>trk</td>
<td>vld</td>
<td>12</td>
<td>13</td>
<td>14</td>
<td>15</td>
<td>15</td>
<td>14</td>
<td>13</td>
<td>12</td>
<td>vld</td>
<td>$\mathrm { t r k }$</td>
<td>3</td>
<td>2</td>
<td>1</td>
<td>0</td>
<td>Tx</td>
<td></td>
</tr>
<tr>
<td>Layer 4</td>
<td>Module 2</td>
<td>4</td>
<td>5</td>
<td>6</td>
<td>7</td>
<td>ckp</td>
<td>ckn</td>
<td>8</td>
<td>9</td>
<td>10</td>
<td>11</td>
<td>11</td>
<td>10</td>
<td>9</td>
<td>8</td>
<td>ckn</td>
<td>ckp</td>
<td>7</td>
<td>6</td>
<td>5</td>
<td>4</td>
<td>Module 2</td>
<td></td>
</tr>
<tr>
<td>Sideband</td>
<td></td>
<td colspan="3">m1txdatasb</td>
<td colspan="3">m2rxdatasb</td>
<td colspan="2">m1txcksb</td>
<td colspan="2">m2rxcksb</td>
<td colspan="2">m2txcksb</td>
<td colspan="2">m1rxcksb</td>
<td colspan="3">m2txdatasb</td>
<td colspan="3">m 1rxdatasb</td>
<td colspan="2">Sideband</td>
</tr>
</table>

<figure>
<figcaption>Figure 5-48. Standard Package cross section for stacked module</figcaption>

Package

Orange - Tx signals on Die 1 talking to Rx on Die 2 in Layer 1

Orange - Tx signals on Die 1 talking to Rx on Die 2 in Layer 2

Blue - Tx signals on Die 2 talking to Rx on Die 1 in Layer 3
Blue - Tx signals on Die 2 talking to Rx on Die 1 in Layer 4
Brown - VCCIO
Green - VSS

</figure>

## IMPLEMENTATION NOTE

Figure 5-49 shows a breakout design reference with the Standard Package channel based on the
bump pitch and on routing design rules.

Figure 5-49.
Standard Package reference configuration

D

I

V

VL

1

1

$S$

$P = D + L + 2 S$

$\mathrm { P } _ { \mathrm { y } }$

$P = \frac { 1 } { 2 } \sqrt { P _ { x } ^ { 2 } + P _ { y } ^ { 2 } }$

V

1

$P$

$P _ { X }$

· 4-row deep breakout per routing layer

· Example $1 : P _ { y } = 1 9 0 . 5 u m ,$ $P _ { x } \approx 1 1 1 . 5 u m ,$ $P \approx 1 1 0 u m$

· Example 2: $P _ { v } = 1 9 0 . 5 u m ,$ $P _ { x } \approx 1 7 7 ,$ $P \approx 1 3 0 u m$

<table>
<caption>Figure 5-50 and Figure 5-51 present recommended bump configurations for Standard Package modules for 48 GT/s and 64 GT/s. As with the Advanced Package configurations, a greater number of power and ground bumps have been integrated to support the increased data rates. Additional bump maps or further optimizations may be introduced in subsequent updates to this specification. To enhance die edge bandwidth density, the UCIe Consortium is investigating the feasibility of bump maps for 48 GT/s and 64 GT/s that have die edge equal to that of 32 GT/s and below. This exploration involves optimizing bump maps and enhancing circuits through improvements in equalization, termination network, skew, jitter, and noise reduction. Figure 5-50. Standard Package Bump Map: 48 GT/s and 64 GT/s x32 Interface</caption>
<tr>
<th>Column 1</th>
<th>Column 2</th>
<th>Column 3</th>
<th>Column 4</th>
<th>Column 5</th>
<th>Column 6</th>
<th>Column 7</th>
<th>Column 8</th>
<th>Column 9</th>
<th>Column 10</th>
<th>Column 11</th>
<th>Column 12</th>
<th>Column 13</th>
<th>Column 14</th>
</tr>
<tr>
<th></th>
<th>rxdatasb2</th>
<th></th>
<th>rxcksb2</th>
<th></th>
<th>vccio</th>
<th></th>
<th>vccinfaon</th>
<th></th>
<th>vccio</th>
<th></th>
<th>txdatasb2</th>
<th></th>
<th>txcksb2</th>
</tr>
<tr>
<td>txdatasb1</td>
<td></td>
<td>txcksb1</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccinfaon</td>
<td></td>
<td>vccio</td>
<td></td>
<td>rxdatasb1</td>
<td></td>
<td>rxdatack1</td>
<td></td>
</tr>
<tr>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td></td>
<td>rxdata6</td>
<td></td>
<td>rxckp</td>
<td></td>
<td>rxdata10</td>
<td></td>
<td>txdata11</td>
<td></td>
<td>txdata8</td>
<td></td>
<td>txdata7</td>
<td></td>
<td>txdata4</td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td></td>
<td>rxdata5</td>
<td></td>
<td>rxckn</td>
<td></td>
<td>rxdata9</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata9</td>
<td></td>
<td>txckn</td>
<td></td>
<td>txdata5</td>
<td></td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>rxdata4</td>
<td></td>
<td>rxdata7</td>
<td></td>
<td>rxdata8</td>
<td></td>
<td>rxdata11</td>
<td></td>
<td>txdata10</td>
<td></td>
<td>txckp</td>
<td></td>
<td>txdata6</td>
<td></td>
</tr>
<tr>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
</tr>
<tr>
<td></td>
<td>rxdata2</td>
<td></td>
<td>rxvld</td>
<td></td>
<td>rxdata14</td>
<td></td>
<td>txdata15</td>
<td></td>
<td>txdata12</td>
<td></td>
<td>txdata3</td>
<td></td>
<td>txdata0</td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td></td>
<td>rxdata1</td>
<td></td>
<td>rxtrk</td>
<td></td>
<td>rxdata13</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>txdata13</td>
<td></td>
<td>txtrk</td>
<td></td>
<td>txdata1</td>
<td></td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>rxdata0</td>
<td></td>
<td>rxdata3</td>
<td></td>
<td>rxdata12</td>
<td></td>
<td>rxdata15</td>
<td></td>
<td>txdata14</td>
<td></td>
<td>txvld</td>
<td></td>
<td>txdata2</td>
<td></td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>txdata4</td>
<td></td>
<td>txdata7</td>
<td></td>
<td>txdata8</td>
<td></td>
<td>txdata11</td>
<td></td>
<td>rxdata10</td>
<td></td>
<td>rxckp</td>
<td></td>
<td>rxdata6</td>
<td></td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata9</td>
<td></td>
<td>rxckn</td>
<td></td>
<td>rxdata5</td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata5</td>
<td></td>
<td>txckn</td>
<td></td>
<td>txdata9</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata6</td>
<td></td>
<td>txckp</td>
<td></td>
<td>txdata10</td>
<td></td>
<td>rxdata11</td>
<td></td>
<td>rxdata8</td>
<td></td>
<td>rxdata7</td>
<td></td>
<td>rxdata4</td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
</tr>
<tr>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>txdata0</td>
<td></td>
<td>txdata3</td>
<td></td>
<td>txdata12</td>
<td></td>
<td>txdata15</td>
<td></td>
<td>rxdata14</td>
<td></td>
<td>rxvld</td>
<td></td>
<td>rxdata2</td>
<td></td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata13</td>
<td></td>
<td>rxtrk</td>
<td></td>
<td>rxdata1</td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata1</td>
<td></td>
<td>txtrk</td>
<td></td>
<td>txdata13</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata2</td>
<td></td>
<td>txvld</td>
<td></td>
<td>txdata14</td>
<td></td>
<td>rxdata15</td>
<td></td>
<td>rxdata12</td>
<td></td>
<td>rxdata3</td>
<td></td>
<td>rxdata0</td>
</tr>
</table>

Die Edge

<table>
<caption>Figure 5-51. x16 Standard Package Potential Bump Map: 48 GT/s and 64 GT/s x16</caption>
<tr>
<th></th>
<th>Column 1</th>
<th>Column 2</th>
<th>Column 3</th>
<th>Column 4</th>
<th>Column 5</th>
<th>Column 6</th>
<th>Column 7</th>
<th>Column 8</th>
<th>Column 9</th>
<th>Column 10</th>
<th>Column 11</th>
<th>Column 12</th>
<th colspan="3">Column 13 Column 14</th>
</tr>
<tr>
<th></th>
<th></th>
<th>txdatasb1</th>
<th></th>
<th>txcksb1</th>
<th></th>
<th>vccio</th>
<th></th>
<th>vccinfaon</th>
<th></th>
<th>vccio</th>
<th></th>
<th>rxdatasb1</th>
<th></th>
<th>rxdatack1</th>
<th></th>
</tr>
<tr>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata4</td>
<td></td>
<td>txdata7</td>
<td></td>
<td>txdata8</td>
<td></td>
<td>txdata11</td>
<td></td>
<td>rxdata10</td>
<td></td>
<td>rxckp</td>
<td></td>
<td>rxdata6</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata9</td>
<td></td>
<td>rxckn</td>
<td></td>
<td>rxdata5</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata5</td>
<td></td>
<td>txckn</td>
<td></td>
<td>txdata9</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata6</td>
<td></td>
<td>txckp</td>
<td></td>
<td>txdata10</td>
<td></td>
<td>rxdata11</td>
<td></td>
<td>rxdata8</td>
<td></td>
<td>rxdata7</td>
<td></td>
<td>rxdata4</td>
<td></td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td></td>
<td>txdata0</td>
<td></td>
<td>txdata3</td>
<td></td>
<td>txdata12</td>
<td></td>
<td>txdata15</td>
<td></td>
<td>rxdata14</td>
<td></td>
<td>rxvld</td>
<td></td>
<td>rxdata2</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>rxdata13</td>
<td></td>
<td>rxtrk</td>
<td></td>
<td>rxdata1</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata1</td>
<td></td>
<td>txtrk</td>
<td></td>
<td>txdata13</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>txdata2</td>
<td></td>
<td>txvld</td>
<td></td>
<td>txdata14</td>
<td></td>
<td>rxdata 15</td>
<td></td>
<td>rxdata12</td>
<td></td>
<td>rxdata3</td>
<td></td>
<td>rxdata0</td>
<td></td>
</tr>
<tr>
<td></td>
<td colspan="15">Die Edge</td>
</tr>
<tr>
<td colspan="16"></td>
</tr>
</table>

## 5.7.3.2 x8 Standard Package Module Bump Map

Designs can choose to add a UCIe-S port for sort/pre-bond test purposes in scenarios where they
need the high bandwidth of UCIe, but the design is an advanced package design, or for any other
reason. To reduce the chiplet's die edge when supporting such a UCIe-S usage, a x8 version of UCIe-
S is provided. This is an additional option that goes beyond the available standard x16 UCIe-S port
options. A UCIe-S x16 Module, including bump maps for all data rates, can optionally support a
connection to a UCIe-S x8 Module. When this connection is supported, the connection is always to the
lower x8 lanes (i.e., Lanes 7:0). UCIe-S x8 designs must support lane reversal and degraded mode
operation to x4. UCIe-S x16 designs that support connection to a x8 Module must support lane
reversal, and must support degraded mode operation to x4 on its lower 8 lanes when connected to a
x8 Module.

UCIe-S x8 support is limited to a single module configuration and up to 32 GT/s. When a UCIe-S x8
port is connected to a multi-module x16 port, it is always connected to Module 0 UCIe-S x16.

Figure 5-52 shows the reference bump matrix for a x8 Standard Package.

<table>
<caption>Figure 5-52. Standard Package Bump Map: x8 Interface</caption>
<tr>
<th>Column 0</th>
<th>Column 1</th>
<th>Column 2</th>
<th>Column 3</th>
<th>Column 4</th>
<th>Column 5</th>
<th>Column 6</th>
<th>Column 7</th>
</tr>
<tr>
<td>txdatasb</td>
<td></td>
<td>txcksb</td>
<td></td>
<td>rxcksb</td>
<td></td>
<td>rxdatasb</td>
<td></td>
</tr>
<tr>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
<td></td>
<td>vccio</td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td></td>
<td>Txdata0</td>
<td></td>
<td>Txdata7</td>
<td></td>
<td>Rxdata6</td>
<td></td>
<td>Rxdata1</td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>Txckn</td>
<td></td>
<td>VSS</td>
<td></td>
<td>Rxckp</td>
<td></td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>vccio</td>
<td></td>
<td>Txckp</td>
<td></td>
<td>vccio</td>
<td></td>
<td>Rxckn</td>
<td></td>
</tr>
<tr>
<td></td>
<td>Txdata1</td>
<td></td>
<td>Txdata6</td>
<td></td>
<td>Rxdata7</td>
<td></td>
<td>Rxdata0</td>
</tr>
<tr>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
<td>vccio</td>
<td></td>
<td>VSS</td>
<td></td>
</tr>
<tr>
<td></td>
<td>Txdata3</td>
<td></td>
<td>Txdata4</td>
<td></td>
<td>Rxdata5</td>
<td></td>
<td>Rxdata2</td>
</tr>
<tr>
<td>vccio</td>
<td></td>
<td>$T x v l d$</td>
<td></td>
<td>vccio</td>
<td></td>
<td>Rxtrk</td>
<td></td>
</tr>
<tr>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
<td></td>
<td>VSS</td>
</tr>
<tr>
<td>VSS</td>
<td></td>
<td>Txtrk</td>
<td></td>
<td>VSS</td>
<td></td>
<td>Rxvld</td>
<td></td>
</tr>
<tr>
<td></td>
<td>Txdata2</td>
<td></td>
<td>Txdata5</td>
<td></td>
<td>Rxdata4</td>
<td></td>
<td>Rxdata3</td>
</tr>
</table>

Die Edge

It is strongly recommended to follow the bump matrix provided in Figure 5-52. The lower left corner
of the bump map will be considered "origin" of a bump matrix.

The same rules as mentioned for x16 and x32 Standard Package bump matrices in Section 5.7.3.1
must be followed for the x8 bump matrix.

## 5.7.3.3 x16 and x8 Standard Package Module Interoperability

A x8 bump matrix will either connect to another x8 bump matrix or to bits [7:0] of a x16 bump
matrix.

## 5.7.3.4 Module Naming of Standard Package Modules

This section describes the Module naming convention of Standard Package Modules in a multi-module
configuration.

The naming of M0, M1, M2, and M3 will apply to 1, 2, or 4 Standard Package modules that are
aggregated through MMPL, in stacked and unstacked configuration combinations.

Figure 5-53 shows the naming convention for 1, 2, or 4 Standard Package modules when they are
connected to their "Standard Die Rotate" module counterparts with the same number of Standard
Package modules, with either same stack or same unstacked configuration.

Note:
The double-ended arrows in Figure 5-53 through Figure 5-57 indicate Module-to-
Module connections.

<figure>
<figcaption>Figure 5-53. Naming Convention for One-, Two-, and Four-module Standard Package Paired with "Standard Die Rotate" Configurations</figcaption>

MO

M1

MO

M1

MO

Tx
(x15)

Hs
(16)

Tx
(x16)

RN
(<16)

Ts
(*15]

R.
[x16)

Tx
[x16)

Rx
(x26)

T.K
[x16)

Rx
[xIGI

Tx
[x16)

M2

RX
(x16)

Tx
(x)6)

M3

Rx
(=26)

(91)

[91X)

19L.)

(TN)
RX

(OTX)
KA

(9Tv)
TH

(91)

(x16)

(STX)
XL

(x1E)

(x16)

Rx

¥L

(9)*)
34

191-)
X1

19LAT
KN

W!

MO

M34

Rx

XL

MO

M1

M3

M2

MO

M1

$1 - x 1$

$x 2$ Unstacked $- \quad x 2$ Unstacked

x4 Unstacked - x4 Unstacked

MI

M3

AY
[x16)

M1

Fix
(x16

Ta
(,16)

REA
(*16

1,
(×16)

1x

(x16)

MO

MQ

IX
(x16)

1x
(x16)

Hx
(x15)

M2

TK

Rx
(×16)

AX

(x16)

[x16)

·15)

(9[*)
MI

x10)

(91)
KL

(91)

(1)

EH

KH

Xb

OW

X1

M2

OW

(9TX)

(Prk)

(9TM)

(92%)

(41)

(41X)
RK

K

MN

.:

TW

M3

X1

M1

x2 Stacked - x2 Stacked

x4 Stacked - x4 Stacked

</figure>

Figure 5-54 shows the naming convention for 1, 2, or 4 Standard Package modules when they are
connected to their "Mirrored Die Rotate" counterparts that have same number of Standard Package
modules, with either same stack or same unstacked configuration.

<figure>
<figcaption>Figure 5-54. Naming Convention for One-, Two-, and Four-module Standard Package Paired with "Mirrored Die Rotate" Configurations</figcaption>

MO

M1

MO

Ta
(=16)

M1

MO

RX
(wtG)

Tx
(*16)

RW
(x16)

TM
[x16)

M2

AN
(x16)

Tx
(x16)

M3

Tx
(x10)

Rx
[x16)

1x
(x16)

1x

A

(¥101

Tx
(x16)

KV
(16)

I-10)

here)
1X

(are)

(KB)

(2)
K

(xJe)
P

(*)+)
12

(se)

(x12)

1x12)
IN

ISTEN
BX

(XTC)
1ª

(XTC)
HA

(XTC)
IM

(KT2)
!! &

WO

LOX

1#

14

54

WT

OM

WT

OM

WS

EM

$x 1 - x 1$

x2 Unstacked -x2 Unstacked

x4 Unstacked - x4 Unstacked

M1

ALK

TA
[¥15)

RKA
İKİG

M1

Tx
(x1G)

RX
(x10

M3

Tx
İx1G)

4x16

MO

1x
(xIG)

KK
(HIG)

1%
(x36)

MO

TW
(16)

M2

RN
for

Re
(1)

चिस
I

(vr@)
1

(xTe)
IK

(KT2)
UX

[XTeJ

(Tel
IK

WO

WO

2

WS

(a)e)
LO

(xre)
KT

Ire

(xce)
IM

(>10
HM

(xTe)

WT

1\.

1Z

WAT

EM

x2 Stacked - x2 Stacked

x4 Stacked - x4 Stacked

</figure>

Table 5-27 summarizes the connections between the combinations shown in Figure 5-53 and
Figure 5-54.

<table>
<caption>Table 5-27. Summary of Standard Package Module Connection Combinations with Same Number of Modules on Both Sides a b</caption>
<tr>
<th rowspan="2">Standard Package Module Connections (Same # of Modules on Both Sides)</th>
<th rowspan="2">Standard Die Rotate Counterpart</th>
<th colspan="2">Mirrored Die Rotate Counterpart</th>
</tr>
<tr>
<th>Option 1 (See Figure 5-54)</th>
<th>Option 2℃ (See Figure 5-57)</th>
</tr>
<tr>
<td>$1 \quad - x 1$</td>
<td>· $M O \quad - \quad M O$</td>
<td>· $M O \quad - \quad M O$</td>
<td></td>
</tr>
<tr>
<td rowspan="2">x2 Unstacked - x2 Unstacked</td>
<td>· $M O \quad - \quad M 1$</td>
<td>· $M O \quad - \quad M O$</td>
<td></td>
</tr>
<tr>
<td>· $M 1 \quad - \quad M O$</td>
<td>· $M 1 \quad - \quad M 1$</td>
<td></td>
</tr>
<tr>
<td rowspan="2">x2 Stacked - x2 Stacked</td>
<td>· $M O \quad - \quad M O$</td>
<td>· $M O \quad - \quad M O$</td>
<td>· $M O \quad - \quad M 1$</td>
</tr>
<tr>
<td>· $M 1 \quad - \quad M 1$</td>
<td>· $M 1 \quad - \quad M 1$</td>
<td>· $M 1 \quad - \quad M O$</td>
</tr>
<tr>
<td rowspan="4">x4 Unstacked - x4 Unstacked</td>
<td>· $M O \quad - \quad M 2$</td>
<td>· $M O \quad - \quad M O$</td>
<td></td>
</tr>
<tr>
<td>· $M 1 \quad - \quad M 3$</td>
<td>· $M 1 \quad - \quad M 1$</td>
<td></td>
</tr>
<tr>
<td>· $M 3 \quad - \quad M 1$</td>
<td>· $M 2 \quad - \quad M 2$</td>
<td></td>
</tr>
<tr>
<td>· M2 - MO</td>
<td>· $M 3 \quad - \quad M 3$</td>
<td></td>
</tr>
<tr>
<td rowspan="4">$x 4 \quad S t a c k e d \quad - \quad x 4 \quad S t a c k e d$</td>
<td>· $M O \quad - \quad M 2$</td>
<td>· $M O \quad - \quad M O$</td>
<td>· $M O \quad - \quad M 1$</td>
</tr>
<tr>
<td>· M1 - M3</td>
<td>· $M 1 \quad - \quad M 1$</td>
<td>· $M 1 \quad - \quad M O$</td>
</tr>
<tr>
<td>· M3 - M1</td>
<td>· $M 2 \quad - \quad M 2$</td>
<td>· $M 2 \quad - \quad M 3$</td>
</tr>
<tr>
<td>· M2 - MO</td>
<td>· $M 3 \quad - \quad M 3$</td>
<td>· $M 3 \quad - \quad M 2$</td>
</tr>
</table>

a. Mirror-to-Mirror connection will be same as non-mirrored case.

b. Mirror die connectivity may have jogs and need additional layers on package.

c. For some mirrored cases, there are possible alternative connections to allow design choices between more routing layers vs. max
data rates, shown as Option 1 and Option 2 in Table 5-27. For x2 - x2 Stacked and x4 - x4 Stacked cases, Option 1 typically
requires 2x the routing layers and enables nominal data rates, while Option 2 enables same the layer count but at reduced max
data rates due to potential crosstalk. See Figure 5-56 for Option 2 connection illustrations.

Figure 5-55 shows the naming convention for 1, 2, or 4 Standard Package modules when they are
connected to their "Standard Die Rotate" counterparts that have a different number of Standard
Package modules.

<figure>
<figcaption>Figure 5-55. Examples for Standard Package Configurations Paired with "Standard Die Rotate" Counterparts, with a Different Number of Modules</figcaption>

MI

M3

MI

MJ

MT

7

A

4

MI

M3

\-

%

\-

\-

wicy

MO

M2

MD

M2

MU

M2

W

MO

M2

2

.

7

K

\-

nro

Hirey

0

w

EW

MO

IW

MD

x4 Stacked -x4 Unstacked

x4 Stacked - x2 Unstacked

\-

$4 \quad S t a c k e d \quad - x 1$

x4 Stacked - x2 Stacked

MI

MO

M2

M3

MI

MO

M2

Ma

M1

MO

M2

M3

\-

&

1441

1.MH

TE

W

\-

\-

(-16)

I

MD

LT
4

my

DW

x4 Unstacked - x2 Unstacked

x4 Unstacked - x2 Stacked

.

TW

$x 4 \quad U n s t a c k e d \quad - x 1$

MI

MI

MO

0

P

\-

I

6

T

I

\-

Bu

\-

W

\-
M

\-

-4

4

$x 2 \quad U n s t a c k e d \quad - x 1$

MO

x2 Stacked -x2 Unstacked

$x 2 \quad S t a c k e d \quad - x 1$

</figure>

Figure 5-56 shows the naming convention for 1, 2, or 4 Standard Package Modules when they are
connected to their "Mirrored Die Rotate" counterparts that have a different number of Standard
Package Modules.

<figure>
<figcaption>Figure 5-56. Examples for Standard Package Configurations Paired with "Mirrored Die Rotate" Counterparts, with a Different Number of Modules</figcaption>

MI

MR

Ta

MI

W

CON

MO

M2

MO

M2

MI

MO

A

..

..

.

1

IM

.

EM

0

VAT

I

\-

1

NO

x4 Stacked - x4 Unstacked

x4 Stacked - x2 Unstacked

x4 Stacked - x1

4

\-

x4 Stacked - x2 Stacked

MI

MO

MJ

MI

MO

M2

M3

MI

MO

M2

.

.

T

Te

T

H

..

1

..

..

DJ41

1-360

5

1100

A

0

I

\#

\-

x4 Unstacked - x2 Unstacked

x4 Unstacked $- \quad x 2$ Stacked

W

x4 Unstacked - x1

M1

M

M1

MU

n

\-

Tw

\-

MG

W

T

A

aJej

pTet

\-

x2 Unstacked -x1

0

1

WO

AT

WO

1

x2 Stacked - x2 Unstacked

×2 Stacked -x1

</figure>

Figure 5-57 illustrates the possible alternative connections for some mirrored cases to allow design
choices between more routing layers vs. reduced max data rates due to potential crosstalk, shown as
Option 2 in Table 5-27 and Table 5-28.

<figure>
<figcaption>Figure 5-57. Additional Examples for Standard Package Configurations Paired with "Mirrored Die Rotate" Counterparts, with a Different Number of Modules</figcaption>

MI

MI

M3

MI

M3

MI

M3

\-

-161

[x

MO

MO

M2

MD

M2

n

TA

N

D

A

2

Intel

161

TM

TA

Popel

(-200

I

WO

\-

WD

WS

W

.

OM

(*10)

\-

x4 Stacked - x2 Unstacked

WIT

EM

$x 2 \quad S t a c k e d \quad - \quad x 2 \quad S t a c k e d$

x4 Stacked - x4 Stacked

x4 Stacked - x2 Stacked

</figure>

Table 5-28 summarizes the connections between the combinations shown in Figure 5-55, Figure 5-56,
and Figure 5-57.

<table>
<caption>5.7.3.4.1 Module Degrade Rules Table 5-28. Summary of Standard Package Module Connection Combinations with Different Number of Modules on Both Sides</caption>
<tr>
<th rowspan="2">Standard Package Module Connections (Different # of Modules on Both Sides)</th>
<th rowspan="2">Standard Die Rotate Counterpartª</th>
<th colspan="2">Mirrored Die Rotate Counterpartª</th>
</tr>
<tr>
<th>Option 1 (See Figure 5-56)</th>
<th>Option 2 (See Figure 5-57)</th>
</tr>
<tr>
<td rowspan="4">x4 Stacked - x4 Unstacked</td>
<td>· $M O \quad - \quad M 2$</td>
<td>· $M O \quad - \quad M O$</td>
<td></td>
</tr>
<tr>
<td>· $M 1 \quad - \quad M 3$</td>
<td>· $M 1 \quad - \quad M 1$</td>
<td></td>
</tr>
<tr>
<td>· M3 - M1</td>
<td>· M2 - M2</td>
<td></td>
</tr>
<tr>
<td>· $M 2 \quad - \quad M O$</td>
<td>· $M 3 \quad - \quad M 3$</td>
<td></td>
</tr>
<tr>
<td rowspan="4">x4 Stacked - x2 Stacked</td>
<td>· $M O \quad - \quad M O$</td>
<td>· $M O \quad - \quad M O$</td>
<td>· MO - M1</td>
</tr>
<tr>
<td>· $M 1 \quad - \quad M 1$</td>
<td>· $M 1 \quad - \quad M 1$</td>
<td>· $M 1 \quad - \quad M O$</td>
</tr>
<tr>
<td>· $M 3 \quad - \quad N C$</td>
<td>· M2 - NC</td>
<td>· M2 - NC</td>
</tr>
<tr>
<td>· M2 - NC</td>
<td>· M3 - NC</td>
<td>· $M 3 \quad - \quad N C$</td>
</tr>
<tr>
<td rowspan="4">$x 4 \quad S t a c k e d \quad - \quad x 2 \quad U n s t a c k e d$</td>
<td>· $M O \quad - \quad M O$</td>
<td>· $M O \quad - \quad M 1$</td>
<td>· MO - NC</td>
</tr>
<tr>
<td>· $M 1 \quad - \quad N C$</td>
<td>· $M 1 \quad - \quad N C$</td>
<td>· $M 1 \quad - \quad M 1$</td>
</tr>
<tr>
<td>· M3 - NC</td>
<td>· $M 2 \quad - \quad M O$</td>
<td>· M2 - NC</td>
</tr>
<tr>
<td>· $M 2 \quad - \quad M 1$</td>
<td>· M3 - NC</td>
<td>· $M 3 \quad - \quad M O$</td>
</tr>
<tr>
<td rowspan="4">$x 4 \quad S t a c k e d \quad - \quad x 1$</td>
<td>· $M O \quad - \quad M O$</td>
<td>· $M O \quad - \quad M O$</td>
<td></td>
</tr>
<tr>
<td>· $M 1 \quad - \quad N C$</td>
<td>· $M 1 \quad - \quad N C$</td>
<td></td>
</tr>
<tr>
<td>· M3 - NC</td>
<td>· M3 - NC</td>
<td></td>
</tr>
<tr>
<td>· M2 - NC</td>
<td>· M2 - NC</td>
<td></td>
</tr>
<tr>
<td rowspan="4">x4 Unstacked - x2 Unstacked</td>
<td>· $M O \quad - \quad M 1$</td>
<td>· $M O \quad - \quad M O$</td>
<td></td>
</tr>
<tr>
<td>· $M 1 \quad - \quad M O$</td>
<td>· $M 1 \quad - \quad M 1$</td>
<td></td>
</tr>
<tr>
<td>· M3 - NC</td>
<td>· M2 - NC</td>
<td></td>
</tr>
<tr>
<td>· M2 - NC</td>
<td>· M3 - NC</td>
<td></td>
</tr>
<tr>
<td rowspan="4">x4 Unstacked - x2 Stacked</td>
<td>· $M O \quad - \quad M 1$</td>
<td>· $M O \quad - \quad M 1$</td>
<td></td>
</tr>
<tr>
<td>· M1 - MO</td>
<td>· $M 1 \quad - \quad M O$</td>
<td></td>
</tr>
<tr>
<td>· M3 - NC</td>
<td>· M2 - NC</td>
<td></td>
</tr>
<tr>
<td>· M2 - NC</td>
<td>· M3 - NC</td>
<td></td>
</tr>
<tr>
<td rowspan="4">$x 4 \quad U n s t a c k e d \quad - \quad x 1$</td>
<td>· $M O \quad - \quad M O$</td>
<td>· $M O \quad - \quad M O$</td>
<td></td>
</tr>
<tr>
<td>· M1 - NC</td>
<td>· $M 1 \quad - \quad N C$</td>
<td></td>
</tr>
<tr>
<td>· M3 - NC</td>
<td>· M3 - NC</td>
<td></td>
</tr>
<tr>
<td>· M2 - NC</td>
<td>· M2 - NC</td>
<td></td>
</tr>
<tr>
<td rowspan="2">x2 Stacked - x2 Unstacked</td>
<td>· $M O \quad - \quad M 1$</td>
<td>· $M O \quad - \quad M O$</td>
<td></td>
</tr>
<tr>
<td>· $M 1 \quad - \quad M O$</td>
<td>· $M 1 \quad - \quad M 1$</td>
<td></td>
</tr>
<tr>
<td rowspan="2">x2 Stacked - x1</td>
<td>· $M O \quad - \quad M O$</td>
<td>· $M O \quad - \quad M O$</td>
<td></td>
</tr>
<tr>
<td>· M1 - NC</td>
<td>· $M 1 \quad - \quad N C$</td>
<td></td>
</tr>
<tr>
<td rowspan="2">x2 Unstacked - x1</td>
<td>· $M O \quad - \quad M O$</td>
<td>· $M O \quad - \quad M O$</td>
<td></td>
</tr>
<tr>
<td>· M1 - NC</td>
<td>· M1 - NC</td>
<td></td>
</tr>
</table>

a. NC indicates no connection.

On a 2-module or 4-module link, if one or more module-pairs have failed, the link will be degraded
and shall comply with the following rules:

1\. The degraded link shall be either one or two modules, and shall not be three modules.

a. For a 4-module link:

i. If any one module-pair failed, it shall be degraded to a 2-module link.

ii. If any two module-pairs failed, it shall be degraded to a 2-module link.

iii. If any three module-pairs failed, it shall be degraded to a 1-module link.

b. For a 2-module link:

i. If any one module-pair failed, it shall be degraded to a 1-module link.

2\. For a 4-module link, if only one module-pair failed, one additional module-pair that belongs to the
"same half" (along the Die Edge) of the 4-module will be disabled/degraded.

Figure 5-58 illustrates an example with a x4 Unstacked connected to a x4 Unstacked "Standard Die
Rotate" counterpart with one MO - M2 pair failed. The M1 - M3 pair on its left shall be disabled
accordingly to comply with the rules defined above, which will be denoted as "x (d)" in Table 5-29.

<figure>
<figcaption>Note: The double-ended arrows in Figure 5-58 indicate Module-to-Module connections. Figure 5-58. Example of a Configuration for Standard Package, with Some Modules Disabled</figcaption>

M1

Tx
(x16)

MO

Rx
(x16)

Tx
(x16)

Rx
(x16)

Tx
(x16)

M2

Rx
(x16)

Tx
(x16)

M3

Rx

(x16)

X (degraded)
☒

X
☒

(x16)

(x16)
XL

(x16)
Rx

(9T*)
×1

(91x)
Rx

(×16)
XL

(x16)
Rx

(×16)
×1

RX

M3

M2

MO

M1

</figure>

Table 5-29 summarizes the resulting degraded link if there are one, two, or three failed module-pairs
for the x4 Unstacked to x4 Unstacked configuration.

<table>
<caption>Table 5-29. Summary of Degraded Links when Standard Package Module-pairs Fail</caption>
<tr>
<th rowspan="2">Module - Module Partner Pair</th>
<th colspan="14">Number of Module-pairs Failedª</th>
</tr>
<tr>
<th colspan="4">1-fail</th>
<th colspan="2"></th>
<th colspan="4">2-fail</th>
<th colspan="4">3-fail</th>
</tr>
<tr>
<td>$M O \quad - \quad M 2$</td>
<td>$x$ ☒</td>
<td>$x \left( d \right)$ ☒</td>
<td>☒</td>
<td>☒</td>
<td>$x$ ☒</td>
<td>$x$ ☒</td>
<td>$x$ ☒</td>
<td>☒</td>
<td>☒</td>
<td>☒</td>
<td>$x$ ☒</td>
<td>$x$ ☒</td>
<td>$x$ ☒</td>
<td>☒</td>
</tr>
<tr>
<td>$M 1 \quad - \quad M 3$</td>
<td>$x \left( d \right)$ ☒</td>
<td>☒ x</td>
<td>☒</td>
<td>☒</td>
<td>$x$ ☒</td>
<td>☒</td>
<td>☒</td>
<td>$x$ ☒</td>
<td>$x$ ☒</td>
<td>☒</td>
<td>$x$ ☒</td>
<td>$x$ ☒</td>
<td>☒</td>
<td>$x$ ☒</td>
</tr>
<tr>
<td>$M 3 \quad - \quad M 1$</td>
<td>☒</td>
<td>☒</td>
<td>☒ x</td>
<td>$x \left( d \right)$ ☒</td>
<td>☒</td>
<td>$x$ ☒</td>
<td>☒</td>
<td>$x$ ☒</td>
<td>☒</td>
<td>$x$ ☒</td>
<td>$x$ ☒</td>
<td>☒</td>
<td>$x$ ☒</td>
<td>$x$ ☒</td>
</tr>
<tr>
<td>$M 2 \quad - \quad M O$</td>
<td>☒</td>
<td>☒</td>
<td>$x \left( d \right)$ ☒</td>
<td>$x$ ☒</td>
<td>☒</td>
<td>☒</td>
<td>$x$ ☒</td>
<td>☒</td>
<td>$x$ ☒</td>
<td>$x$ ☒</td>
<td>☒</td>
<td>$x$ ☒</td>
<td>$x$ ☒</td>
<td>$x$ ☒</td>
</tr>
</table>

a. x = Failed Module - Module Partner Pair.
☒

x (d) = Disabled Module - Module Partner Pair to comply with Degrade rules.
☒

v = Functional Module - Module Partner Pair.
☒

All other module configurations shall follow the same Module Degrade rules as defined above.

### 5.7.4 UCIe-S Sideband-only Port

A UCIe-S sideband-only port is also permitted for test/manageability purposes. The RDI signals to the
sideband port for a sideband-only configuration are the same as for a sideband with mainband
configuration (see Chapter 10.0 for details of the latter).

Figure 5-59 shows the bump map for a UCIe-S sideband-only port. Figure 5-60 shows the supported
configurations for a UCIe-S sideband-only port.

<figure>
<figcaption>Figure 5-59. UCIe-S Sideband-only Port Bump Map</figcaption>

VSS

m1rxdatasb

m1rxcksb

vccaon

VSS

m1txcksb

m1txdatasb

</figure>

<figure>
<figcaption>Figure 5-60. UCIe-S Sideband-only Port Supported Configurations</figcaption>

Config 1

Config 2

UCIe-S
SB-only

UCIe-S
SB-only

SB

MB

UCIe-S
SB-only

CIe-S x16/x8

</figure>

#### 5.8 Tightly Coupled Mode

Tightly Coupled PHY mode is defined as when both of the following conditions are met:

· Shared Power Supply between Tx and Rx, or Forwarded Power Supply from Tx to Rx

. Channel supports larger eye mask defined in Table 5-30

In this mode, there is no Receiver termination and the Transmitter must provide full swing output. In
this mode, further optimization of PHY circuit and power reduction is possible. For example, a tuned
inverter can potentially be used instead of a front-end amplifier. Training complexity such as voltage
reference can be simplified.

<table>
<caption>Table 5-30. Tightly Coupled Mode: Eye Mask</caption>
<tr>
<th>Data Rate</th>
<th>4-16 GT/s</th>
</tr>
<tr>
<td>Overall (Eye Closure due to Channel)a</td>
<td></td>
</tr>
<tr>
<td>Eye Heightb</td>
<td>250 mV</td>
</tr>
<tr>
<td>Eye Width (rectangular eye mask with specified eye height)</td>
<td>0.7 UI</td>
</tr>
</table>

a. With 750-mV Transmitter signal swing.

b. Centered around VCCFWDIO/2.

Loss and crosstalk requirement follow the same VTF method, adjusting to the eye mask defined in
Table 5-30. Table 5-31 shows the specification at Nyquist frequency.

<table>
<caption>Table 5-31. Tightly Coupled Mode Channel for Advanced Package</caption>
<tr>
<th>Data Rate</th>
<th>4-12 GT/s</th>
<th>16 GT/s</th>
</tr>
<tr>
<td>VTF Lossª (dB)</td>
<td>L(fN) &gt; -3</td>
<td>-</td>
</tr>
<tr>
<td>VTF Crosstalkª (dB)</td>
<td>XT(f) &lt; 1.5 * L(fN) - 21.5 and $X T \left( f _ { N } \right) < - 2 3$</td>
<td>-</td>
</tr>
</table>

a. Based on Voltage Transfer Function (Tx: 25 ohm / 0.25 pF; Rx: 0.2 pF).

Loss and crosstalk specifications between DC and Nyquist $\mathrm { f } _ { \mathrm { N } }$ follow the same methodology defined in
Section 5.7.2.1.

Although the use of this mode is primarily for Advanced Package, it may also be used for Standard
Package when two Dies are near one another and Receiver must be unterminated.

##### 5.9 Interconnect redundancy Remapping

###### 5.9.1 Advanced Package Lane Remapping

Interconnect Lane remapping is supported in Advanced Package Module to improve assembly yield
and recover functionality. Each module supports:

· Four redundant bumps for Data

. One redundant bump for Clock and Track

· One redundant bump for Valid

For x64 Advanced Package modules, the four redundant bumps for data repair are divided into two
groups of two. Figure 5-61 shows an illustration of x64 Advanced package module redundant bump
assignment for data signals. TRD_P0 and TRD_P1 are allocated to the lower 32 data Lanes and
TRD_P2 and TRD_P3 are allocated to the upper 32 data Lanes. Each group is permitted to remap up

to two Lanes. For example, TD15 is a broken Lane in the lower half and TD_P32 and TD_P40 are
broken Lanes in the upper 32 Lanes. Figure 5-62 illustrates Lane remapping for the broken Lanes.

For x32 Advanced Package modules, only the lower 32 data lanes and TRD_P0 and TRD_P1 apply in
Figure 5-61 and Figure 5-62.

Details and implementation of Lane remapping for Data, Clock, Track, and Valid are provided in
Section 4.3.

<figure>
<figcaption>Figure 5-61. Data Lane repair resources</figcaption>

TD_P2

TD_P9

TD_P16

TD_P23

TD_P30

TD_P34

TD_P41

TD_P48

TD_P55

TD_P62

TD_P3

$T D _ { - } P 1 0$

TD_P17

TD_P24

TD_P31

$T D _ { - } P 3 5$

TD_P42

TD_P49

TD_P56

TD_P63

TD_P1

TD_P8

TD_P15

TD_P22

TD_P29

TD_P33

TD_P40

TD_P47

TD_P54

TD_P61

$T D _ { - } P$

TD_P11

$T D _ { - } P 1 8$

TD_P25

TRD_P1

TD_P36

TD_P43

TD_P50

TD_P57

TRD_P3

TD_P0

TD_P7

$T D _ { - } P 1 4$

TD_P21

TD_P28

$T D _ { - } P 3 2$

$T D _ { - } P 3$

$T D _ { - } P 4 6$

TD_P53

TD_P60

TD_P5

$T D \_ P 1 2$

$T D _ { - P 1 }$

TD_P26

TD_P37

TD_P44

TD_P51

TD_P58

TRD_P0

$T D _ { - } P$

TD_P13

TD_P20

TD_P27

TRD_P2

TD_P38

$T D \_ P 4 5$

TD_P52

TD_P59

</figure>

<figure>
<figcaption>Figure 5-62. Data Lane repair</figcaption>

TD_P2

TD_P9

TD_P16

$T D _ { 2 }$

TD_P30

TD_P34

TD_P41

TD_P48

$T D \_ P 5 5$

$T D _ { 2 } P 6 2$

TD_P3

TD_P10

$T D \_ P 1 7$

TD_P24

$T D \_ P 3 1$

TD_P35

TD_P42

TD_P49

TD_P56

TD_P63

TD_P1

TD_P8

TD <15

TD_P22

TD_P29

$T D \_ P 3 3$

TD 40

TD_P47

TD_P54

TD_P61

TD_P4

$T D \_ P 1 1$

TD_P18

TD_P25

TRD_P1

TD_P36

TD_P43

TD_P50

$P 5 ^ { \circ }$

TRD_P3

TD_P0

TD_P7

$T D \_ P 1 4$

TD_P21

TD_P28

TD -32

TD_P39

TD_P46

$T D \_ P 5 3$

TD_P60

TD_P5

TD_P12

TD_P19

TD_P26

TD_P37

TD_P44

TD_P51

TD_P58

TRD_P0

$T D _ { - } P 6$

TD_P13

TD_P20

TD_P27

TRD_P2

TD_P38

TD_P45

TD_P52

TD_P59

</figure>

###### 5.9.2 Standard Package Lane remapping

Lane repair is not supported in Standard Package modules.

##### 5.10 BER Requirements, CRC, and Retry

The BER requirement based on channel reach defined in Section 5.7 is shown in Table 5-32. Error
detection and correction mechanisms such as CRC and retry are required for BER of 1E-15 or higher
to achieve the required Failure In Time (FIT) rate of significantly less than 1 (1 FIT = 1 device failure
in 109 Hours). The UCIe spec defined CRC and retry is detailed in Chapter 3.0. For the BER of 1E-27,
either parity or CRC can be used and the appropriate error reporting mechanism must be invoked to
ensure a FIT that is significantly less than 1.

<table>
<caption>Table 5-32. Raw BER Requirements</caption>
<tr>
<th rowspan="2">Package Type</th>
<th colspan="8">Data Rate $\left( \mathrm { G T } / \mathrm { s } \right)$</th>
</tr>
<tr>
<th>4</th>
<th>8</th>
<th>12</th>
<th>16</th>
<th>24</th>
<th>32</th>
<th>48</th>
<th>64</th>
</tr>
<tr>
<td>Advanced Package</td>
<td>1E-27</td>
<td>1E-27</td>
<td>1E-27</td>
<td>1E-15</td>
<td>1E-15</td>
<td>1E-15</td>
<td>1E-15</td>
<td>1E-12</td>
</tr>
<tr>
<td>Standard Package</td>
<td>1E-27</td>
<td>1E-27</td>
<td>1E-15</td>
<td>$1 E - 1 5$</td>
<td>1E-15</td>
<td>1E-15</td>
<td>1E-15</td>
<td>$1 E - 1 2$</td>
</tr>
</table>

###### 5.11 Valid and Clock Gating

Valid is used to frame transmit data. For a single transmission of 8 UI data packet, Valid is asserted
for the first 4 UI and de-asserted for the second 4 UI. Figure 5-63 shows the transfer of two 8 UI data
packets back to back.

<figure>
<figcaption>Figure 5-63. Valid Framing</figcaption>

Clock

Valid

Data

8 UI

8 UI

</figure>

As described in Section 4.1.3, clock must be gated only after Valid signal remains low for 16 UI
(8 cycles) of postamble clock for half-rate clocking and 32 UI (8 cycles) of postamble clock for
quarter-rate clocking, unless free running clock mode is negotiated.

Idle state is when there is no data transmission on the mainband. During Idle state, Data, Clock, and
Valid Lanes must hold values as follows:

. If the Link is unterminated, some Data Lane Transmitters are permitted to remain toggling up to
the same transition density as the scrambled data without advancing the scrambler state. The
remaining Data Lane Transmitters must hold the data of the last transmitted bit. Valid Lane must
be held low until the next normal transmission.

\- In Strobe mode, the clock level in a clock-gated state for half-rate clocking (after meeting
postamble requirement) must alternate between differential high and differential low during
consecutive clock-gating events. For quarter-rate clocking, the clock level in a clock-gated
state must alternate between high and low for both phases (Phase-1 and Phase-2)
simultaneously. Clock must drive a differential (simultaneous) low for half- (quarter-) rate
clocking for at least 1 UI or a maximum of 8 UI before normal operation. The total clock-gated
period must be an integer multiple of 8 UI. Example shown in Figure 5-64 and Figure 5-65.

\- In Continuous mode, the clock remains free running (examples shown in Figure 5-66). Total
idle period must be an integer multiple of 8 UI.

<figure>
<figcaption>Figure 5-64. Data, Clock, Valid Levels for Half-rate Clocking: Clock-gated Unterminated Link</figcaption>

Clock Gated (Multiple of 8 UI: N * 8 UI)

Normal operation

Clock Postamble

Normal operation

Clock

Parked Clock Level

Valid

Data[n]

D0

D1

De

DB

D4

D5

D6

D7

D7 or Implementation-specific pattern

16 UL

1 UI to 8 UI

</figure>

<figure>
<figcaption>Figure 5-65. Data, Clock, Valid Levels for Quarter-rate Clocking: Clock-gated Unterminated Link</figcaption>

Normal operation

Clock Postamble

Clock Gated (Multiple of Valid frames: N * 8 UI)

Normal operation

Quad Clock

Phase-1

Parked Clock Level

Quad Clock
Phase-2

Parked Cock Level

Valid

Data[n]

D0

D1

D2

DB

D4

D5

D6

D7

D7 or Implementation-specific pattern

32 UI

1 UI to 8 UI

</figure>

Figure 5-66.
Data, Clock, Valid Levels for Half-rate Clocking:
Continuous Clock Unterminated Link

<table>
<tr>
<th></th>
<th>Normal operation</th>
<th>Free running (Multiple of 8 UI: N * 8 UI)</th>
<th colspan="2">Normal operation</th>
</tr>
<tr>
<td>Clock Valid</td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td colspan="2" rowspan="3">Data[n] D0 D1 D2 DB D4 D5 D6 D7</td>
<td></td>
<td></td>
<td rowspan="3"></td>
</tr>
<tr>
<td>D7 or Implementation-specific pattern</td>
<td rowspan="2"></td>
</tr>
<tr>
<td></td>
</tr>
</table>

<figure>
</figure>

. If the Link is terminated, some Data Lane Transmitters are permitted to remain toggling up to the
same transition density as the scrambled data without advancing the scrambler state. The
remaining Data Lanes' Transmitters hold the data of the last-transmitted bit for 16 UIs under half-
rate clocking and 32 UIs under quarter-rate clocking, before transitioning to Hi-Z. Valid Lane must
be held low until the next normal transmission. Note that keeping the transmitter toggling will
incur extra power penalty and should be applied with discretion.

\- In Strobe mode, the clock level in a clock-gated state for half-rate clocking (after meeting
postamble requirement) must alternate between differential high and differential low during
consecutive clock-gating events. For quarter-rate clocking, the clock level in a clock-gated
state must alternate between high and low for both phases (Phase-1 and Phase-2)
simultaneously. Transmitters must precondition the Data Lanes to a 0 or 1 (V) and clock must
drive a differential low for at least 1 UI or up to a maximum of 8 UIs for half- (quarter-) rate
clocking before the normal transmission. The total clock-gated period must be an integer
multiple of 8 UI. Example shown in Figure 5-67 and Figure 5-69.

\- In Continuous mode, the clock remains free running (examples shown in Figure 5-70).
Transmitters must precondition the Data Lanes to a 0 or 1 (V) for at least 1 UI or up to a
maximum of 8 UI. Total idle period must be an integer multiple of 8 UI.

Note:
Entry into and Exit from Hi-Z state are analog transitions. Hi-Z represents Transmitter
state and the actual voltage during this period will be pulled Low due to termination to
ground at the Receiver.

<figure>
<figcaption>Figure 5-67. Data, Clock, Valid Gated Levels for Half-rate Clocking: Terminated Link</figcaption>

Normal operation

Clock Postamble

Clock Gated (Multiple of 8 UI: N*8UI)

Normal operation

Clock

Parked Clock Level

Valid

Data: Hi-Z

Data[n]

D0

D1

D2

DB

D4

D5

D6

D7

D7

V

16 UI

1 UI to 8 UI

</figure>

<figure>
<figcaption>Figure 5-68. Data, Clock, Valid Gated Levels for Quarter-rate Clocking: Terminated Link</figcaption>

Normal operation

$\mathrm { C l o c k } \mathrm { P o s t a m b l }$

Clock Gated (Multiple of Valid frames: N*8UI)

Normal operation

Quad Clock

Phase -1

Parked Clock Level

Quad Clock

Phase - 2

Parked Clock Level

Valid

Data: Hi-Z

Data[n]

D0

D1

D2

DB

D4

D5

D6

D7

D7

32 UI

1 UI to 8 UI

</figure>

<figure>
<figcaption>Figure 5-69. Data, Clock, Valid Gated Levels for Half-rate Clocking: Continuous Clock Terminated Link</figcaption>

Normal operation

Free running (Multiple of 8 UI : N*8UI)

Normal operation

Clock

Valid

Data: Hi-Z

Data[n]

D0

D1

D2

DB

D4

D5

D6

D7

D7

V

16 UI

1 UI to 8 UI

</figure>

For data rates of 48 GT.s and 64 GT/s, the forwarded clock lanes must operate in continuous mode.
Hamming distance 4 encoding is utilized for Valid Framing, Retimers, and other potential applications.
At these data rates, it is required to implement double-error detection and single-error correction for
the Valid signal. This requirement aims to minimize the frequency of Link re-training events that are
caused by Valid framing errors, while ensuring a sufficiently low probability of failure. Table 4-1
describes the four legal Valid Framing encodings for retimers. For non-retimer links, only two of those
encodings are legal. A received value that is one bit different from one of those legal encodings is
corrected to that legal encoding. A received value that is two or more bits different from one of those
legal encodings is detected as a Valid framing error.

Track operation and Strobe mode:

· Track may be enabled during Link Training (MBTRAIN.RXCLKCAL) and when runtime recalibration
is requested

· When Track is enabled, both CLKP/N and Track will remain ON until the flow is complete

· Track may be enabled during mainband data transfer or during Electrical Idle state

. If Strobe mode is selected and runtime recalibration is on-going, the clock continues to toggle
even if the Idle state is entered, until the flow is complete

##### 5.12 Electrical Idle

Some training states need electrical idle when Transmitters and Receivers are waiting for generate
and receive patterns.

· Electrical idle on the mainband in this Specification is described as when Transmitters and
Receivers are enabled; Data, Valid and Track Lanes are held low and Clock is parked at high and
low.

##### 5.13 Sideband signaling

Each module supports a sideband interface. The sideband is a two-signal interface that is used for the
transmit and receive directions. The sideband data is an 800 MT/s single data rate signal with an 800-
MHz source. Channel reach of the sideband is the same as that of the main band, as defined in
Table 1-1 and Table 1-2, unless explicitly stated otherwise in the extended reach setting. The
extended reach setting must meet the Tx Driver Output Impedance specified in Table 5-33. Sideband
should run on power supply and clock derived from the auxiliary clock (AUXCLK) source which are
always on (VCCAON). See Section 5.13.2 for AUXCLK details.

Sideband data is sent edge aligned with the positive edge of the strobe. The Receiver must sample
the incoming data with the strobe. The negative edge of the strobe is used to sample the data as the
data uses single data rate signaling as shown in Figure 5-70. Sideband transmission is described in
Section 4.1.5.

For Advanced Package modules, redundancy is supported for the sideband interface. Sideband
initialization and repair are described in Section 4.5.3.2. There is no redundancy and no Lane repair
support on Standard Package modules.

<figure>
<figcaption>Figure 5-70. Sideband signaling</figcaption>

SB Clock

SB Message

</figure>

###### 5.13.1 Sideband Electrical Parameters

Table 5-33 shows the sideband electrical parameters.

It is strongly recommended that the two sides of the sideband I/O Link share the same power supply
rail.

s

<table>
<caption>Table 5-33. Sideband Parameters summary</caption>
<tr>
<th>Parameter</th>
<th>Min</th>
<th>Typ</th>
<th>Max</th>
<th>Unit</th>
</tr>
<tr>
<td>Supply voltage (VCCAON)ª</td>
<td>0.65</td>
<td></td>
<td></td>
<td>☒ V</td>
</tr>
<tr>
<td></td>
<td>0.8*VCCAON</td>
<td>—</td>
<td>—</td>
<td>☒ V</td>
</tr>
<tr>
<td>$\left( V _ { I H } \right)$</td>
<td>0.7*VCCAON</td>
<td></td>
<td></td>
<td>☒ V</td>
</tr>
<tr>
<td>Input low voltage (VIL)</td>
<td></td>
<td></td>
<td>0.3*VCCAON</td>
<td>☒ V</td>
</tr>
<tr>
<td>Output high voltage $\left( V _ { O H } \right)$</td>
<td>0.9*VCCCAON</td>
<td></td>
<td></td>
<td>☒ V</td>
</tr>
<tr>
<td>Output low voltage $\left( \mathrm { V } _ { \mathrm { O L } } \right)$</td>
<td></td>
<td></td>
<td>0.1*VCCAON</td>
<td>☒ V</td>
</tr>
<tr>
<td>$\text { Sideband Data } \mathrm { S e t u p } \mathrm { T i m e } ^ { \mathrm { t } }$</td>
<td>200</td>
<td>—</td>
<td>—</td>
<td>ps</td>
</tr>
<tr>
<td>Sideband Data Hold Timeb</td>
<td>200</td>
<td>—</td>
<td>—</td>
<td>ps</td>
</tr>
<tr>
<td>Rise/Fall time for Advanced Packagec, d</td>
<td>50</td>
<td>—</td>
<td>280</td>
<td>ps</td>
</tr>
<tr>
<td>Rise/Fall time for Standard Packagee, d</td>
<td>80</td>
<td>—</td>
<td>175</td>
<td>ps</td>
</tr>
<tr>
<td>Extended Reach Channel Length (Standard Package)</td>
<td></td>
<td></td>
<td>100</td>
<td>mm</td>
</tr>
<tr>
<td>Tx Driver Output Impedance for Extended Reachf</td>
<td></td>
<td></td>
<td>60</td>
<td>Ohms</td>
</tr>
</table>

a. Always On power supply. The guidelines for maximum Voltage presented in Section 1.5 apply to sideband signaling.

b. The Setup and Hold Times are referenced to the Sideband Data in relation to the falling edge of the Sideband Clock
at Sideband Rx.

c. 20 to 80% of VCCAON level with Advanced Package reference channel load.

d. This specification applies to sideband of channel length the same as that of the mainband.

e. 20 to 80% of VCCAON level with Standard Package reference channel load.

f. This specification is only required for enabling the extended reach sideband. The specification must be met across variations in
process, voltage, and temperature.

###### 5.13.2 Auxiliary Clock (AUXCLK)

Auxiliary clock (AUXCLK) may be from any clock source. Although other clock frequencies are
possible, it is recommended that every chiplet should also use a 100-MHz clock source. Table 5-34
lists the permitted auxiliary clock frequency range. The minimum and maximum frequencies listed in
the table indicate the limits, and do not indicate a requirement to support the entire frequency range.
Reference clock (REFCLK; see Section 5.1.2) can be used if it is always on. Spread-Spectrum Clocking
(SSC) is permitted. AUXCLK has relaxed tolerances compared to REFCLK.

<table>
<caption>Table 5-34. AUXCLK Frequency Parameters</caption>
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
<td>FAUXCLK</td>
<td>AUXCLK Frequency</td>
<td>25</td>
<td>100</td>
<td>800</td>
<td>MHz</td>
<td></td>
</tr>
</table>

##### 5.14 Open Drain

An Open-drain net is resistively pulled up and one or multiple drivers can pull down the net. Any of
the drivers can pull down the net such that all sinks will detect the net as low within the maximum fall
time. When all drivers have stopped pulling the net low, all sinks will detect the net as high within the
maximum rise time.

A chiplet can optionally support an Open Drain pin that connects to a common net. The Open Drain
has been specified for a pin connected to a common package route. This pin is not required to be on
the same die-edge as the UCIe macro. For an SiP with a small number of chiplets, it is possible for the
Open Drain to be routed on the substrate. It is recommended that SiP integrators perform the
necessary simulations to ensure functionality.

Figure 5-71 shows an example using Open Drain to connect 16 modules of 10 mm x 10 mm size with
5-mm separation. Note that this example assumes worst-case routing where a default package
resistor pull-up is on one end of the Open Drain net. Actual implementations may have more
optimized routing compared to the figure. This should allow for meeting the specifications in
Table 5-35 more easily.

<figure>
<figcaption>Figure 5-71. Example Package Route for Open Drain Signal</figcaption>

$R _ { p u l l - u p }$

15 mm

15 mm

15 mm

7.5 mm

2.5 mm

2.5 mm

2.5 mm

2.5 mm

10 x 10
mm2

$1 0 \times 1 0$
mm2

10 x 10
mm2

15 mm

10 x 10

mm2

2.5 mm

2.5 mm

2.5 mm

2.5 mm

15 mm

Chiplet

$1 0 \times 1 0$
$m m ^ { 2 }$

$1 0 \times 1 0$
$m m ^ { 2 }$

$1 0 \times 1 0$
mmª

$1 0 \times 1 0$
mm

15 mm

10 × 10
mmª

10 × 10

10 x 10
mm

10 × 10
mm

Approximately
250-mm total
routing length

$m m ^ { 4 }$

$2 . 5 \quad m m$

2.5 mm

2.5 mm

2.5 mm

10 × 10
mm2

10 × 10
mm2

10 × 10
mm2

10 x 10
mm2

15 mm

2.5 mm

2.5 mm

2.5 mm

2.5 mm

$1 5 \quad m m$

$1 5 \quad m m$

15 mm

7.5 mm

</figure>

<table>
<caption>Table 5-35. Open Drain Specification Summary</caption>
<tr>
<th>Parameter</th>
<th>Min</th>
<th>Typ</th>
<th>Max</th>
<th>Units</th>
<th>Notes</th>
</tr>
<tr>
<td>$R _ { \text { pull-down } }$</td>
<td>120</td>
<td>180</td>
<td>240</td>
<td>Ohms</td>
<td>a</td>
</tr>
<tr>
<td>$R _ { \mathrm { p u l l - u p } }$</td>
<td>5K</td>
<td>7.5K</td>
<td>10K</td>
<td>Ohms</td>
<td>a</td>
</tr>
<tr>
<td>$\left( V _ { H } \right)$</td>
<td>$0 . 7 ^ { * } V C C A O N$</td>
<td></td>
<td></td>
<td>V</td>
<td></td>
</tr>
<tr>
<td>Input low voltage $\left( \mathrm { V } _ { \mathrm { I L } } \right)$</td>
<td></td>
<td></td>
<td>0.3*VCCAON</td>
<td>V</td>
<td></td>
</tr>
<tr>
<td>Output high voltage $\left( \mathrm { V } _ { \mathrm { O H } } \right)$</td>
<td>0.9*VCCAON</td>
<td></td>
<td></td>
<td>V</td>
<td></td>
</tr>
<tr>
<td>Output low voltage $\left( \mathrm { V } _ { \mathrm { O L } } \right)$</td>
<td></td>
<td></td>
<td>0.1*VCCAON</td>
<td>V</td>
<td></td>
</tr>
<tr>
<td>Rise time</td>
<td>-</td>
<td>1.5</td>
<td>&lt;2.0</td>
<td>us</td>
<td>b</td>
</tr>
<tr>
<td>Fall time</td>
<td>-</td>
<td>30</td>
<td>&lt;100</td>
<td>ns</td>
<td>c</td>
</tr>
<tr>
<td>Pin Capacitance $\left( \mathrm { C } _ { \mathrm { D i n } } \right)$</td>
<td></td>
<td></td>
<td>1</td>
<td>$\mathrm { p F }$</td>
<td></td>
</tr>
</table>

Note: Requires typical package routing and default single pull-up resistor on package.

a. Ratio $R _ { \text { pull-down } } / \left( R _ { \text { pull-down } } + R _ { \text { pull-up } } \right)$ is important to meet $\mathrm { V } _ { \mathrm { O L } } .$ Any combination of Min/Max values meets the
requirements.

b. Rise time to $V _ { O H } < 2 .$

C.
Fall time to $V _ { O I } < 1 0 0 .$

The specification must be met across variations in process, voltage, and temperature.

###### 5.14.1 Open Drain Usage

Open Drain pins enable low-latency, bidirectional events. The Open Drain signals are used for some
specified UCIe low-latency events (see Section 8.4.2.1 and Section 8.4.2.2), as well as vendor-
defined events.

###### 5.14.2 External Open Drain Connections

The Open Drain specification is recommended to use for in-package routing. Systems that require
external event connections are recommended to use a separate pin for external event
communications. In this case, it is expected that one chiplet provides any associated bridging
between the internal Open Drain and the external event pin. Figure 5-72 shows an example of
bridging between internal Open Drain and external event pin. Although not shown in Figure 5-72, it is
possible that the external event pin is also bidirectional. Details of external Open Drain
implementation are beyond the scope of this specification.

<figure>
<figcaption>$F i g u r e \quad 5 - 7 2 .$ Example Bridging between Internal and External Event Pin</figcaption>

External
Event/Monitor

External
Event/Monitor

VCCAON

VCCAON

External Pin
(External
I/O Voltage)

ENB

$I / O +$
Bridge

Chiplet A

Chiplet B

Bridging Circuit

Chiplet C

Chiplet D

</figure>

# IMPLEMENTATION NOTE

## Bridging Circuit

If the event being communicated indicates that we are approaching or exceeding
standard operating conditions, it is advisable that the bridging circuitry be designed
to maintain functionality beyond standard operating conditions.

# 6.0 UCIe-3D

## 6.1 Introduction

Three-dimensional heterogeneously integrated technologies present an opportunity for the
development of new electronic systems with advantages of higher bandwidth and lower power as
compared to 2D and 2.5D architectures. 3D will enable applications where the scale of data
movement is impractical for monolithic, 2D, or 2.5D approaches.

Universal Chiplet Interconnect express for 3D packaging (UCIe-3D) is designed as a universally
applicable interface for 3D die-to-die communication. Figure 6-1 illustrates an example of two dies
stacked in a 3D configuration. UCIe-3D uses a two-dimensional array of interconnect bumps for data
transmission between dies.

<figure>
<figcaption>Figure 6-1. Example of 3D Die Stacking</figcaption>

Face-to-Face Hybrid Bonding

TSVs

Package Substrate

C4 Bumps

</figure>

## 6.2 UCIe-3D Features and Summary

While the UCIe 2D and 2.5D models strive for seamless plug-and-play interoperability, the UCIe-3D
model necessitates a more-integrated approach due to the inherent characteristics of packaging
technology. The objective is to offer a range of options or a "menu" from which users can select what
best suits their needs. The primary objectives and general methodology for UCIe-3D are as follows:

· Circuit and logic must fit within the bump area (i.e., UCIe will continue to be bump-limited). Given
the high density, this will translate to lower operating frequencies and a much-simplified circuit
(e.g., at 1-um bump-pitch, the UCIe-3D area amortized on a per-lane basis must be less than 1
um2).

. No D2D adapter. Low BER due to low-frequency and almost zero-channel distance - No CRC/
replay is needed.

. A hardened minimal PHY such as a simple inverter/driver. The SoC Logic connects directly to the
PHY.

· All debug/testability hooks are located within a common block (across all UCIe-3D Links) that is
connected to the SoC Logic network inside the chiplet.

. Lane repair becomes a bundle-wide repair that is orchestrated by the SoC Logic.

<figure>
<figcaption>Figure 6-2. UCIe-3D Illustration</figcaption>

PHY

PHY

PHY

Chiplet 0

SoC.

SoC

SoC

0

1

2

Logic

Logic

Logic

3

4

5

PHY

6

7

8

PHY

SoC

PHY

Logic

SoC

SoC
Logic

Chiplet

A

EC
G

1

2

2\.

Logic

TDPI

3

X

5

PHY

PHY

6

7:

B

8

Soc
Logic

SoC
Logic

PHY

SoC

Logic

(a)

(b)

Chiplets connected across each SoC with UCIe-3D.
A failure in UCIe-3D in either die results in the
remaining SoCs being routing around the failure.

Each chiplet has its own system controller logic,
I/Os, etc. Each SoC Logic connects to one or more
UCIe-3D PHY. The common test, debug, pattern,
and infrastructure (TDPI) block orchestrates
training, testing, debug, etc. across chiplets.

</figure>

<table>
<caption>Table 6-1 summarizes the key performance indicators of the proposed UCIe-3D. Table 6-1. UCIe-3D Key Performance Indicators (Sheet 1 of 2)</caption>
<tr>
<th>Characteristics/KPIs</th>
<th>UCIe-S</th>
<th>UCIe-A</th>
<th>UCIe-3D</th>
<th>Comments for UCIe-3D</th>
</tr>
<tr>
<td colspan="5">Characteristics</td>
</tr>
<tr>
<td>Data Rate (GT/s)</td>
<td colspan="2">4, 8, 12, 16, 24, 32, 48, 64</td>
<td>up to 4</td>
<td>· Equal to SoC Logic Frequency - power efficiency is critical</td>
</tr>
<tr>
<td>Width (each cluster)</td>
<td>16</td>
<td>64</td>
<td>80</td>
<td>· Options of reduced width to 70, 60, ...</td>
</tr>
<tr>
<td>Bump Pitch (um)</td>
<td>100 to 130</td>
<td>$2 5 \quad t o \quad 5 5$</td>
<td>≤ 10 (optimized) &gt; 10 to 25 (functional)</td>
<td>· Must scale such that UCIe-3D fits within the bump area · Must support hybrid bonding</td>
</tr>
<tr>
<td>$C h a n n e l \quad R e a c h$ (mm)</td>
<td>≤ 25</td>
<td>≤ 2</td>
<td>3D vertical</td>
<td>· F2F bonding initially; F2B, B2B, multi-stack possible</td>
</tr>
<tr>
<td colspan="5">Target for Key Metrics</td>
</tr>
<tr>
<td>$\begin{array}{} { \text { BW Die Edg } } \\ { \left( G B / s / m m \right) } \end{array}$</td>
<td>$2 8 \quad t o \quad 3 7 0$</td>
<td>$1 6 5 \quad t o \quad 2 6 3 4$</td>
<td>N/A (vertical)</td>
<td></td>
</tr>
<tr>
<td>$B W \quad D e n s i t y$</td>
<td>22 to 192</td>
<td>188 to 1646</td>
<td>4,000 at 9 um</td>
<td>· 4 TB/s/mm2 at 9 um · Approximately 12 TB/s/mm2 at 5 um · Approximately $3 5 T B / s / m m ^ { 2 }$ at 3 um · Approximately $3 0 0 T B / s / m m ^ { 2 }$ at 1 um</td>
</tr>
<tr>
<td>Power Efficiency Target (pJ/b)</td>
<td>$0 . 5 0 \quad t o$</td>
<td>0.25 to 0.50</td>
<td>$< 0 . 0 5 \quad a t \quad 9 \quad u m$</td>
<td>· Conservatively estimated at 9-um pitch · &lt; 0.02 for 3-um pitch</td>
</tr>
<tr>
<td>Low-power Entry/Exit</td>
<td colspan="2">0.5 ns at ≤ 16 GT/s $0 . 5 \text { ns to } 1 \text { ns at } \geq 2 4$</td>
<td>0 ns</td>
<td>· No preamble or postamble</td>
</tr>
</table>

<table>
<caption>Table 6-1. UCIe-3D Key Performance Indicators (Sheet 2 of 2)</caption>
<tr>
<th>Characteristics/KPIs</th>
<th>UCIe-S</th>
<th>UCIe-A</th>
<th>UCIe-3D</th>
<th>Comments for UCIe-3D</th>
</tr>
<tr>
<td>Latency $\left( T x + R x \right)$</td>
<td colspan="2">&lt; 2 ns $\left( P H Y + A d a p t e r \right)$ ≤ 0.75 ns (PHY 16 GT/s)</td>
<td>0.125 ns at 4 GT/s</td>
<td>· 0.5 UI, half of flop to flop</td>
</tr>
<tr>
<td>Reliability $\left( \mathrm { F I T } ^ { \mathrm { a } } \right)$</td>
<td colspan="3">$0 < F I T < < 1$</td>
<td>· $B E R < 1 E - 2 7$</td>
</tr>
<tr>
<td>ESD</td>
<td>$3 0 - V \quad C D M$</td>
<td></td>
<td>$5 - V C D M - > \leq 3 V$</td>
<td>· 5-V CDM at introduction . No ESD for wafer-to-wafer hybrid bonding possible</td>
</tr>
</table>

a. $F I T = F a i l u r e$ in Time.

## 6.3 UCIe-3D Tx, Rx, and Clocking

Figure 6-3 presents the Transceiver (Trx) architecture of UCIe-3D. A matched architecture as shown
in Figure 5-4, Figure 5-9, and Figure 5-15 offers optimal supply noise rejection. However, this comes
at the cost of increased power consumption. The architecture depicted in Figure 6-3 circumvents this
power penalty while maintaining the same level of supply noise rejection. The UCIe-3D specification
will establish target values and tolerances for clock distribution delays $D _ { 1 }$ and $D _ { 2 } .$

<figure>
<figcaption>Figure 6-3. UCIe-3D PHY</figcaption>

80x

Data Tx

Data $R x$

Channel

ClkTree

$D _ { 1 }$

$D _ { 2 }$

ClkTree

CLK

Clock Tx

Clock Rx

</figure>

It is important to highlight that UCIe-3D uses a rise-to-fall timing approach, differing from the typical
on-die logic design that uses a rise-to-rise timing approach. The primary distinction between these
two scenarios is that on-die logic must factor in the delay caused by combinational logic, whereas
UCIe-3D features matched data and clock buffer delays, resulting in a near-zero differential. As
depicted in Figure 6-4, rise-to-fall timing yields the most-optimal timing margin for zero-delay
differential.

<figure>
<figcaption>Figure 6-4. Start Edge and Sample Edge</figcaption>

1 UI

Rx Data Eye

$T x \quad C L K \left( r i s e \right) s t a r t$

$T x \quad C L K \left( f a l l \right)$

0.5 UI

Clockdelay

Data $\mathrm { d e l a y }$

Optimal sampling when
Data delay = Clock delay

0.5 UI

Rx CLK (rise)

Rx CLK (fall)
sample

</figure>

## 6.4 Electrical Specification

### 6.4.1 Timing Budget

Consideration of various factors such as jitter, noise, mismatch, and error terms are crucial for the link
timing budget. Table 6-2 outlines the UCIe-3D specification parameters that are pertinent to link
timing. Pulse width deviation from 50% clock period includes both static error (duty-cycle error) and
dynamic error (pulse-width jitter). Lane-to-lane skews account for the variation between data lanes,
and Data/Clock differential delays account for the clock to center of distribution of data lanes.

<table>
<caption>Table 6-2. Timing and Mismatch Specification (Sheet 1 of 2)</caption>
<tr>
<th>Specification</th>
<th>Name</th>
<th>Min</th>
<th>Typ</th>
<th>Max</th>
<th>Unit</th>
<th>$U I = 2 5 0 \quad p s$ at $4 \quad G T / s$</th>
<th>Note</th>
</tr>
<tr>
<td>Eye Closure due to Channel</td>
<td>$\mathrm { C } _ { \mathrm { h } }$</td>
<td></td>
<td>0.1</td>
<td></td>
<td>UI</td>
<td>$2 5 \quad p s$</td>
<td>a</td>
</tr>
<tr>
<td>Pulse-width Deviation from 50% Clock Period</td>
<td>$\mathrm { J } _ { \mathrm { p w } }$</td>
<td></td>
<td>0.08</td>
<td></td>
<td>UI pk-to-pk</td>
<td>20 ps</td>
<td></td>
</tr>
<tr>
<td>Tx Lane-to-Lane Skew</td>
<td>$\mathrm { S } _ { \mathrm { t x } }$</td>
<td></td>
<td>0.12</td>
<td></td>
<td>UI pk-to-pk</td>
<td>30 ps</td>
<td></td>
</tr>
<tr>
<td>Rx Lane-to-Lane Skew</td>
<td>$\mathrm { S } _ { \mathrm { r x } }$</td>
<td></td>
<td>0.12</td>
<td></td>
<td>UI pk-to-pk</td>
<td>30 $p s$</td>
<td></td>
</tr>
<tr>
<td>Tx Data/Clock Differential Delay</td>
<td>$D _ { t }$</td>
<td>$D _ { t x }$</td>
<td>$D _ { t x }$</td>
<td>Dtx_max</td>
<td>ps</td>
<td>$m a x \quad - \quad m i n = 5 0 \quad p s$</td>
<td rowspan="2">b</td>
</tr>
<tr>
<td>Rx Data/Clock Differential $\mathrm { D e l a y }$</td>
<td>$D _ { r x }$</td>
<td>$D _ { r x m i n }$</td>
<td>$D _ { r x _ { - } t y p }$</td>
<td>$D _ { r x m a x }$</td>
<td>ps</td>
<td>$m a x \quad - \quad m i n = 5 0 \quad p s$</td>
</tr>
<tr>
<td>$A l p h a \quad F a c t o r \left( T x \quad a n d \quad R x \right)$</td>
<td>$\alpha _ { t r x }$</td>
<td></td>
<td></td>
<td>1.5</td>
<td></td>
<td></td>
<td>c</td>
</tr>
<tr>
<td>Vcc Noise</td>
<td>$\mathrm { n } _ { \mathrm { v c c } }$</td>
<td></td>
<td></td>
<td>10</td>
<td>% pk-to-pk</td>
<td></td>
<td>d</td>
</tr>
</table>

<table>
<caption>Table 6-2. Timing and Mismatch Specification (Sheet 2 of 2)</caption>
<tr>
<th>Specification</th>
<th>Name</th>
<th>Min</th>
<th>Typ</th>
<th>Max</th>
<th>Unit</th>
<th>$U I = 2 5 0 \quad p s$ at 4 GT/s</th>
<th>Note</th>
</tr>
<tr>
<td>Tx Data/Clock Differential RJ</td>
<td>$J _ { r t x }$</td>
<td></td>
<td></td>
<td>0.05</td>
<td>UI pk-to-pk at BER</td>
<td>12.5 ps</td>
<td></td>
</tr>
<tr>
<td>Rx Data/Clock Differential RJ</td>
<td>$J _ { r r x }$</td>
<td></td>
<td></td>
<td>0.05</td>
<td>UI pk-to-pk at BER</td>
<td>12.5 ps</td>
<td></td>
</tr>
<tr>
<td>Sampling Aperture</td>
<td>$\mathrm { A } _ { \mathrm { p } }$</td>
<td></td>
<td></td>
<td>0.03</td>
<td>UI</td>
<td>7.5 ps</td>
<td></td>
</tr>
</table>

a. Eye closure due to channel includes inter-symbol interference (ISI) and crosstalk.

b. Defined as clock to mean data, min/typ/max values are shown below.

c. Alpha factor is defined as follows for Tx and Rx, respectively:

$$\alpha _ { T x } = \frac { d D _ { t x } } { D _ { t x } } / \frac { d V _ { C C } } { V _ { C C } } \quad \alpha _ { R x } = \frac { d D _ { r x } } { D _ { T X } } / \frac { d V _ { C C } } { V _ { C C } }$$

d. This is equivalent to a variation of ±5% in Vcc. Careful mitigation is particularly needed when disturbances external to UCIe
occur, such as electromagnetic coupling from through-silicon vias (TSVs).

Parameters $D _ { \mathrm { t x } }$ and $D _ { \mathrm { r x } }$ are Vcc-dependent functions. Equation 6-1 defines their typical values.

#### Equation 6-1.

$$D _ { t x \_ t y p } = D _ { r x \_ t y p } = \frac { V _ { c c } } { 0 . 0 1 5 3 V _ { c c } { } ^ { 2 } + 0 . 0 1 8 8 V _ { c c } - 0 . 0 0 8 4 }$$

where, unit of $D _ { t x _ { - } t y p }$ and $D _ { r x }$ $t y p$ is ps and unit of $V _ { C C }$ is $\mathrm { V } .$
☒

Equation 6-2 and Equation 6-3 define the minimum spec curve of $D _ { t x }$ and $D _ { r x } ,$ respectively.

##### Equation 6-2.

$$D _ { t x } { } _ { m i n } = m a x \left( D _ { t x } { } _ { t y p } - 0 . 0 8 U I _ { r } 0 \right)$$

###### Equation 6-3.

$$D _ { r x m i n } = m a x \left( D _ { r x } t y p - 0 . 0 8 U I , 0 \right)$$

Equation 6-4 and Equation 6-5 define the maximum spec curve of $D _ { t x }$ and $D _ { r x } ,$ respectively.

###### Equation 6-4.

$$D _ { t x m a x } = D _ { t x t y p } + 0 . 1 2 U I$$

Equation 6-5.

$$D _ { r x } { } _ { - } m a x = D _ { r x } { } _ { - } t y p + 0 . 1 2$$ ☒

Figure 6-5 illustrates a plot of the spec range for 4 GT/s.

<figure>
<figcaption>Figure 6-5. Dtx and Drx Spec Range for 4 GT/s</figcaption>

120

Spec Typ

100

Spec Max

$\mathrm { S p e c } M i r$

$\frac { x } { a } 4 0$ and Drx (ps)

80

60

20

0

0.5

0.55

0.6

0.65

0.7

0.75

0.8

0.85

Vcc (V)

</figure>

The equation for delay time, derived from the general theory of buffer chain, incorporates a term
proportional to Vcc and a quadratic Vcc dependence in the denominator. This equation is fitted to a
specific process and design. A typical design is expected to have the same trend, and remain within
the boundaries of the upper and lower curves. It is not required to align with the central curve.

Equation 6-6 is essential in closing the timing budget, subsequently leading to the defined
specification limit.

Equation 6-6.

$$C _ { h } + J _ { p w } + S _ { t x } + S _ { r x } + \sqrt { J _ { r t x } ^ { 2 } + J _ { r r x } ^ { 2 } } + A _ { p }$$
$$+ \left[ m a x \left( D _ { b x } \right) - m i n \left( D _ { b x } \right) + m a x \left( D _ { r x } \right) - m i n \left( D _ { r x } \right) \right] \left( 1 + \alpha _ { t r x } n _ { v c c } \right) < 1 U I$$

When there is a change in $\mathrm { V c c } ,$ as in the case of a dynamic voltage frequency scaling (DVFS) scenario,
the specification range for $D _ { \mathrm { t x } }$ and $D _ { r x }$ adjusts correspondingly. This offers a degree of design
flexibility because the delay does not need to conform to a fixed band across the entire Vcc range.
Given that the range from maximum to minimum remains constant, the timing margin remains
unaffected.

### 6.4.2 ESD and Energy Efficiency

Data and clock signals shall comply with a mask on an eye diagram that specifies the following:

· Minimum voltage swing

· Minimum duration during which the output voltage will be stable

· Maximum permitted overshoot and undershoot

The Tx output swing range is between 0.40 V and 0.75 V.

Table 6-3 defines the ESD targets.

<table>
<caption>Table 6-3. ESD Specification for ≤ 10 um Bump Pitch</caption>
<tr>
<th>Parameter</th>
<th>Minimum</th>
</tr>
<tr>
<td>Discharge voltage (CDM)</td>
<td>5 V</td>
</tr>
<tr>
<td>Discharge peak current</td>
<td>40 mA</td>
</tr>
</table>

The feasibility of 0-V ESD should be explored for the special case of wafer-to-wafer hybrid bonding.
For more details, see the Industry Council on ESD Targets white papers.

For > 10 um to < 25 um bump pitches, higher ESD can be permitted. The exact target will be
published in a future revision of the specification.

Table 6-4 lists the Energy Efficiency targets.

<table>
<caption>Table 6-4. Energy Efficiency Target</caption>
<tr>
<th>Bump Spacing (um)</th>
<th>Energy Efficiency at 4 GT/s (pJ/bit)</th>
</tr>
<tr>
<td>9</td>
<td>0.05</td>
</tr>
<tr>
<td>3</td>
<td>0.02</td>
</tr>
<tr>
<td>1</td>
<td>0.01</td>
</tr>
<tr>
<td>9 to 25</td>
<td>To be published in a future revision of the specification.</td>
</tr>
</table>

### 6.4.3 UCIe-3D Module and Bump Map

Figure 6-6 depicts a potential bump map for UCIe-3D. The arrangement of the signals is such that the
same PHY can be utilized on both the top die and bottom die. The unit used in Figure 6-6 is the bump
pitch. The estimated area for a x80 module (encompassing both Tx and Rx) in a 9-um pitch is
approximately 0.02 mm2. It is important to note that the area scales with the square of the bump
pitch.

<table>
<caption>Figure 6-6. UCIe-3D Module Bump Map</caption>
<tr>
<th></th>
<th>21</th>
<th>R00</th>
<th>R01</th>
<th>R02</th>
<th>R03</th>
<th>R04</th>
<th>VSS</th>
<th>R05</th>
<th>R06</th>
<th>R07</th>
<th>R08</th>
<th>R09</th>
</tr>
<tr>
<td rowspan="21"></td>
<td>20</td>
<td>R10</td>
<td>R11</td>
<td>R12</td>
<td>R13</td>
<td>R14</td>
<td>VSS</td>
<td>R15</td>
<td>R16</td>
<td>R17</td>
<td>R18</td>
<td>R19</td>
</tr>
<tr>
<td>19</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
</tr>
<tr>
<td>18</td>
<td>R20</td>
<td>R21</td>
<td>R22</td>
<td>R23</td>
<td>R24</td>
<td>VSS</td>
<td>R25</td>
<td>R26</td>
<td>$R 2 7$</td>
<td>R28</td>
<td>R29</td>
</tr>
<tr>
<td>17</td>
<td>R30</td>
<td>R31</td>
<td>R32</td>
<td>R33</td>
<td>R34</td>
<td>VSS</td>
<td>R35</td>
<td>R36</td>
<td>R37</td>
<td>R38</td>
<td>R39</td>
</tr>
<tr>
<td>16</td>
<td>R40</td>
<td>R41</td>
<td>R42</td>
<td>R43</td>
<td>R44</td>
<td>RXCK</td>
<td>R45</td>
<td>R46</td>
<td>R47</td>
<td>R48</td>
<td>R49</td>
</tr>
<tr>
<td>15</td>
<td>VSS</td>
<td>VSS</td>
<td>VSS</td>
<td>VSS</td>
<td>VSS</td>
<td>VSS</td>
<td>VSS</td>
<td>VSS</td>
<td>VSS</td>
<td>VSS</td>
<td>VSS</td>
</tr>
<tr>
<td>14</td>
<td>R50</td>
<td>R51</td>
<td>R52</td>
<td>R53</td>
<td>R54</td>
<td>VSS</td>
<td>R55</td>
<td>R56</td>
<td>R57</td>
<td>R58</td>
<td>R59</td>
</tr>
<tr>
<td>13</td>
<td>R60</td>
<td>R61</td>
<td>R62</td>
<td>R63</td>
<td>R64</td>
<td>VSS</td>
<td>R65</td>
<td>R66</td>
<td>R67</td>
<td>R68</td>
<td>R69</td>
</tr>
<tr>
<td>12</td>
<td>R70</td>
<td>R71</td>
<td>R72</td>
<td>R73</td>
<td>R74</td>
<td>VSS</td>
<td>R75</td>
<td>R76</td>
<td>R77</td>
<td>R78</td>
<td>R79</td>
</tr>
<tr>
<td>11</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
</tr>
<tr>
<td>10</td>
<td>T70</td>
<td>T71</td>
<td>T72</td>
<td>T73</td>
<td>T74</td>
<td>VSS</td>
<td>T75</td>
<td>T76</td>
<td>T77</td>
<td>T78</td>
<td>T79</td>
</tr>
<tr>
<td>9</td>
<td>T60</td>
<td>T61</td>
<td>T62</td>
<td>T63</td>
<td>T64</td>
<td>VSS</td>
<td>T65</td>
<td>T66</td>
<td>T67</td>
<td>T68</td>
<td>T69</td>
</tr>
<tr>
<td>8</td>
<td>T50</td>
<td>T51</td>
<td>T52</td>
<td>T53</td>
<td>T54</td>
<td>VSS</td>
<td>T55</td>
<td>T56</td>
<td>T57</td>
<td>T58</td>
<td>T59</td>
</tr>
<tr>
<td>7</td>
<td>VSS</td>
<td>VSS</td>
<td>VSS</td>
<td>VSS</td>
<td>VSS</td>
<td>VSS</td>
<td>VSS</td>
<td>VSS</td>
<td>VSS</td>
<td>VSS</td>
<td>VSS</td>
</tr>
<tr>
<td>6</td>
<td>T40</td>
<td>T41</td>
<td>T42</td>
<td>T43</td>
<td>T44</td>
<td>TXCK</td>
<td>T45</td>
<td>T46</td>
<td>T47</td>
<td>T48</td>
<td>T49</td>
</tr>
<tr>
<td>5</td>
<td>T30</td>
<td>T31</td>
<td>T32</td>
<td>T33</td>
<td>T34</td>
<td>VSS</td>
<td>T35</td>
<td>T36</td>
<td>T37</td>
<td>T38</td>
<td>T39</td>
</tr>
<tr>
<td>4</td>
<td>T20</td>
<td>T21</td>
<td>T22</td>
<td>T23</td>
<td>T24</td>
<td>VSS</td>
<td>T25</td>
<td>T26</td>
<td>T27</td>
<td>T28</td>
<td>T29</td>
</tr>
<tr>
<td>3</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
</tr>
<tr>
<td>2</td>
<td>T10</td>
<td>T11</td>
<td>T12</td>
<td>T13</td>
<td>T14</td>
<td>VSS</td>
<td>T15</td>
<td>T16</td>
<td>T17</td>
<td>T18</td>
<td>T19</td>
</tr>
<tr>
<td>1</td>
<td>T00</td>
<td>T01</td>
<td>T02</td>
<td>T03</td>
<td>T04</td>
<td>VSS</td>
<td>T05</td>
<td>T06</td>
<td>T07</td>
<td>T08</td>
<td>T09</td>
</tr>
<tr>
<td></td>
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
</tr>
</table>

<figure>

\-

VDS

VOD

\-

0

W

ER

\-

\-

W

M

\-

WA

4

\-

\-

\-

\-

\-

\-

\-

\-

4

v

\-

1

W

W

\-
m

\-

2

\-

\-

\-

6

4

.

5

1

m

m

\-

\-

W

A

\-

\-

\-

3

155

151

1

V

15

N

W

134

1

路

221

12%

129

100

VDO

VOO

WOO

154

VSS

115

15%

124

129

104

DO'S

106

</figure>

The UCIe-3D standard does not prescribe a mandatory bump pitch; however, a 9-um pitch is
recommended at introduction. As the technology advances, additional specific recommended pitch
values will be established.

Although UCIe-3D does not inherently predefine an adapter, users have the flexibility to allocate some
data lanes within the module for adapter functions as required, such as Valid, Data Mask, Parity, and
ECC. UCIe-3D does not necessitate a sideband for initialization. If a low-bandwidth data link similar to
sideband is required, it is up to the implementation to determine how to assign a group of lanes for
the purpose. Bit replication or other forms of redundancy can be used to guarantee link reliability.

If modules are physically adjacent, extra VDDs can be added between them to provide physical
separation, shielding, and additional power delivery.

Along with x80, the bump map of x70 Module is depicted in Figure 6-7. Bump maps of additional
Module widths may be incorporated in a future update to this specification if needed, using similar
layout.

<table>
<caption>Figure 6-7. x70 Module</caption>
<tr>
<th rowspan="20"></th>
<th>19</th>
<th>R00</th>
<th>R01</th>
<th>R02</th>
<th>R03</th>
<th>R04</th>
<th>VSS</th>
<th>R05</th>
<th>R06</th>
<th>R07</th>
<th>R08</th>
<th>R09</th>
<th rowspan="20"></th>
</tr>
<tr>
<td rowspan="2">18 17</td>
<td>R10</td>
<td>R11</td>
<td>R12</td>
<td>R13</td>
<td>R14</td>
<td>VSS</td>
<td>R15</td>
<td>R16</td>
<td>R17</td>
<td>R18</td>
<td>R19</td>
</tr>
<tr>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
</tr>
<tr>
<td>16</td>
<td>R20</td>
<td>R21</td>
<td>R22</td>
<td>R23</td>
<td>R24</td>
<td>VSS</td>
<td>R25</td>
<td>R26</td>
<td>R27</td>
<td>R28</td>
<td>R29</td>
</tr>
<tr>
<td>15</td>
<td>R30</td>
<td>R31</td>
<td>R32</td>
<td>R33</td>
<td>R34</td>
<td>VSS</td>
<td>R35</td>
<td>R36</td>
<td>R37</td>
<td>R38</td>
<td>R39</td>
</tr>
<tr>
<td>14</td>
<td>R40</td>
<td>R41</td>
<td>R42</td>
<td>R43</td>
<td>R44</td>
<td>RXCK</td>
<td>R45</td>
<td>R46</td>
<td>R47</td>
<td>R48</td>
<td>R49</td>
</tr>
<tr>
<td>13</td>
<td>VSS</td>
<td>VSS</td>
<td>VSS</td>
<td>VSS</td>
<td>VSS</td>
<td>VSS</td>
<td>VSS</td>
<td>VSS</td>
<td>VSS</td>
<td>VSS</td>
<td>VSS</td>
</tr>
<tr>
<td>12</td>
<td>R50</td>
<td>R51</td>
<td>R52</td>
<td>R53</td>
<td>R54</td>
<td>VSS</td>
<td>R55</td>
<td>R56</td>
<td>R57</td>
<td>R58</td>
<td>R59</td>
</tr>
<tr>
<td>11</td>
<td>R60</td>
<td>R61</td>
<td>R62</td>
<td>R63</td>
<td>R64</td>
<td>VSS</td>
<td>R65</td>
<td>R66</td>
<td>R67</td>
<td>R68</td>
<td>R69</td>
</tr>
<tr>
<td>10</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
</tr>
<tr>
<td>9</td>
<td>T60</td>
<td>T61</td>
<td>T62</td>
<td>T63</td>
<td>T64</td>
<td>VSS</td>
<td>T65</td>
<td>T66</td>
<td>T67</td>
<td>T68</td>
<td>T69</td>
</tr>
<tr>
<td>8</td>
<td>T50</td>
<td>T51</td>
<td>T52</td>
<td>T53</td>
<td>T54</td>
<td>VSS</td>
<td>T55</td>
<td>T56</td>
<td>T57</td>
<td>T58</td>
<td>T59</td>
</tr>
<tr>
<td>7</td>
<td>VSS</td>
<td>VSS</td>
<td>VSS</td>
<td>VSS</td>
<td>VSS</td>
<td>VSS</td>
<td>VSS</td>
<td>VSS</td>
<td>VSS</td>
<td>VSS</td>
<td>VSS</td>
</tr>
<tr>
<td>6</td>
<td>T40</td>
<td>T41</td>
<td>T42</td>
<td>T43</td>
<td>T44</td>
<td>TXCK</td>
<td>T45</td>
<td>T46</td>
<td>T47</td>
<td>T48</td>
<td>T49</td>
</tr>
<tr>
<td>5</td>
<td>T30</td>
<td>T31</td>
<td>T32</td>
<td>T33</td>
<td>T34</td>
<td>VSS</td>
<td>T35</td>
<td>T36</td>
<td>T37</td>
<td>T38</td>
<td>T39</td>
</tr>
<tr>
<td>4</td>
<td>T20</td>
<td>T21</td>
<td>T22</td>
<td>T23</td>
<td>T24</td>
<td>VSS</td>
<td>T25</td>
<td>T26</td>
<td>T27</td>
<td>T28</td>
<td>T29</td>
</tr>
<tr>
<td>3</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
<td>VDD</td>
</tr>
<tr>
<td>2</td>
<td>T10</td>
<td>T11</td>
<td>T12</td>
<td>T13</td>
<td>T14</td>
<td>VSS</td>
<td>₸15</td>
<td>T16</td>
<td>T17</td>
<td>T18</td>
<td>T19</td>
</tr>
<tr>
<td>1</td>
<td>TOO</td>
<td>T01</td>
<td>T02</td>
<td>T03</td>
<td>T04</td>
<td>VSS</td>
<td>T05</td>
<td>T06</td>
<td>T07</td>
<td>T08</td>
<td>T09</td>
</tr>
<tr>
<td></td>
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
</tr>
</table>

### 6.4.4 Repair Strategy

Defect size (more exactly, Si area impacted by a single defect) is defined by a probability distribution.
The size is influenced by factors such as numbers of I/Os in SoC, packaging technology used, and
bump pitch. A standard needs to cover technologies from multiple companies, scalable to future bump
pitches, as well as different SoC sizes. Lane repair based on fixed defect size is not practical for an
effective standard.

Given these considerations, a bundle repair strategy is proposed for UCIe-3D. This involves reserving
bundles within the SoC for repair purposes, which can be rerouted to serve as backup in the event of
a failure, as illustrated in Figure 6-8. The figure shows the cases of no repair, 1-bundle repair, and 4-
bundle repairs. For a densely packed 2D UCIe Module array, it is recommended to reserve two full
Modules (equivalent to four bundles) to repair a single failure. This assumes an alternating
arrangement of Tx and Rx bundles in at least one direction. Each Module is equipped with one Tx
bundle (comprising a x80 Tx + Clock) and one Rx bundle (comprising a x80 Rx + Clock).

Figure 6-8.
Bundle Repair

<table>
<tr>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
</table>

<figure>

Unrepaired Row

0

1

2

3

Unused spare bundles

Repaired Row
2

0

3

1
Unused

Bundle
with defect

Re-route to spare

Repaired Rows
2
3

0

1

Bundles with defect

Re-route to spare

</figure>

To scale the general case of a large number of UCIe links, the following mathematical model can be
used to compute the repair requirements:

Parameters:

. Do represents the defect density of the interconnect, expressed in terms of the number of failures
per unit area

· A signifies the total UCIe-3D area of the chip

· 8 denotes the acceptable yield loss

The model suggests reserving 2k full Modules, where $\mathrm { k }$ is determined by the subsequent equation.

Equation 6-7.

$$1 - \sum _ { i = 0 } ^ { k } P _ { i } \left( A D _ { 0 } \right) < 8$$

#### Equation 6-8.

$$P _ { i } \left( x \right) = \frac { x ^ { i } } { i ! } e ^ { - x }$$ ☒ ☒

The calculations in Equation 6-7 and Equation 6-8 assume that large interconnect defects that are
comparable to bundle size are relatively rare. More spare bundles may be needed if density of large
defects exceeds a limit such that Equation 6-9 does not hold.

#### Equation 6-9.

$$1 - e ^ { - A D _ { 1 } } < 8$$

where, $\mathrm { D } _ { 1 }$ is the density of defects with diameter greater than the bundle dimension. The exact
amount can be determined by simulation.

When UCIe-3D links are not densely packed, strategic placement of spacing between bundles can
effectively reduce the number of repair bundles required. For example, with sufficient spacing
between rows, the occurrence of a single defect eliminating four bundles can be prevented. However,
the precise determination of this spacing is highly dependent on the specific technology in use, and
thus, falls beyond the scope of this specification. The specification merely highlights this as a potential
option.

The initiation of repair is anticipated to originate from the SoC Logic, which is external to the UCIe-3D
PHY, and therefore is not elaborated on in this context. The implementation can be specific to the
system.

## 6.4.5 Channel and Data Rate Extension

While the immediate focus of UCIe-3D is on Face-to-Face hybrid bonding, the proposed architecture is
designed to be adaptable for Face-to-Back, Back-to-Back, and multi-stack configurations.
Comprehensive channel and circuit simulations are necessary to determine the optimal data rate for
these scenarios. Reduction of 10% or less in data rate is expected for Face-to-Back and Back-to-Back
configurations.

§ §

# 7.0 Sideband

## 7.1 Protocol Specification

The usage for the sideband Link is to provide a out of band channel for Link training and an interface
for sideband access of registers of the Link partner. It is also used for Link Management Packets and
parameter exchanges with remote Link partner.

The same protocol is also used for local die sideband accesses over FDI and RDI. When relevant, FDI
specific rules are pointed out using "FDI sideband:". When relevant, RDI specific rules are pointed out
using "RDI sideband:". When relevant, UCIe Link specific rules are pointed out using "UCIe Link
sideband:". If no prefix is mentioned, it is a common rule across FDI, RDI and UCIe Link.

The Physical Layer is responsible for framing and transporting sideband packets over the UCIe Link.
Direct sideband access to remote die can originate from the Adapter or the Physical Layer. The
Adapter forwards a remote die sideband access over RDI to the Physical Layer for framing and
transport. These include register access requests, completions or messages.

The Protocol Layer has indirect access to remote die registers using the sideband mailbox mechanism.
The mailbox registers reside in the Adapter, and it is the responsibility of the Adapter to initiate
remote die register access requests when it receives the corresponding access trigger for the mailbox
register over FDI.

FDI sideband: In the case of multi-protocol stacks, the Adapter must track which protocol stack sent
the original request and route the completion back to the appropriate protocol stack.

FDI sideband: Because the Protocol Layer is only permitted indirect access to remote die registers,
and direct access to local die registers, currently only Register Access requests and completions are
permitted on the FDI sideband.

All sideband requests that expect a response have an 8ms timeout. A "Stall" encoding is provided for
the relevant packets for Retimers, to prevent timeouts if the Retimer needs extra time to respond to
the request. When stalling to prevent timeouts, it is the responsibility of the Retimer to send the
corresponding Stall response once every 4ms. The Retimer must also ensure that it does not Stall
indefinitely, and escalates a Link down event after a reasonable attempt to complete resolution that
required stalling the requester. If a requester receives a response with a "Stall" encoding, it resets the
timeout counter.

In certain cases, it is necessary for registers to be fragmented between the different layers; i.e.,
certain bits of a given register physically reside in the Protocol Layer, other bits reside in the Adapter,
and other bits reside in the Physical Layer. UCIe takes a hierarchical decoding for these registers. For
fragmented registers, if a bit does not physically reside in a given Layer, it implements that bit as
Read Only and tied to 0. Hence reads would return 0 for those bits from that Layer, and writes would
have no effect on those bits. As an example, for reads, Protocol Layer would forward these requests
to the Adapter on FDI and the Protocol Layer will OR the data responded by the Adapter with its local
register before responding to software. The Adapter must do the same if any bits of that register
reside in the Physical Layer before responding to the Protocol Layer.

### 7.1.1 Sideband Packet Types

Five different categories of sideband packets are permitted:

· Register Accesses: These can be Configuration (CFG) or Memory Mapped accesses for both Reads
or Writes are supported. These can be associated with 32b of data or 64b of data. All register
accesses (Reads or Writes) have an associated completion.

· Messages without data: These can be Link Management (LM), or Vendor Defined Packets. These
do not carry additional data payloads.

· Messages with data: These can be Parameter Exchange (PE), Link Training related or Vendor
Defined, and carry 64b of data.

· Management Transport Messages: If Management Transport protocol is supported, Management
Transport Messages with data or without data are supported (see Section 7.1.2.4 and
Section 7.1.2.5, respectively).

· Priority Sideband Traffic Packets (PSTP): These are sideband packets that carry priority messages
to the remote Link partner (see Section 4.1.5.2 for the rules related to transmitting these
sideband packets, and Figure 7-14 for the format of a PSTP).

Every sideband packet type carries a 5-bit opcode. Every sideband packet type, with the exception of
a PSTP, also carries a 3-bit source identifier (srcid), and a 3-bit destination identifier (dstid). The 5-bit
opcode indicates the sideband packet type, as well as whether the sideband packet carries no data,
32b of data or 64b of data.

Table 7-1 gives the mapping of opcode encodings to the Sideband Packet Types.

<table>
<caption>Table 7-1. Sideband Packet Opcode Encodings Mapped to Sideband Packet Types</caption>
<tr>
<th>Opcode Encoding</th>
<th>Sideband Packet Type</th>
<th>Opcode Encoding</th>
<th>Sideband Packet Type</th>
</tr>
<tr>
<td>00000b</td>
<td>32b Memory Read</td>
<td>01101b</td>
<td>64b Configuration Write</td>
</tr>
<tr>
<td>00001b</td>
<td>32b Memory Write</td>
<td>10000b</td>
<td>Completion without Data</td>
</tr>
<tr>
<td>00010b</td>
<td>32b DMS Register Read</td>
<td>10001b</td>
<td>Completion with 32b Data</td>
</tr>
<tr>
<td>00011b</td>
<td>32b DMS Register Write</td>
<td>10010b</td>
<td>Message without Data</td>
</tr>
<tr>
<td>00100b</td>
<td>32b Configuration Read</td>
<td>10111b</td>
<td>Management Port Messages without Data</td>
</tr>
<tr>
<td>00101b</td>
<td>32b Configuration Write</td>
<td>11000b</td>
<td>Management Port Message with Data</td>
</tr>
<tr>
<td>01000b</td>
<td>64b Memory Read</td>
<td>11001b</td>
<td>Completion with 64b Data</td>
</tr>
<tr>
<td>01001b</td>
<td>64b Memory Write</td>
<td>11011b</td>
<td>Message with 64b Data</td>
</tr>
<tr>
<td>01010b</td>
<td>64b DMS Register Read</td>
<td>11110b</td>
<td>Priority Packet (see Section 4.1.5.2 for details)ª</td>
</tr>
<tr>
<td>01011b</td>
<td>64b DMS Register Write</td>
<td>11111b</td>
<td>Priority Packet (see Section 4.1.5.2 for details)ª</td>
</tr>
<tr>
<td>01100b</td>
<td>64b Configuration Read</td>
<td>Other encodings</td>
<td>Reserved</td>
</tr>
</table>

a. The Priority Packet headers are of a different size compared to other sideband packets, which causes the parity bit location to
be different for them. With a BER of 1E-27 on the sideband Link, it is required to prevent single bit errors on the Link from causing
aliasing between priority packets and other sideband packets. This relies on the opcode field plus bit [5] and bit [6] requiring
more than one bit flip to change between priority packet format and non-priority packet format types. Future packet changes/
additions must take this into account and prevent aliasing for any new packet additions/changes.

$T a b l e \quad 7 - 2 , T a b l e \quad 7 - 3 ,$ and Table 7-4 give the encodings of source and destination identifiers. It is not
permitted for Protocol Layer from one side of the Link to directly access Protocol Layer of the remote
Link partner over sideband (this should be done via mainband).

<table>
<caption>Table 7-2. FDI sideband: srcid and dstid encodings on FDI</caption>
<tr>
<th>Fieldª</th>
<th>Description</th>
</tr>
<tr>
<td>$\mathrm { s r c i d } \left[ 2 : 0 \right]$</td>
<td>000b: Stack 0 Protocol Layer 100b: Stack 1 Protocol Layer other encodings are reserved.</td>
</tr>
<tr>
<td>dstid[2:0]</td>
<td>001b: D2D Adapter 010b: Physical Layer other encodings are reserved.</td>
</tr>
</table>

a. srcid and dstid are Reserved for completion messages transferred over FDI. The Protocol Layer must correlate
the completions to original requests using the Tag field. Currently, no requests are permitted from Adapter to
Protocol Layer over FDI sideband.

<table>
<caption>Table 7-3. RDI sideband: srcid and dstid encodings on RDI</caption>
<tr>
<th>Fieldª</th>
<th>Description</th>
</tr>
<tr>
<td>$s r c i d \left[ 2 : 0 \right]$</td>
<td>000b: Stack 0 Protocol Layer 001b: D2D Adapter 011b: Management Port Gateway (see Section 8.2) 100b: Stack 1 Protocol Layer other encodings are reserved.</td>
</tr>
<tr>
<td rowspan="2">$d s t i d \left[ 2 \right]$</td>
<td>$O b : L o c a l \quad d i e \quad t e r m i n a t e d \quad r e q u e s t$</td>
</tr>
<tr>
<td>1b: Remote die terminated</td>
</tr>
<tr>
<td rowspan="4">$\mathrm { d s t i d } \left[ 1 : 0 \right]$</td>
<td>For Local die terminated requests: 10b: Physical Layer other encodings are reserved.</td>
</tr>
<tr>
<td>For Remote die terminated Register Access Requests: dstid[1:0] is Reserved</td>
</tr>
<tr>
<td>For Remote die terminated Register Access Completions: 01b: D2D Adapter other encodings are reserved.</td>
</tr>
<tr>
<td>For Remote die terminated messages: message $1 0 b : P h y s i c a l \quad L a y e r \quad m e s s a g e$ 11b: message (see Section 8.2)</td>
</tr>
</table>

a. srcid and dstid are Reserved for completion messages transferred over RDI for local Register Access
completions. For Register Access completions, the Adapter must correlate the completions to original requests
using the Tag field regardless of dstid field. Both local and remote Register Access requests are mastered by
the Adapter with unique Tag encodings.

<table>
<caption>Table 7-4. UCIe Link sideband: srcid and dstid encodings for UCIe Link</caption>
<tr>
<th>Field</th>
<th>Description</th>
</tr>
<tr>
<td>$\mathrm { s r c i d } \left[ 2 : 0 \right]$</td>
<td>001b: D2D Adapter 010b: Physical Layer 011b: Management Port Gateway (see Section 8.2)</td>
</tr>
<tr>
<td rowspan="2">$\mathrm { d s t i d } \left[ 2 \right]$</td>
<td>$1 b : R e m o t e \quad d i e \quad t e r m i n a t e d \quad r e q u e s t$</td>
</tr>
<tr>
<td>other encodings are reserved</td>
</tr>
<tr>
<td rowspan="3">$\mathrm { d s t i d } \left[ 1 : 0 \right]$</td>
<td>For Register Access requests: dstid[1:0] is Reserved.</td>
</tr>
<tr>
<td>$F o r \quad R e m o t e \quad d i e \quad t e r m i n a t e d \quad R e g i s t e r \quad A c c e s s \quad C o m p l e t i o n s :$ 01b: D2D Adapter other encodings are reserved.</td>
</tr>
<tr>
<td>For Remote die terminated messages: 01b: D2D Adapter message $1 0 b : P h y s i c a l \quad L a y e r \quad m e s s a g e$ message (see Section 8.2)</td>
</tr>
</table>

### 7.1.2 Sideband Packet Formats

All the figures in this section show examples assuming a 32-bit interface of RDI/FDI transfer for
sideband packets, hence the headers and data are shown in Phases of 32 bits.

Note that the sideband packet format figures provided in this chapter show the packet format over
multiple 32-bit Phases. This is for representation purposes only. For transport over the UCIe sideband
bumps (serial interface), the transfer occurs as a 64-bit serial packet at a time. For headers, the
transmission order is bit 0 of Phase 0 as bit 0 of the serial packet (D0 in Figure 4-7), bit 1 of Phase 0
as bit 1 of the serial packet, etc., followed by bit 0 of Phase 1 as bit 32 of the serial packet, bit 1 of
Phase 1 as bit 33 of the serial packet, etc., until bit 31 of Phase 1 as bit 63 of the serial packet.

Data (if present) is sent as a subsequent serial packet, with bit 0 of Phase 2 as bit 0 of the serial
packet (D0 in Figure 4-7), bit 1 of Phase 2 as bit 1 of the serial packet, etc., followed by bit 0 of Phase
3 as bit 32 of the serial packet, bit 1 of Phase 3 as bit 33 of the serial packet, etc., until bit 31 of Phase
3 as bit 63 of the serial packet.

### 7.1.2.1 Register Access Packets

Figure 7-1 shows the packet format for Register Access requests. Table 7-5 gives the description of
the fields other than the opcode, srcid, and dstid.

<table>
<caption>Table 7-5. Field descriptions for Register Access Requests</caption>
<tr>
<th>Field</th>
<th>Description</th>
</tr>
<tr>
<td>CP</td>
<td>Control Parity (CP) is the even parity of all the header bits excluding DP.</td>
</tr>
<tr>
<td>DP</td>
<td>Data Parity is the even parity of all bits in the data payload. If there is no data payload, this bit is set to 0b.</td>
</tr>
<tr>
<td>Cr</td>
<td>If 1b, indicates one credit return for credited sideband messages. This field is only used by the Adapter for remote Link partner's credit returns for E2E credits. It is not used for local FDI or RDI credit loops.</td>
</tr>
<tr>
<td>$A d d r \left[ 2 3 : 0 \right]$</td>
<td>$\begin{array}{} { \text { Address of the request } } \\ { \text { Table } 7 - 6 \text { for details. } } \end{array} .$ Different opcodes use this field differently. See The following rules apply for the address field: For 64-bit request, Addr[2:0] is reserved.</td>
</tr>
<tr>
<td>$B E \left[ 7 : 0 \right]$</td>
<td>$B y t e \quad E n a b l e s \quad f o r \quad t h e \quad R e q u e s t . I t \quad i s \quad N O T \quad r e q u i r e d \quad t o \quad b e \quad c o n t i g u o u s .$</td>
</tr>
<tr>
<td>$E P$</td>
<td>Data Poison. If poison forwarding is enabled, the completer can poison the data on internal errors. Setting the EP bit is optional, the conditions for setting it to 1 are implementation-specific. Typical usages involve giving additional FIT protection against data integrity errors on internal data buffers. A Receiver must not modify the contents of the target location for requests with data payload that have the EP bit set. It must return UR for the completion status of requests with an EP bit set.</td>
</tr>
<tr>
<td>$\mathrm { T a a r } \left[ 4 : 0 \right]$</td>
<td>$\log$ generated by the requester, and it must be unique for all outstanding requests that require a completion. The original requester uses the Tag to associate returning completions with the original request.</td>
</tr>
<tr>
<td>Data</td>
<td>Payload. Can be 32 bits or 64 bits wide depending on the Opcode.</td>
</tr>
</table>

<table>
<caption>Table 7-6. Mapping of Addr[23:0] for Different Requests</caption>
<tr>
<th>Opcode</th>
<th>Description</th>
</tr>
<tr>
<td>Memory Reads/Writes</td>
<td>$R L \left[ 3 : 0 \right] ,$ Offset[19:0]} Offset is the Byte Offset. RL[3:0] encodings are as follows: 0h: Register Locator 0 1 $2 h : R e g i s t e r \quad L o c a t o r \quad 2$ 3h: Register Locator 3 Fh: Accesses for Protocol specific MMIO registers that are shadowed in the Adapter (e.g., ARB/MUX registers defined in the CXL Specification). The offsets for these registers are implementation specific, and the protocol layer must translate accesses to match the offsets implemented in the Adapter. Other encodings are reserved. For accesses to Reserved RL encodings, the completer must respond with a UR.</td>
</tr>
<tr>
<td>Configuration Reads/Writes</td>
<td>{RL[3:0], Rsvd[7:0], Byte Offset[11:0]}, where RL[3:0] encodings are as follows: 0h: UCIe Link DVSEC Fh: Accesses for Protocol specific configuration registers that are shadowed in the Adapter (e.g., ARB/MUX registers defined in the CXL Specification). The offsets for these registers are implementation specific, and the protocol layer must translate accesses to match the offsets implemented in the Adapter. Other encodings are reserved. For accesses to Reserved RL encodings, the completer must respond with a UR.</td>
</tr>
<tr>
<td>DMS Register Reads/Writes</td>
<td>These allow for accessing the DMS registers implemented in UCIe Spoke Type 0, 1, or 2. Addr[21:0] provides the register offset in DMS register space, relative to the start of the Spoke's register space, that corresponds to the DevID. A maximum of 4 MB of address space is possible for UCIe D2D/PHY Spokes. These opcodes are always targeted at the local D2D or PHY registers (i.e., these opcodes never target the remote link partner). Addr[23:22] encodings are as follows: 00b: Spoke registers. 01b: Reserved. 10b: Reserved. 11b: Used for other chiplet UMAP registers that are shadowed in the D2D or PHY, if any. The definitions of these registers and offsets are implementation- specific.</td>
</tr>
</table>

<table>
<caption>Figure 7-1. Format for Register Access Request</caption>
<tr>
<td colspan="20">Register Access Request</td>
</tr>
<tr>
<td>Bytes</td>
<td colspan="5">3</td>
<td colspan="2"></td>
<td colspan="2">2</td>
<td colspan="2"></td>
<td colspan="3">1</td>
<td colspan="5">0</td>
</tr>
<tr>
<td>Bits</td>
<td>31</td>
<td colspan="2">30 29</td>
<td>28 27</td>
<td>26 25 24</td>
<td>23 22</td>
<td>21 20</td>
<td>19</td>
<td>18</td>
<td>17</td>
<td>16</td>
<td>15 14</td>
<td>13 12 11 10</td>
<td>9 8</td>
<td>7 6</td>
<td colspan="2">5 4 3 2</td>
<td>10</td>
<td></td>
</tr>
<tr>
<td>Header / Data</td>
<td colspan="19">Header</td>
</tr>
<tr>
<td>Phase0</td>
<td colspan="3">srcid</td>
<td>rsvd</td>
<td colspan="2">tag[4:0]</td>
<td colspan="6">be[7:0]</td>
<td colspan="2">rsvd</td>
<td></td>
<td colspan="4">ep opcode [4:0]</td>
</tr>
<tr>
<td>Phase1</td>
<td>dp</td>
<td>cp</td>
<td>|cr</td>
<td>rsvd</td>
<td>dstid</td>
<td colspan="2"></td>
<td colspan="4"></td>
<td></td>
<td colspan="2">addr[23:0]</td>
<td></td>
<td></td>
<td></td>
<td colspan="2"></td>
</tr>
<tr>
<td>Header / Data</td>
<td colspan="19">Data (if applicable, can be 32 bits or 64 bits)</td>
</tr>
<tr>
<td>Phase2</td>
<td colspan="19">data[31:0]</td>
</tr>
<tr>
<td>Phase3</td>
<td></td>
<td colspan="8"></td>
<td colspan="3">data[63:32]</td>
<td colspan="7"></td>
</tr>
</table>

<figure>
</figure>

<table>
<caption>Figure 7-2 gives the format for Register Access completions. Figure 7-2. Format for Register Access Completions</caption>
<tr>
<th colspan="22">Register Access Completions</th>
</tr>
<tr>
<th>Bytes</th>
<th colspan="5">3</th>
<th colspan="2">2</th>
<th colspan="2"></th>
<th colspan="2"></th>
<th colspan="4">1</th>
<th colspan="6">0</th>
</tr>
<tr>
<td>Bits</td>
<td>31</td>
<td>30</td>
<td>29</td>
<td>28 27</td>
<td>26 25 24</td>
<td colspan="2">23 22 21 20 19</td>
<td>18 17</td>
<td>16</td>
<td>15</td>
<td>14</td>
<td>13</td>
<td>12 11</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>109876543210</td>
<td></td>
</tr>
<tr>
<td>Header / Data</td>
<td colspan="5"></td>
<td colspan="2"></td>
<td colspan="4">Header</td>
<td colspan="4"></td>
<td colspan="6"></td>
</tr>
<tr>
<td>Phase0</td>
<td colspan="3">srcid</td>
<td>rsvd</td>
<td colspan="2">tag[4:0]</td>
<td colspan="3">be[7:0]</td>
<td colspan="2"></td>
<td colspan="3">rsvd</td>
<td></td>
<td></td>
<td></td>
<td>ep</td>
<td colspan="3">opcode [4:0]</td>
</tr>
<tr>
<td>Phase1</td>
<td>dp</td>
<td>cp</td>
<td>cr</td>
<td>rsvd</td>
<td>dstid</td>
<td colspan="2"></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td colspan="2">rsvd</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td colspan="2">Status</td>
</tr>
<tr>
<td>Header / Data</td>
<td colspan="3"></td>
<td></td>
<td colspan="11">Data (if completion with data, can be 32 bits or 64 bits)</td>
<td colspan="6"></td>
</tr>
<tr>
<td>Phase2</td>
<td colspan="7"></td>
<td colspan="8">data[31:0]</td>
<td></td>
<td></td>
<td colspan="4"></td>
</tr>
<tr>
<td>Phase3</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td colspan="2"></td>
<td></td>
<td colspan="3">data [63:32]</td>
<td colspan="3"></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td colspan="2"></td>
</tr>
</table>

<table>
<caption>Table 7-7 gives the field descriptions for a completion. Table 7-7. Field Descriptions for a Completion</caption>
<tr>
<th>Field</th>
<th>Description</th>
</tr>
<tr>
<td>$\mathrm { T a g } \left[ 4 : 0 \right]$</td>
<td>Completion Tag associated with the corresponding Request. The requester uses this to associate the completion with the original request.</td>
</tr>
<tr>
<td>CP</td>
<td>$\begin{array}{} { \text { Control Parity. All fields other than whan when vand crothe the the Header are pretected by Control } } \\ { \text { Parity, and the parity sarity schene is even \left(including reserved bits\right). } } \end{array}$</td>
</tr>
<tr>
<td>DP</td>
<td>Data Parity. All fields in data are protected by data parity, and the parity scheme is even.</td>
</tr>
<tr>
<td>$\mathrm { C r }$</td>
<td>If 1b, indicates one credit return for credited sideband messages. This field is only used by the Adapter for remote Link partner's credit returns for E2E credits. It is not used for local FDI or RDI credit loops.</td>
</tr>
<tr>
<td rowspan="2">$E P$</td>
<td>Data Poison. If poison forwarding is enabled, the completer can poison the data on internal errors.</td>
</tr>
<tr>
<td>Setting the EP bit is optional, the conditions for setting it to 1 are implementation-specific. Typical usages involve giving additional FIT protection against data integrity errors on internal data buffers. A Receiver must not modify the contents of the target location for requests with data payload that have the EP bit set. It must return UR for the completion status of requests with an EP bit set.</td>
</tr>
<tr>
<td>$B E \left[ 7 : 0 \right]$</td>
<td>Byte Enables for the Request. Completer returns the same value that the original request had (this avoids the requester from having to save off the BE value). BE[7:4] are reserved if the opcode is for a 32-bit request.</td>
</tr>
<tr>
<td rowspan="2">$S t a t u s \left[ 2 : 0 \right]$</td>
<td>Completion Status 000b - Successful Completion (SC). This can be a completion with or without data, depending on the original request (it must set the appropriate Opcode). If the original request was a write, it is a completion without data. If the original request was a read, it is a completion with data. 001b - Unsupported Request (UR). On UCIe, this is a completion with 64b Data when a request is aborted by the completer, and the Data carries the original request header that resulted in UR. This enables easier header logging at the requester. Register Access requests that timeout must also return UR status, but for those the completion is without Data.</td>
</tr>
<tr>
<td>100b - Completer Abort (CA). On UCIe, this is a completion with 64b Data, and the Data the requester. carries original request header that resulted in CA. This enables easier header logging at 111b - Stall. Receiving a completion with Stall encoding must reset the timeout at the original request. requester. Completer must send a Stall once every 4ms if it is not ready to respond to the Other encodings are reserved. An error is logged in the Sideband Mailbox Status if a CA was received or if the number of timeouts exceed the programmed threshold. For timeouts below the programmed threshold, a UR is returned to the requester.</td>
</tr>
<tr>
<td>Data</td>
<td>Payload. 32 bits or 64 bits depending on the Opcode.</td>
</tr>
</table>

### 7.1.2.2 Messages without Data

Figure 7-3 shows the Format for Messages without data payloads. These can be Link Management
Packets, NOPs or Vendor Defined message packets.

<table>
<caption>Figure 7-3. Format for Messages without Data</caption>
<tr>
<th colspan="23">Messages without Data</th>
</tr>
<tr>
<th>Bytes</th>
<th colspan="3">3</th>
<th colspan="3"></th>
<th>2</th>
<th></th>
<th colspan="2"></th>
<th></th>
<th colspan="5">1</th>
<th colspan="4">0</th>
<th></th>
<th></th>
</tr>
<tr>
<td>Bits</td>
<td>31 30 29 28 27</td>
<td>26</td>
<td>25 24</td>
<td>23</td>
<td>22</td>
<td>21 20</td>
<td>19</td>
<td>18</td>
<td>17</td>
<td>16</td>
<td>15</td>
<td>14</td>
<td>13 12</td>
<td>11</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>109876543210</td>
<td></td>
<td></td>
<td></td>
</tr>
</table>

Header / Data

Header

<table>
<tr>
<th>Phase0</th>
<th></th>
<th>srcid</th>
<th>rsvd</th>
<th>rsvd</th>
<th>msgcode [7:0]</th>
<th>rsvd</th>
<th>opcode [4:0]</th>
</tr>
<tr>
<td>Phase1</td>
<td>dp</td>
<td>|cp</td>
<td>rsvd</td>
<td>dstid</td>
<td>MsgInfo[15:0]</td>
<td></td>
<td>MsgSubcode[7:0]</td>
</tr>
</table>

The definitions of opcode, srcid, dstid, dp, and cp fields are the same as Register Access packets.
Table 7-8 and Table 7-9 give the encodings of the different messages without data that are send on
UCIe. Some Notes on the different message categories are listed below:

· {NOP.Crd} - These are used for E2E Credit returns. The destination must be D2D Adapter.

· {LinkMgmt.RDI .* } - These are used to coordinate RDI state transitions, the source and
destination is Physical Layer.

. {LinkMgmt.Adapter0 .* } - These are used to coordinate Adapter LSM state transitions for the
Adapter LSM corresponding to Stack 0 Protocol Layer. The source and destination is D2D Adapter.

. {LinkMgmt.Adapter1 .* } - These are used to coordinate Adapter LSM state transitions for the
Adapter LSM corresponding to Stack 1 Protocol Layer. The source and destination is D2D Adapter.

· {ParityFeature .* } - This is used to coordinate enabling of the Parity insertion feature. The source
and destination for this must be the D2D Adapter.

· $\left\{ \mathrm { E r r M s g } \right\} - \mathrm { T h i s } \mathrm { i s }$ used for error reporting and escalation from the remote Link Partner. This is
sent from the Retimer or Device die to the Host, and the destination must be the D2D Adapter.

<table>
<caption>Table 7-8. Message Encodings for Messages without Dataª (Sheet 1 of 3)</caption>
<tr>
<th>Name</th>
<th>Msgcode</th>
<th>Msgsubcode</th>
<th>MsgInfo</th>
<th>Description</th>
</tr>
<tr>
<td>$\left\{ \mathrm { N o p } . \mathrm { C r d } \right\}$</td>
<td>00h</td>
<td>00h</td>
<td>$\begin{array}{} { 0 0 0 0 h : R e s e r v e d } \\ { 0 0 0 1 h : 1 \text { Credit returr } } \end{array}$ 0002h: 2 Credit returns 0003h: 3 Credit returns 0004h: 4 Credit returns</td>
<td>Explicit Credit return from Remote Link partner for credited messages.</td>
</tr>
<tr>
<td>{LinkMgmt.RDI.Req .Active}</td>
<td rowspan="7">01h</td>
<td>01h</td>
<td rowspan="7">Reserved</td>
<td>Active Request for RDI SM.</td>
</tr>
<tr>
<td>{LinkMgmt.RDI.Req .L1}</td>
<td>04h</td>
<td>L1 Request for RDI SM.</td>
</tr>
<tr>
<td>{LinkMgmt.RDI.Req .L2}</td>
<td>$0 8 h$</td>
<td>L2 Request for RDI SM.</td>
</tr>
<tr>
<td>{LinkMgmt.RDI.Req .LinkReset}</td>
<td>$0 9 h$</td>
<td>LinkReset Request for RDI SM.</td>
</tr>
<tr>
<td>{LinkMgmt.RDI.Req .LinkError}</td>
<td>0Ah</td>
<td>LinkError Request for RDI SM.</td>
</tr>
<tr>
<td>{LinkMgmt.RDI.Req .Retrain}</td>
<td>0Bh</td>
<td>Retrain Request for RDI SM.</td>
</tr>
<tr>
<td>{LinkMgmt.RDI.Req .Disable}</td>
<td>$0 C h$</td>
<td>Disable Request for RDI SM.</td>
</tr>
</table>

<table>
<caption>Table 7-8. Message Encodings for Messages without Dataª (Sheet 2 of 3)</caption>
<tr>
<th>Name</th>
<th>Msgcode</th>
<th>Msgsubcode</th>
<th>MsgInfo</th>
<th>Description</th>
</tr>
<tr>
<td>$\begin{array}{} { \left\{ \mathrm { L i n k M g m t } . R D I . R S _ { F } \right. } \\ { . A c t i v e ^ { 2 } } \end{array}$</td>
<td rowspan="8">02h</td>
<td>01h</td>
<td rowspan="8">0000h: Regular Response FFFFh: Stall Response</td>
<td>Active Response for RDI SM.</td>
</tr>
<tr>
<td>{LinkMgmt.RDI.Rsp .PMNAK}</td>
<td>02h</td>
<td>PMNAK Response for RDI SM</td>
</tr>
<tr>
<td>{LinkMgmt.RDI.Rsp .L1}</td>
<td>04h</td>
<td>L1 Response for RDI SM.</td>
</tr>
<tr>
<td>{LinkMgmt.RDI.Rsp .L2}</td>
<td>$0 8 h$</td>
<td>L2 Response for RDI SM.</td>
</tr>
<tr>
<td>{LinkMgmt.RDI.Rsp .LinkReset}</td>
<td>09h</td>
<td>LinkReset Response for RDI SM.</td>
</tr>
<tr>
<td>{LinkMgmt.RDI.Rsp .LinkError}</td>
<td>$0 A h$</td>
<td>LinkError Response for RDI SM.</td>
</tr>
<tr>
<td>$\begin{array}{} { \left\{ \text { LinkMgmt.RDI.RSp } \right. } \\ { \left. \text { Retrain } \right\} } \end{array}$</td>
<td>$0 B h$</td>
<td>Retrain Response for RDI SM.</td>
</tr>
<tr>
<td>$\begin{array}{} { \left\{ \mathrm { L i n k M g m t } . R D I . R S F \right. } \\ { \left. . D i s a b l e \right\} } \end{array}$</td>
<td>$0 C h$</td>
<td>Disable Response for RDI SM.</td>
</tr>
<tr>
<td>{LinkMgmt.Adapter 0.Req.Active}</td>
<td rowspan="5">03h</td>
<td>$0 1 h$</td>
<td>0000h: Regular Request FFFFh: Stall</td>
<td>Active Request for Stack 0 Adapter LSM. The Stall encoding is provided for Retimers to avoid the Adapter LSM transition to Active timeout as described in Section 9.5.3.8.</td>
</tr>
<tr>
<td>$L i n k M g m t . A d a p t e r$</td>
<td>04h</td>
<td rowspan="4">Reserved</td>
<td>L1 Request for Stack 0 Adapter LSM.</td>
</tr>
<tr>
<td>$\begin{array}{} { \text { \left\{LinkMgmt.Adapter } } \\ { 0 . R e a . 1 2 3 } \end{array}$</td>
<td>$0 8 h$</td>
<td>L2 Request for Stack 0 Adapter LSM.</td>
</tr>
<tr>
<td>{LinkMgmt.Adapter 0.Req.LinkReset}</td>
<td>09h</td>
<td>LinkReset Request for Stack 0 Adapter LSM.</td>
</tr>
<tr>
<td>$\begin{array}{} { \text { \left\{LinkMgmt.Adapter } } \\ { \left. 0 . R e a . D i s a b l e \right\} } \end{array}$</td>
<td>0Ch</td>
<td>Disable Request for Stack 0 Adapter LSM.</td>
</tr>
<tr>
<td>$\left\{ \mathrm { L i n k M g m t } . \mathrm { A d a p t e r } \right.$</td>
<td rowspan="6">04h</td>
<td>01h</td>
<td rowspan="6">0000h: Regular Response FFFFh: Stall Response</td>
<td>Active Response for Stack 0 Adapter LSM.</td>
</tr>
<tr>
<td>{LinkMgmt.Adapter 0.Rsp.PMNAK}</td>
<td>02h</td>
<td>PMNAK Response for Stack 0 Adapter LSM.</td>
</tr>
<tr>
<td>$L i n k M g m t . A d a p t e r$</td>
<td>04h</td>
<td>L1 Response for Stack 0 Adapter LSM.</td>
</tr>
<tr>
<td>$\begin{array}{} { \text { LinkMgmt. Adapter } } \\ { \left. 0 . R s 0 . 1 2 \right\} } \end{array}$</td>
<td>08h</td>
<td>L2 Response for Stack 0 Adapter LSM.</td>
</tr>
<tr>
<td>$\begin{array}{} { \text { \left\{LinkMgmt. Adapter } } \\ { \left. 0 . R s p . L i n k R e s e t \right\} } \end{array}$</td>
<td>$0 9 h$</td>
<td>LinkReset Response for Stack 0 Adapter LSM.</td>
</tr>
<tr>
<td>$\begin{array}{} { \left\{ \text { LinkMgmt.Adapter } \right. } \\ { \left. \text { D.Rsp.Disable } \right\} } \end{array}$</td>
<td>0Ch</td>
<td>Disable Response for Stack 0 Adapter LSM.</td>
</tr>
<tr>
<td>$\begin{array}{} { \left\{ \text { LinkMgmt.Adapter } \right. } \\ { \left. \text { 1.Rea.Active } \right\} } \end{array}$</td>
<td rowspan="5">05h</td>
<td>01h</td>
<td>0000h: Regular Request FFFFh: Stall</td>
<td>Active Request for Stack 1 Adapter LSM. The Stall encoding is provided for Retimers to avoid the Adapter LSM transition to Active timeout as described in Section 9.5.3.8.</td>
</tr>
<tr>
<td>$L i n k M g m t . A d a p t e r$</td>
<td>$0 4 h$</td>
<td rowspan="4">Reserved</td>
<td>L1 Request for Stack 1 Adapter LSM.</td>
</tr>
<tr>
<td>$\begin{array}{} { \left\{ \text { LinkMgmt.Adapter } \right. } \\ { \left. 1 . \text { Req.L2 } \right\} } \end{array}$</td>
<td>08h</td>
<td>L2 Request for Stack 1 Adapter LSM.</td>
</tr>
<tr>
<td>$\left\{ \mathrm { L i n k M g m t } . \mathrm { A d a p t e r } \right.$</td>
<td>$0 9 h$</td>
<td>LinkReset Request for Stack 1 Adapter LSM.</td>
</tr>
<tr>
<td>$\begin{array}{} { \text { LinkMgmt.Adapter } } \\ { \left. \text { 1.Req. Disable } \right\} } \end{array}$</td>
<td>0Ch</td>
<td>Disable Request for Stack 1 Adapter LSM.</td>
</tr>
</table>

<table>
<caption>Table 7-8. Message Encodings for Messages without Dataª (Sheet 3 of 3)</caption>
<tr>
<th>Name</th>
<th>Msgcode</th>
<th>Msgsubcode</th>
<th>MsgInfo</th>
<th>Description</th>
</tr>
<tr>
<td>$\left\{ \mathrm { L i n k M g m t } . \mathrm { A d a p t e r } \right.$</td>
<td rowspan="6">$0 6 h$</td>
<td>01h</td>
<td rowspan="6">0000h: Regular Response FFFFh: Stall Response</td>
<td>Active Response for Stack 1 Adapter LSM.</td>
</tr>
<tr>
<td>$\left\{ \mathrm { L i n k M g m t } . \mathrm { A d a p t e r } \right.$</td>
<td>02h</td>
<td>PMNAK Response for Stack 1 Adapter LSM</td>
</tr>
<tr>
<td>$\begin{array}{} { \left\{ \text { LinkMgmt.Adapter } \right. } \\ { \left. 1 . R s p . L 1 \right\} } \end{array}$</td>
<td>04h</td>
<td>L1 Response for Stack 1 Adapter LSM.</td>
</tr>
<tr>
<td>$\begin{array}{} { \left\{ \text { LinkMgmt. Adapter } \right. } \\ { \left. 1 . R s p . L 2 \right\} } \end{array}$</td>
<td>$0 8 h$</td>
<td>L2 Response for Stack 1 Adapter LSM.</td>
</tr>
<tr>
<td>$L i n k M g m t . A d a p t e r$</td>
<td>09h</td>
<td>LinkReset Response for Stack 1 Adapter LSM.</td>
</tr>
<tr>
<td>$\left\{ \mathrm { L i n k M g m t } . \mathrm { A d a p t e r } \right.$</td>
<td>0Ch</td>
<td>Disable Response for Stack 1 Adapter LSM.</td>
</tr>
<tr>
<td>{ParityFeature.Req}</td>
<td>07h</td>
<td>00h</td>
<td>Reserved</td>
<td>Parity Feature enable request.</td>
</tr>
<tr>
<td>$P a r i t y F e a t u r e . A c k$</td>
<td rowspan="2">$0 8 h$</td>
<td>00h</td>
<td rowspan="2">0000h: Regular Response FFFFh: Stall Response</td>
<td>Parity Feature enable Ack.</td>
</tr>
<tr>
<td>{ParityFeature.Nak}</td>
<td>01h</td>
<td>Parity Feature enable Nak.</td>
</tr>
<tr>
<td rowspan="3">$E r r M s g$</td>
<td rowspan="3">09h</td>
<td>00h</td>
<td rowspan="3">Reserved</td>
<td>Correctable Error Message.</td>
</tr>
<tr>
<td>01h</td>
<td>Non-Fatal Error Message.</td>
</tr>
<tr>
<td>$0 2 h$</td>
<td>Fatal Error Message.</td>
</tr>
<tr>
<td>{Vendor Defined Message}</td>
<td>$F F h$</td>
<td>--</td>
<td>Vendor ID</td>
<td>Vendor Defined Messages. These can be exchanged at any time after sideband is functional post SBINIT. Interoperability is vendor defined. Unsupported vendor defined messages must be discarded by the receiver. Note that this is NOT the UCIe Vendor ID, but rather the unique identifier of the chiplet vendor that is defining and using these messages.</td>
</tr>
</table>

a. All other encodings not mentioned in this table are reserved.

<table>
<caption>Table 7-9. Link Training State Machine related Message encodings for messages without data (Sheet 1 of 5)</caption>
<tr>
<th>Message</th>
<th>MsgInfo[15:0]</th>
<th>MsgCode[7:0]</th>
<th>MsgSubcode[7:0]</th>
</tr>
<tr>
<td>{Start Tx Init D to C point test resp}</td>
<td>0000h</td>
<td>8Ah</td>
<td>01h</td>
</tr>
<tr>
<td>{LFSR_clear_error req}</td>
<td>0000h</td>
<td>85h</td>
<td>02h</td>
</tr>
<tr>
<td></td>
<td>0000h</td>
<td>8Ah</td>
<td>02h</td>
</tr>
<tr>
<td>$\left\{ T \times \text { Init } D \text { to C results req } \right\}$</td>
<td>0000h</td>
<td>85h</td>
<td>03h</td>
</tr>
<tr>
<td>$\frac { \left\{ \text { End Tx Init } D \text { to C point test req } \right\} } { \left\{ \text { End } T \times \text { Init } D \text { to C point test } r e s p \right\} }$</td>
<td>0000h</td>
<td>85h</td>
<td>04h</td>
</tr>
<tr>
<td></td>
<td>0000h</td>
<td>8Ah</td>
<td>04h</td>
</tr>
<tr>
<td>{Start Tx Init D to C eye sweep resp}</td>
<td>0000h</td>
<td>8Ah</td>
<td>05h</td>
</tr>
<tr>
<td>{End Tx Init D to C eye sweep req}</td>
<td>0000h</td>
<td>85h</td>
<td>06h</td>
</tr>
<tr>
<td>$T \times \text { Init } D$ to C eye sweep resp}</td>
<td>0000h</td>
<td>8Ah</td>
<td>06h</td>
</tr>
<tr>
<td>{Start Rx Init D to C point test resp}</td>
<td>0000h</td>
<td>8Ah</td>
<td>07h</td>
</tr>
<tr>
<td>$\left\{ R \times \text { Init } D \text { to C } T x \text { Count Done } r e q \right\}$</td>
<td>0000h</td>
<td>85h</td>
<td>08h</td>
</tr>
<tr>
<td>$R x \quad I n i t \quad D \quad t o \quad C \quad T x \quad C o u n t \quad D o n e \quad r e s p$</td>
<td>0000h</td>
<td>8Ah</td>
<td>08h</td>
</tr>
<tr>
<td>$E n d \quad R x \quad I n i t \quad D \quad t o \quad C \quad p o i n t \quad t e s t \quad r e q$</td>
<td>0000h</td>
<td>85h</td>
<td>09h</td>
</tr>
<tr>
<td>{End Rx Init D to C point test resp}</td>
<td>0000h</td>
<td>8Ah</td>
<td>09h</td>
</tr>
<tr>
<td>{Start Rx Init D to C eye sweep resp}</td>
<td>0000h</td>
<td>8Ah</td>
<td>0Ah</td>
</tr>
<tr>
<td>{Rx Init D to C results req}</td>
<td>0000h</td>
<td>85h</td>
<td>0Bh</td>
</tr>
<tr>
<td>$E n d \quad R x \quad I n i t \quad D \quad t o \quad C \quad e y e \quad s w e e p \quad r e q$</td>
<td>0000h</td>
<td>85h</td>
<td>0Dh</td>
</tr>
<tr>
<td>{End Rx Init D to C eye sweep resp}</td>
<td>0000h</td>
<td>8Ah</td>
<td>0Dh</td>
</tr>
<tr>
<td>$S B I N I T \quad o u t \quad o f \quad R e s e t$</td>
<td>$\left[ 3 : 0 \right] : R e s u l t$</td>
<td>$9 1 h$</td>
<td>00h</td>
</tr>
<tr>
<td>$S B I N I T \quad d o n e \quad r e q$</td>
<td>0000h</td>
<td>95h</td>
<td>01h</td>
</tr>
<tr>
<td>{SBINIT done resp}</td>
<td>0000h</td>
<td>9Ah</td>
<td>01h</td>
</tr>
<tr>
<td>$\left\{ \mathrm { M B I N I T } . \mathrm { C A L D o n e } \mathrm { r e q } \right\}$</td>
<td>0000h</td>
<td>A5h</td>
<td>02h</td>
</tr>
<tr>
<td>{MBINIT.CAL Done resp}</td>
<td>0000h</td>
<td>AAh</td>
<td>02h</td>
</tr>
<tr>
<td>{MBINIT.REPAIRCLK init req}</td>
<td>0000h</td>
<td>A5h</td>
<td>03h</td>
</tr>
<tr>
<td>{MBINIT.REPAIRCLK init resp}</td>
<td>0000h</td>
<td>AAh</td>
<td>03h</td>
</tr>
<tr>
<td>{MBINIT.REPAIRCLK result req}</td>
<td>0000h</td>
<td>A5h</td>
<td>04h</td>
</tr>
<tr>
<td>{MBINIT.REPAIRCLK result resp}</td>
<td>[15:4]: Reserved $\left[ 3 \right] : C o m p a r e \quad R e s u l t s \quad f r o m$ L _ $\left[ 2 \right] : C o m p a r e \quad R e s u l t s \quad f r o m$ L _ $\left[ 1 \right] : C o m p a r e \quad R e s u l t s \quad f r o m$ L _ $\left[ 0 \right] : C o m p a r e \quad R e s u l t s \quad f r o m$ L _</td>
<td>$A A h$</td>
<td>04h</td>
</tr>
<tr>
<td>{MBINIT.REPAIRCLK apply repair req}</td>
<td>[15:4]: Reserved [3:0]: Repair Encoding • · $\begin{array}{} \text { Fh: Reserved } \\ \text { Oh: Repair RCKP } \end{array}$ _ · 1h: Repair RCKN L · 2h: Repair RTRK L _ · 7h: Reserved</td>
<td>A5h</td>
<td>05h</td>
</tr>
<tr>
<td>{MBINIT.REPAIRCLK apply repair resp}</td>
<td>0000h</td>
<td>AAh</td>
<td>05h</td>
</tr>
</table>

<table>
<caption>Table 7-9. Link Training State Machine related Message encodings for messages without data (Sheet 2 of 5)</caption>
<tr>
<th>Message</th>
<th>$M s g I n f o \left[ 1 5 : 0 \right]$</th>
<th>$\mathrm { M s g C o d e \left[ 7 : 0 \right] }$</th>
<th>$\mathrm { M s g S u b c o d e } \left[ 7 : 0 \right]$</th>
</tr>
<tr>
<td>{MBINIT.REPAIRCLK check repair init req}</td>
<td>0000h</td>
<td>$A 5 h$</td>
<td>06h</td>
</tr>
<tr>
<td>{MBINIT.REPAIRCLK check repair init resp}</td>
<td>0000h</td>
<td>AAh</td>
<td>06h</td>
</tr>
<tr>
<td>{MBINIT.REPAIRCLK check results req}</td>
<td>0000h</td>
<td>A5h</td>
<td>07h</td>
</tr>
<tr>
<td>{MBINIT.REPAIRCLK check results resp}</td>
<td>[15:4]: $\begin{array}{} { \left[ 3 \right] : \text { Compare Results from } } \\ { \text { RRDCK I } } \end{array}$ L _ $\begin{array}{} { \left[ 2 \right] : \text { Compare Results from } } \\ { \text { RTRK } I } \end{array}$ L _ $\left[ 1 \right] : C o m p a r e \quad R e s u l t s \quad f r o m$ RCKN_L $\begin{array}{} { \text { \left[0\right]: Compare Results from } } \\ { \text { RCKP L } } \end{array}$ L _</td>
<td>AAh</td>
<td>07h</td>
</tr>
<tr>
<td>{MBINIT.REPAIRCLK done req}</td>
<td>0000h</td>
<td>A5h</td>
<td>$0 8 h$</td>
</tr>
<tr>
<td>{MBINIT.REPAIRCLK done resp}</td>
<td>0000h</td>
<td>AAh</td>
<td>$0 8 h$</td>
</tr>
<tr>
<td>{MBINIT.REPAIRVAL init req}</td>
<td>0000h</td>
<td>A5h</td>
<td>09h</td>
</tr>
<tr>
<td>{MBINIT.REPAIRVAL init resp}</td>
<td>0000h</td>
<td>$A A h$</td>
<td>09h</td>
</tr>
<tr>
<td>{MBINIT.REPAIRVAL result req}</td>
<td>0000h</td>
<td>A5h</td>
<td>0Ah</td>
</tr>
<tr>
<td>{MBINIT.REPAIRVAL result resp}</td>
<td>[15:2]: Reserved $\begin{array}{} { \left[ 1 \right] : \text { Compare Results from } } \\ { \text { RRDVLD } } \end{array}$ L _ $\begin{array}{} { \text { \left[0\right]: Compare Results from } } \\ { \text { RVLD I } } \end{array}$ L _</td>
<td>AAh</td>
<td>$0 A h$</td>
</tr>
<tr>
<td>{MBINIT.REPAIRVAL apply repair req}</td>
<td>$\left[ 1 5 : 2 \right] : R e s e r v e d$ [1:0]: · 3h: Reserved · Oh: Repair RVLD_L · 1h: Reserved</td>
<td>A5h</td>
<td>$0 B h$</td>
</tr>
<tr>
<td>{MBINIT.REPAIRVAL apply repair resp}</td>
<td>0000h</td>
<td>$A A h$</td>
<td>$0 B h$</td>
</tr>
<tr>
<td>{MBINIT.REPAIRVAL done req}</td>
<td>0000h</td>
<td>A5h</td>
<td>$0 C h$</td>
</tr>
<tr>
<td>{MBINIT.REPAIRVAL done resp}</td>
<td>0000h</td>
<td>AAh</td>
<td>0Ch</td>
</tr>
<tr>
<td>{MBINIT.REVERSALMB init req}</td>
<td>0000h</td>
<td>A5h</td>
<td>0Dh</td>
</tr>
<tr>
<td>{MBINIT.REVERSALMB init resp}</td>
<td>0000h</td>
<td>AAh</td>
<td>0Dh</td>
</tr>
<tr>
<td>{MBINIT.REVERSALMB clear error req}</td>
<td>0000h</td>
<td>A5h</td>
<td>0Eh</td>
</tr>
<tr>
<td>{MBINIT.REVERSALMB clear error resp}</td>
<td>0000h</td>
<td>AAh</td>
<td>0Eh</td>
</tr>
<tr>
<td>{MBINIT.REVERSALMB result req}</td>
<td>0000h</td>
<td>A5h</td>
<td>0Fh</td>
</tr>
<tr>
<td>{MBINIT.REVERSALMB done req}</td>
<td>0000h</td>
<td>A5h</td>
<td>10h</td>
</tr>
<tr>
<td>{MBINIT.REVERSALMB done resp}</td>
<td>0000h</td>
<td>AAh</td>
<td>10h</td>
</tr>
<tr>
<td>{MBINIT.REPAIRMB start req}</td>
<td>0000h</td>
<td>A5h</td>
<td>11h</td>
</tr>
<tr>
<td>{MBINIT.REPAIRMB start resp}</td>
<td>0000h</td>
<td>AAh</td>
<td>11h</td>
</tr>
<tr>
<td>{MBINIT.REPAIRMB Apply repair resp}</td>
<td>0000h</td>
<td>AAh</td>
<td>12h</td>
</tr>
<tr>
<td>$\left\{ \mathrm { M B I N I T } . \mathrm { R E P A I R M B } \mathrm { e n d } \mathrm { r e q } \right\}$</td>
<td>0000h</td>
<td>A5h</td>
<td>13h</td>
</tr>
<tr>
<td>{MBINIT.REPAIRMB end resp}</td>
<td>0000h</td>
<td>AAh</td>
<td>13h</td>
</tr>
<tr>
<td>{MBINIT.REPAIRMB apply degrade req}</td>
<td>$\left[ 1 5 : 3 \right] : R e s e r v e d$ $\left[ 2 : 0 \right] :$ Standard package logical</td>
<td>A5h</td>
<td>14h</td>
</tr>
<tr>
<td>{MBINIT.REPAIRMB apply degrade resp}</td>
<td>0000h</td>
<td>AAh</td>
<td>14h</td>
</tr>
</table>

<table>
<caption>Table 7-9. Link Training State Machine related Message encodings for messages without data (Sheet 3 of 5)</caption>
<tr>
<th>$\mathrm { M e s s a g } 6$</th>
<th>$M s g I n f o \left[ 1 5 : 0 \right]$</th>
<th>$M s g C o d e \left[ 7 : 0 \right]$</th>
<th>MsgSubcode[7:0]</th>
</tr>
<tr>
<td>{MBTRAIN.VALVREF start req}</td>
<td>$0 0 0 0 h$</td>
<td>$B 5 h$</td>
<td>00h</td>
</tr>
<tr>
<td>{MBTRAIN.VALVREF start resp}</td>
<td>0000h</td>
<td>BAh</td>
<td>00h</td>
</tr>
<tr>
<td>$\left\{ \mathrm { M B T R A I N } . \mathrm { V A L V R E E F } \text { end req } \right\}$</td>
<td>0000h</td>
<td>B5h</td>
<td>01h</td>
</tr>
<tr>
<td>$\left\{ \mathrm { M B T R A I N } . \mathrm { V A L V R E F } \text { end resp } \right\}$</td>
<td>0000h</td>
<td>BAh</td>
<td>01h</td>
</tr>
<tr>
<td>$\left\{ \mathrm { M B T R A I N } . \mathrm { D A T A V R E F } \text { start req } \right\}$</td>
<td>0000h</td>
<td>B5h</td>
<td>02h</td>
</tr>
<tr>
<td>{MBTRAIN.DATAVREF start resp}</td>
<td>0000h</td>
<td>BAh</td>
<td>02h</td>
</tr>
<tr>
<td>{MBTRAIN.DATAVREF end req}</td>
<td>0000h</td>
<td>B5h</td>
<td>03h</td>
</tr>
<tr>
<td>$\left\{ \mathrm { M B T R A I N } . \mathrm { D A T A V R F F } \text { end resp } \right\}$</td>
<td>0000h</td>
<td>BAh</td>
<td>03h</td>
</tr>
<tr>
<td>$\left\{ \mathrm { M B T R A I N } . \mathrm { S P E E D I D L E } \mathrm { d o n e } \mathrm { r e q } \right\}$</td>
<td>0000h</td>
<td>B5h</td>
<td>04h</td>
</tr>
<tr>
<td>{MBTRAIN.SPEEDIDLE done resp}</td>
<td>0000h</td>
<td>BAh</td>
<td>04h</td>
</tr>
<tr>
<td>{MBTRAIN.TXSELFCAL Done req}</td>
<td>0000h</td>
<td>B5h</td>
<td>05h</td>
</tr>
<tr>
<td>{MBTRAIN.TXSELFCAL Done resp}</td>
<td>0000h</td>
<td>BAh</td>
<td>05h</td>
</tr>
<tr>
<td>{MBTRAIN.RXCLKCAL start req}</td>
<td>0000h</td>
<td>B5h</td>
<td>06h</td>
</tr>
<tr>
<td>$\left\{ \mathrm { M B T R A I N } . \mathrm { R X C L K C A L } \mathrm { s t a r t } \mathrm { r e s p } \right\}$</td>
<td>0000h</td>
<td>BAh</td>
<td>06h</td>
</tr>
<tr>
<td>{MBTRAIN.RXCLKCAL $\left. \mathrm { d o n e } \mathrm { r e q } \right\}$</td>
<td>0000h</td>
<td>B5h</td>
<td>07h</td>
</tr>
<tr>
<td>{MBTRAIN.RXCLKCAL done resp}</td>
<td>0000h</td>
<td>BAh</td>
<td>07h</td>
</tr>
<tr>
<td>{MBTRAIN.VALTRAINCENTER start req}</td>
<td>0000h</td>
<td>B5h</td>
<td>08h</td>
</tr>
<tr>
<td>{MBTRAIN.VALTRAINCENTER start resp}</td>
<td>0000h</td>
<td>BAh</td>
<td>08h</td>
</tr>
<tr>
<td>{MBTRAIN.VALTRAINCENTER done req}</td>
<td>0000h</td>
<td>B5h</td>
<td>09h</td>
</tr>
<tr>
<td>{MBTRAIN.VALTRAINCENTER $\left. \mathrm { d o n e } \mathrm { r e s p } \right\}$</td>
<td>0000h</td>
<td>BAh</td>
<td>09h</td>
</tr>
<tr>
<td>{MBTRAIN.VALTRAINVREF start req}</td>
<td>0000h</td>
<td>B5h</td>
<td>0Ah</td>
</tr>
<tr>
<td>{MBTRAIN.VALTRAINVREF start resp}</td>
<td>0000h</td>
<td>BAh</td>
<td>0Ah</td>
</tr>
<tr>
<td>{MBTRAIN.VALTRAINVREF $d o n e \quad r e q$</td>
<td>0000h</td>
<td>B5h</td>
<td>0Bh</td>
</tr>
<tr>
<td>{MBTRAIN.VALTRAINVREF $d o n e \quad r e s p$</td>
<td>0000h</td>
<td>BAh</td>
<td>0Bh</td>
</tr>
<tr>
<td>{MBTRAIN.DATATRAINCENTER1 start req}</td>
<td>0000h</td>
<td>B5h</td>
<td>0Ch</td>
</tr>
<tr>
<td>{MBTRAIN.DATATRAINCENTER1 start resp}</td>
<td>0000h</td>
<td>BAh</td>
<td>0Ch</td>
</tr>
<tr>
<td>{MBTRAIN.DATATRAINCENTER1 end req}</td>
<td>0000h</td>
<td>B5h</td>
<td>0Dh</td>
</tr>
<tr>
<td>{MBTRAIN.DATATRAINCENTER1 end resp}</td>
<td>0000h</td>
<td>BAh</td>
<td>0Dh</td>
</tr>
<tr>
<td>{MBTRAIN.DATATRAINVREF start req}</td>
<td>0000h</td>
<td>B5h</td>
<td>0Eh</td>
</tr>
<tr>
<td>{MBTRAIN.DATATRAINVREF start resp}</td>
<td>0000h</td>
<td>BAh</td>
<td>0Eh</td>
</tr>
<tr>
<td>{MBTRAIN.DATATRAINVREF end req}</td>
<td>0000h</td>
<td>B5h</td>
<td>10h</td>
</tr>
<tr>
<td>{MBTRAIN.DATATRAINVREF end resp}</td>
<td>0000h</td>
<td>BAh</td>
<td>10h</td>
</tr>
<tr>
<td>{MBTRAIN.RXDESKEW start req}</td>
<td>0000h</td>
<td>B5h</td>
<td>11h</td>
</tr>
<tr>
<td>{MBTRAIN.RXDESKEW start resp}</td>
<td>0000h</td>
<td>BAh</td>
<td>11h</td>
</tr>
<tr>
<td>{MBTRAIN.RXDESKEW end req}</td>
<td>0000h</td>
<td>B5h</td>
<td>12h</td>
</tr>
<tr>
<td>$\left\{ \mathrm { M B T R I I N } . \mathrm { R X D E S K E W } \mathrm { e n d } \mathrm { r e s p } \right\}$</td>
<td>0000h</td>
<td>BAh</td>
<td>12h</td>
</tr>
<tr>
<td>{MBTRAIN.DATATRAINCENTER2 start req}</td>
<td>0000h</td>
<td>B5h</td>
<td>13h</td>
</tr>
<tr>
<td>{MBTRAIN.DATATRAINCENTER2 start resp}</td>
<td>0000h</td>
<td>BAh</td>
<td>13h</td>
</tr>
<tr>
<td>{MBTRAIN.DATATRAINCENTER2 end req}</td>
<td>0000h</td>
<td>B5h</td>
<td>14h</td>
</tr>
<tr>
<td>{MBTRAIN.DATATRAINCENTER2 end resp}</td>
<td>0000h</td>
<td>BAh</td>
<td>14h</td>
</tr>
</table>

<table>
<caption>Table 7-9. Link Training State Machine related Message encodings for messages without data (Sheet 4 of 5)</caption>
<tr>
<th>Message</th>
<th>$M s g I n f o \left[ 1 5 : 0 \right]$</th>
<th>$M s g C o d e \left[ 7 : 0 \right]$</th>
<th>MsgSubcode [7:0]</th>
</tr>
<tr>
<td>{MBTRAIN.LINKSPEED start req}</td>
<td>$0 0 0 0 h$</td>
<td>B5h</td>
<td>15h</td>
</tr>
<tr>
<td>{MBTRAIN.LINKSPEED start resp}</td>
<td>0000h</td>
<td>BAh</td>
<td>15h</td>
</tr>
<tr>
<td>$\left\{ \mathrm { M B T R A I N } . \mathrm { L I N K S P E E D } \mathrm { e r r o r } \mathrm { r e q } \right\}$</td>
<td>0000h</td>
<td>B5h</td>
<td>16h</td>
</tr>
<tr>
<td>{MBTRAIN.LINKSPEED error resp}</td>
<td>0000h</td>
<td>BAh</td>
<td>16h</td>
</tr>
<tr>
<td>{MBTRAIN.LINKSPEED exit to repair req}</td>
<td>0000h</td>
<td>B5h</td>
<td>17h</td>
</tr>
<tr>
<td>{MBTRAIN.LINKSPEED exit to repair resp}</td>
<td>0000h</td>
<td>BAh</td>
<td>17h</td>
</tr>
<tr>
<td>{MBTRAIN.LINKSPEED exit to speed degrade req}</td>
<td>0000h</td>
<td>B5h</td>
<td>18h</td>
</tr>
<tr>
<td>{MBTRAIN.LINKSPEED exit to speed degrade resp}</td>
<td>0000h</td>
<td>BAh</td>
<td>18h</td>
</tr>
<tr>
<td>{MBTRAIN.LINKSPEED done req}</td>
<td>0000h: For regular response</td>
<td>B5h</td>
<td>19h</td>
</tr>
<tr>
<td>{MBTRAIN.LINKSPEED done resp}</td>
<td>0000h: For regular response FFFFh: For stall</td>
<td>BAh</td>
<td>19h</td>
</tr>
<tr>
<td>{MBTRAIN.LINKSPEED multi-module disable module resp}</td>
<td>0000h</td>
<td>BAh</td>
<td>1Ah</td>
</tr>
<tr>
<td>{MBTRAIN.LINKSPEED exit to phy retrain req}</td>
<td>0000h</td>
<td>B5h</td>
<td>1Fh</td>
</tr>
<tr>
<td>{MBTRAIN.LINKSPEED exit to phy retrain resp}</td>
<td>0000h</td>
<td>BAh</td>
<td>$1 F h$</td>
</tr>
<tr>
<td>{MBTRAIN.REPAIR init req}</td>
<td>0000h</td>
<td>B5h</td>
<td>1Bh</td>
</tr>
<tr>
<td>{MBTRAIN.REPAIR init resp}</td>
<td>0000h</td>
<td>BAh</td>
<td>1Bh</td>
</tr>
<tr>
<td>{MBTRAIN.REPAIR Apply repair resp}</td>
<td>0000h</td>
<td>BAh</td>
<td>1Ch</td>
</tr>
<tr>
<td>{MBTRAIN.REPAIR end req}</td>
<td>0000h</td>
<td>B5h</td>
<td>1Dh</td>
</tr>
<tr>
<td>{MBTRAIN.REPAIR end resp}</td>
<td>0000h</td>
<td>BAh</td>
<td>1Dh</td>
</tr>
<tr>
<td>$\left\{ \mathrm { M B T R A I N } . \mathrm { R E P A I R } \mathrm { A p p l y } \mathrm { d e g r a d e } \mathrm { r e q } \right\}$</td>
<td>[15:3]: Reserved [2:0]: Standard Package logical Lane mapb</td>
<td>B5h</td>
<td>1Eh</td>
</tr>
<tr>
<td>{MBTRAIN.REPAIR Apply degrade resp}</td>
<td>0000h</td>
<td>BAh</td>
<td>$1 E h$</td>
</tr>
<tr>
<td>{MBTRAIN.RXDESKEW EQ Preset req}</td>
<td>$\left[ 1 5 : 4 \right] : R e s e r v e d$</td>
<td>B5h</td>
<td>1Fh</td>
</tr>
<tr>
<td>{MBTRAIN.RXDESKEW EQ Preset resp}</td>
<td>[15:1]: Reserved [0]: Status · 0: Success · 1: Fail</td>
<td>BAh</td>
<td>1Fh</td>
</tr>
<tr>
<td>{MBTRAIN.RXDESKEW exit to DATATRAINCENTER1 req}</td>
<td>0000h</td>
<td>B5h</td>
<td>$2 0 h$</td>
</tr>
<tr>
<td>{MBTRAIN.RXDESKEW exit to DATATRAINCENTER1 $\left. \mathrm { r e s p } \right\}$</td>
<td>0000h</td>
<td>BAh</td>
<td>20h</td>
</tr>
</table>

<table>
<caption>Table 7-9. Link Training State Machine related Message encodings for messages without data (Sheet 5 of 5)</caption>
<tr>
<th>Message</th>
<th>MsgInfo[15:0]</th>
<th>$M s g C o d e \left[ 7 : 0 \right]$</th>
<th>MsgSubcode [7:0]</th>
</tr>
<tr>
<td>{MBTRAIN.RXCLKCAL TCKN_L shift req}</td>
<td>[15:6]: Reserved $\left[ 5 : 1 \right] : S h i f t \quad V a l u e . I n d i c a t e s \quad t h e$ of 1/64 UI [0]: Decrement · 0: Increment · 1: Decrement</td>
<td>B5h</td>
<td>21h</td>
</tr>
<tr>
<td>{MBTRAIN.RXCLKCAL TCKN_L shift resp}</td>
<td>[15:1]: Reserved [0]: Status · 0: Shift was successfully applied · 1: Shift was not applied (most likely scenario is that it is Out of Range)</td>
<td>$B A h$</td>
<td>$2 1 h$</td>
</tr>
<tr>
<td>{PHYRETRAIN.retrain start req}</td>
<td>$\begin{array}{} { \left[ 1 5 : 3 \right] : \text { Reserved } } \\ { \left[ 2 : 0 \right] : \text { Retrain Encoding } } \end{array}$</td>
<td>C5h</td>
<td>01h</td>
</tr>
<tr>
<td>{PHYRETRAIN.retrain start resp}</td>
<td>$\left[ 1 5 : 3 \right] : R e s e r v e d$ [2:0]:</td>
<td>CAh</td>
<td>01h</td>
</tr>
<tr>
<td>{TRAINERROR Entry req}</td>
<td>0000h</td>
<td>$E 5 h$</td>
<td>00h</td>
</tr>
<tr>
<td>{TRAINERROR Entry resp}</td>
<td>0000h</td>
<td>EAh</td>
<td>00h</td>
</tr>
<tr>
<td>{RECAL.track pattern init req}</td>
<td>0000h</td>
<td>D5h</td>
<td>00h</td>
</tr>
<tr>
<td>{RECAL.track pattern init resp}</td>
<td>0000h</td>
<td>DAh</td>
<td>00h</td>
</tr>
<tr>
<td>{RECAL.track pattern done req}</td>
<td>0000h</td>
<td>D5h</td>
<td>01h</td>
</tr>
<tr>
<td>{RECAL.track pattern done resp}</td>
<td>0000h</td>
<td>DAh</td>
<td>01h</td>
</tr>
<tr>
<td>{RECAL.track tx adjust req}</td>
<td>[15:9]: Reserved [8]: · 0: Increment clock delay or decrement data delay · 1: Decrement clock delay or increment data delay [7:0]: Delay compensation value, in units of 1/64 UI</td>
<td>$B 5 h$</td>
<td>$2 2 h$</td>
</tr>
<tr>
<td>{RECAL.track tx adjust resp}</td>
<td>[15:2]: Reserved [1:0]: Status · 00b: Reserved · 01b: Drift compensated · 10b: Drift not compensated . 11b: Stall</td>
<td>BAh</td>
<td>22h</td>
</tr>
</table>

a. See Section 4.5.3.2.

b. See Table 4-9.

### 7.1.2.3 Messages with data payloads

Figure 7-4 shows the formats for Messages with data payloads. The definitions of opcode, srcid, dstid,
dp, and cp fields are the same as Register Access packets.

<table>
<caption>Figure 7-4. Format for Messages with data payloads</caption>
<tr>
<th colspan="18">Messages with data</th>
</tr>
<tr>
<th>Bytes</th>
<th colspan="4">3</th>
<th colspan="5">2</th>
<th colspan="3">1</th>
<th colspan="5">0</th>
</tr>
<tr>
<td>Bits</td>
<td colspan="3">31 30 29 28 27</td>
<td>26 25 24</td>
<td>23</td>
<td colspan="2">22 21 20</td>
<td>19 18</td>
<td>17 16</td>
<td>15 14</td>
<td>13 12 11 10</td>
<td>9 8</td>
<td>7</td>
<td>6 5</td>
<td>4 3</td>
<td></td>
<td>210</td>
</tr>
<tr>
<td>Header / Data</td>
<td colspan="4"></td>
<td colspan="13">Header</td>
</tr>
<tr>
<td>Phase0</td>
<td colspan="2">srcid</td>
<td>rsvd</td>
<td colspan="3">rsvd</td>
<td colspan="4">msgcode [7:0]</td>
<td colspan="2">rsvd</td>
<td colspan="2"></td>
<td colspan="3">opcode [4:0]</td>
</tr>
<tr>
<td>Phase1</td>
<td>dp cp</td>
<td></td>
<td>rsvd</td>
<td>dstid</td>
<td colspan="2"></td>
<td></td>
<td colspan="3">MsgInfo[15:0]</td>
<td colspan="2"></td>
<td colspan="5">MsgSubcode [7:0]</td>
</tr>
<tr>
<td>Header / Data</td>
<td colspan="4"></td>
<td colspan="8">Data</td>
<td colspan="5"></td>
</tr>
<tr>
<td>Phase2</td>
<td colspan="17">data[31:0]</td>
</tr>
<tr>
<td>Phase3</td>
<td></td>
<td colspan="2"></td>
<td></td>
<td colspan="2"></td>
<td colspan="2"></td>
<td colspan="2">data[63:32]</td>
<td colspan="2"></td>
<td colspan="5"></td>
</tr>
</table>

<table>
<caption>Table 7-10 and Table 7-11 give the message encodings. Table 7-10. Message encodings for Messages with Dataª (Sheet 1 of 3)</caption>
<tr>
<th>Name</th>
<th>Msg code</th>
<th>Msgsubcode</th>
<th>MsgInfo</th>
<th>Data Bit Encodings</th>
<th>Description</th>
</tr>
<tr>
<td>{AdvCap.Adapter}</td>
<td>01h</td>
<td>00h</td>
<td>$0 0 0 0 h : R e g u l a r$ Message FFFFh: Stall Message</td>
<td>$\left[ 0 \right] : \text { {waw Format } }$ $\left[ 2 \right] : ^ { \prime \prime } C X L 2 5 6 B$ [3]: "PCIe Flit Mode"</td>
<td>Advertised Capabilities of the D2D Adapter</td>
</tr>
<tr>
<td rowspan="2">{FinCap.Adapter}</td>
<td rowspan="2">$0 2 h$</td>
<td rowspan="2">00h</td>
<td></td>
<td rowspan="2">[4]: "Streaming" [5]: "Retry" [6]: "Multi_Protocol_Enable" [7]: "Stack0_Enable" $\left[ 8 \right] : \text { Stack1 } \text { Enable } ^ { \prime \prime }$ $\left[ 1 0 \right] : C X L \_ L a t O p t \_ F m t 6$ [11]: "Retimer" [20:12]: "Retimer Credits" [21]: "DP" $\left[ 2 3 \right] : 6 8 B \quad F l i t \quad F o r m a t$ $\left[ 2 4 \right] : S t a n d a r d \quad 2 5 6 B \quad E n d \quad H e a d e r \quad F l i t$ $\left[ 2 5 \right] : \text { {Standard } 2 5 6 B \text { Start Header Flit } }$ $\begin{array}{} { \left[ 2 6 \right] : \text { uatency-Optimized } 2 5 6 B \text { without } } \\ { \text { Optional Bytes Flit Format^{\prime\prime } } } \end{array}$ $\begin{array}{} { \left[ 2 7 \right] : \text { uatency-Optimized } 2 5 6 B \text { with } } \\ { \text { Optional Bytes Flit Format^{\prime\prime } } } \end{array}$ $\begin{array}{} { \text { L28\right]: Enhanced_Multi_ Protocol_Enable^{\prime\prime } } } \\ { \left[ 2 9 \right] : \text { Stack } 0 M a x i m u m } \\ { \text { Banduridth limitr } } \end{array}$ [30]: "Stack 1 Maximum Bandwidth_Limit" $\left[ 3 1 \right] : \text { whanagement Transport Protocol } ^ { \prime \prime }$</td>
<td rowspan="2">$\begin{array}{} { \text { Finalized } } \\ { \text { Capability of the } } \end{array}$</td>
</tr>
<tr>
<td>0000h: Regular Message FFFFh: Stall Message</td>
</tr>
</table>

<table>
<caption>Table 7-10. Message encodings for Messages with Dataª (Sheet 2 of 3)</caption>
<tr>
<th>Name</th>
<th>Msg code</th>
<th>Msgsubcode</th>
<th>MsgInfo</th>
<th>Data Bit Encodings</th>
<th>Description</th>
</tr>
<tr>
<td>$\left\{ \mathrm { A d v C a p } . \mathrm { C X L } \right\}$</td>
<td>01h</td>
<td>01h</td>
<td>$0 0 0 0 h : P o s t$ $\begin{array}{} { \text { negotiation, if } } \\ { \text { Fnhanced Mult } } \end{array}$ $i s \quad O b , o r \quad i t \quad i s \quad 1 b$ and the message is for Stack 0. $0 0 0 1 h : P o s t$ negotiation, if Enhanced_Multi $\begin{array}{} \text { Protocol } \text { Enabl } \\ \text { is 1b and the } \end{array}$ $\begin{array}{} { \text { message is fo } } \\ { \text { Stack } 1 } \end{array}$ $\begin{array}{} { \text { FFFh: Stall } } \\ { \text { Messaae } } \end{array}$</td>
<td>[23:0]: Flexbus Mode negotiation usage bits as defined for Symbols 12-14 of Modified TS1/TS2 Ordered Set in CXL Specification, with the following additional rules: · $\begin{array}{} { \text { \left[0\right]: PCIe capable/enable- this mus } } \\ { \text { be 1b for PCIe Non-Flit Mode. } } \end{array}$ • $\begin{array}{} \text { \left[1\right]: CXL.i0 capable/enable-this } \\ \text { must be 0b for PCIe Non-Flit Mode. } \end{array} .$ · $\begin{array}{} { \left[ 2 \right] : \text { CXL.mem capable/enable- this } } \\ { \text { must be 0b for PCIe Non-Flit Mode. } } \end{array}$ · $\begin{array}{} { \left[ 3 \right] : \text { CXL.cache capable/enable- this } } \\ { \text { must be 0b for PCIe Non-Flit Mode. } } \end{array}$ · $\left[ 4 \right] : C X L \quad 6 8 B \quad F l i t \quad a n d \quad V H \quad c a p a b l e ;$</td>
<td>Advertised Capabilities for CXL protocol.</td>
</tr>
<tr>
<td>$F i n C a p . C X L$</td>
<td>02h</td>
<td>01h</td>
<td>$0 0 0 0 h : P o s t$ negotiation, if Enhanced_Multi Protocol_Enable is 0b, or it is 1b and the message is for Stack 0. $\begin{array}{} { 0 0 0 1 h : \text { Post } } \\ { \text { negotiation, if } } \end{array}$ Enhanced_Multi $\begin{array}{} { \text { Protocol Enabl } } \\ { \text { is 1b and the } } \end{array}$ $\begin{array}{} { \text { message is fo } } \\ { \text { Stack } 1 } \end{array}$ $F F F F h : S t a l l$</td>
<td>$\begin{array}{} { \text { CXL protocols, as specified in the } } \\ { \text { Protocol Layer interoperability } } \end{array}$ requirements. · $\left[ 8 \right] : M u l t i - L o g i c a l \quad D e v i c e \quad - \quad m u s t \quad b e$ · [9]: Reserved. · $\begin{array}{} { \left[ 1 2 : 1 0 \right] : \text { these bits do not apply for } } \\ { \text { UCIe, must be nh } } \end{array}$ · $\begin{array}{} { \left[ 1 4 \right] : \text { Retimer } 2 - \text { does not apply fo } } \\ { \text { UCIe. must be 0b } } \end{array}$ · $\begin{array}{} { \left[ 1 5 \right] : \text { CXL.io Throttle } - \text { must be 0b } } \\ { \text { for PCIe Non-Fitt Mode. } } \end{array}$ · $\begin{array}{} { \left[ 1 7 : 1 6 \right] : \text { NOP Hint Info- does not } } \\ { \text { apply for UCIe, and must be } 0 } \end{array}$</td>
<td>Finalized Capabilities for CXL protocol.</td>
</tr>
<tr>
<td>{MultiProtAdvCap. Adapter}</td>
<td>01h</td>
<td>$0 2 h$</td>
<td>0000h: Reserved $F F F F h : S t a l l$</td>
<td>[0]: "68B Flit Mode" [1]: "CXL 256B Flit Mode" [2]: "PCIe Flit Mode" $\begin{array}{} { \text { \left[3\right]: ^{\text{w Streaming Protocol } ^ { \prime \prime } } } } \\ { \left[ 4 \right] : \text { managent Transport Protocol } ^ { \prime } } \end{array}$ [63:5]: Reserved</td>
<td>Protocol $\begin{array}{} { \text { Advertisement fol } } \\ { \text { Stack } 1 \text { when } } \end{array}$ Enhanced Multi_Protocol_En able is negotiated</td>
</tr>
<tr>
<td>{MultiProtFinCap. Adapter}</td>
<td>02h</td>
<td>$0 2 h$</td>
<td>0000h: Reserved $\begin{array}{} { \text { FFFh: Stal } } \\ { \text { Messane } } \end{array}$</td>
<td>$\left[ 0 \right] : \text { vesB Flit Mode^{\prime\prime } }$ [1]: "CXL 256B [2]: "PCIe Flit Mode" [3]: Reserved [4]: "Management Transport Protocol" $\left[ 6 3 : 5 \right] : R e s e r v e d$</td>
<td>Finalized Capability for Protocol negotiation when Enhanced Multi_Protocol_En $a n d \quad S t a c k \quad 1 \quad i s$</td>
</tr>
</table>

<table>
<caption>Table 7-10. Message encodings for Messages with Dataª (Sheet 3 of 3)</caption>
<tr>
<th>Name</th>
<th>Msg code</th>
<th>Msgsubcode</th>
<th>MsgInfo</th>
<th>Data Bit Encodings</th>
<th>Description</th>
</tr>
<tr>
<td>$V e n d o r \quad D e f i n e d$</td>
<td>$F F h$</td>
<td></td>
<td>Vendor ID</td>
<td></td>
<td>Vendor Defined Messages. These can be $\begin{array}{} { \text { exchanged at an } } \\ { \text { time after } } \end{array}$ sideband is functional post SBINIT. Interoperability is vendor defined. Unsupported vendor defined messages must $\begin{array}{} { \text { be discarded by } } \\ { \text { the receiver. } } \end{array} .$ that this is NOT the UCIe Vendor ID, but rather the unique identifier of the $\begin{array}{} { \text { chiplet vendor } } \\ { \text { that is defining } } \end{array}$ and using these messages.</td>
</tr>
</table>

a. All other encodings not mentioned in this table are reserved.

<table>
<caption>Table 7-11. Link Training State Machine related encodings (Sheet 1 of 6)</caption>
<tr>
<th>Message</th>
<th>MsgInfo[15:0]</th>
<th>MsgCode [7:0]</th>
<th>MsgSubcode [7:0]</th>
<th>Data Field [63:0]</th>
</tr>
<tr>
<td>{Start Tx Init D to $C$ point test req}</td>
<td>[15:0]: Maximum comparison error threshold</td>
<td>85h</td>
<td>01h</td>
<td>[63:60]: Reserved [59]: Comparison Mode (0: Per Lane; 1: $\begin{array}{} { \text { Aggregate\right) } } \\ { \left[ 5 8 : 4 3 \right] : \text { Iteration Count Settings } } \end{array}$ [42:27]: Idle Count settings $\left[ 1 0 \right] : P a t t e r n \quad M o d e \left( 0 : c o n t i n u o u s \quad m o d e , 1 : \right.$ Burst Mode) $\begin{array}{} { \left[ 9 : 6 \right] : \text { Clock Phase control at } T \times \text { Device } \left( 0 h \right. } \\ { \text { Clock PI Center, } 1 h : L e f t E d g e , 2 h : \text { Right } } \end{array} :$ $\left[ 5 : 3 \right] : V a l i d \quad P a t t e r n \left( O h : F u n c t i o n a l \quad p a t t e r n \right)$ [2:0]: Data pattern (0h: LFSR, 1h: Per Lane ID)</td>
</tr>
</table>

<table>
<caption>Table 7-11. Link Training State Machine related encodings (Sheet 2 of 6)</caption>
<tr>
<th>Message</th>
<th>MsgInfo[15:0]</th>
<th>$\begin{array}{} { 4 \mathrm { s g } \mathrm { c o d } } \\ { \left[ 7 : 0 \right] } \end{array}$</th>
<th>$M s g S u b c o d e$ $\left[ 7 : 0 \right]$</th>
<th>Data Field [63:0]</th>
</tr>
<tr>
<td>$\left\{ \begin{array}{} { T x \text { Init } D \text { to } } \\ { \left. \text { racults resp } \right\} } \end{array} \right.$ C</td>
<td>$\left[ 1 5 : 6 \right] : R e s e r v e d$ [5]: Valid Lane comparison results of $a l l \quad L a n e s \left( 0 : F a i l \left( E r r o r s \right. \right.$ &gt; 1: Pass (Errors &lt;= Max Error Threshold)). [3:0]: UCIe-A: Compare results from Redundant Lanes (0h: Fail (Errors &gt; Max Error $\begin{array}{} { \text { Threshold\right), } 1 h : \text { Pass } \left( \text { Error } \right. } \\ { \left. < = \text { Max Error Threshold } \right) } \end{array}$ (RRD_L [3], RRD_L[2], RRD_L [1], RRD_L [0]) UCIe-S: Reserved RRD_L [3] and RRD_L $\left[ 2 \right]$ $\begin{array}{} { \text { are reserved for UCIe-A } x 3 2 } \\ { \text { as a transmitter of this } } \end{array}$</td>
<td>8Ah</td>
<td>03h</td>
<td>[63:0]: Compare Results of individual Data Lanes (0h: Fail (Errors &gt; Max Error Threshold), 1h: Pass (Errors &lt;= Max Error Threshold)) UCIe-A {RD_L [63], RD_L [62], .... , RD_L [1], RD_L [0]} $\begin{array}{} { \text { UCIe-S } \left\{ 4 8 h 0 , R D , L \left[ 1 5 \right] , R D , L \left[ 1 4 \right] , \ldots \right. } \\ { \left. \left. \text { RD } I L I \right] , R D L I O T \right\} } \end{array} .$ , $\sqrt { 3 2 } ^ { \prime } h 0 ,$ $\begin{array}{} { \text { UCIe- } S \times 8 \left\{ 5 6 ^ { \prime } h 0 , R D , L \left[ 7 \right] , R D _ { - } L \left[ 6 \right] , \cdots , \right. } \\ { \left. \text { RD LI } 1 1 . R D \text { IJ } 0 1 \right\} } \end{array} ,$</td>
</tr>
<tr>
<td>$T \times \text { Init } D$ eye sweep req}</td>
<td>[15:0]: Maximum comparison error threshold</td>
<td>85h</td>
<td>$0 5 h$</td>
<td>$\left[ 6 3 : 6 0 \right] :$ Reserved [59]: Comparison Mode (0: Per Lane; 1: $\left[ 5 8 : 4 3 \right] : I t e r a t i o n \quad C o u n t \quad S e t t i n g s$ [42:27]: Idle Count settings $\left[ 1 0 \right] : P a t t e r n \quad M o d e \left( 0 : c o n t i n u o u s \quad m o d e , 1 : \right.$ Burst Mode) $\begin{array}{} { \left[ 9 : 6 \right] : \text { Clock Phase control at } T \times \text { Device } \left( 0 h \right. } \\ { \text { Clock PI Center, } 1 h : \text { Left Edge, } 2 h : \text { Right } } \end{array} :$ $\left[ 5 : 3 \right] : V a l i d \quad P a t t e r n \left( O h : F u n c t i o n a l \quad p a t t e r n \right)$ ID) [2:0]: Data pattern (0h: LFSR, 1h: Per Lane</td>
</tr>
<tr>
<td>{Start Rx Init D to C point test req}</td>
<td>[15:0]: Maximum comparison error threshold</td>
<td>$8 5 h$</td>
<td>07h</td>
<td>[63:60]: Reserved [59]: Comparison Mode (0: Per Lane; 1: Aggregate) [58:43]: Iteration Count Settings [42:27]: Idle Count settings [26:11]: Burst Count settings [10]: Pattern Mode (0: continuous mode, 1: Burst Mode) [9:6]: Clock Phase control at Transmitter (0h: Clock PI Center, 1h: Left Edge, 2h: Right Edge) [5:3]: Valid Pattern (0h: Functional pattern) [2:0]: Data pattern (0h: LFSR, 1h: Per Lane ID)</td>
</tr>
</table>

<table>
<caption>Table 7-11. Link Training State Machine related encodings (Sheet 3 of 6)</caption>
<tr>
<th>Message</th>
<th>MsgInfo[15:0]</th>
<th>$\begin{array}{} { \text { Msgcod } } \\ { \left[ 7 : 0 \right] } \end{array}$</th>
<th>$\begin{array}{} { \text { MsgSubcouc } } \\ { \left[ 7 : 0 \right] } \end{array}$ $\left[ 7 : 0 \right]$</th>
<th>Data Field [63:0]</th>
</tr>
<tr>
<td>{Start Rx Init D to C eye sweep req}</td>
<td>$c o m p a r i s o n \quad e r r o r \quad t h r e s h o l d$</td>
<td>$8 5 h$</td>
<td>0Ah</td>
<td>$\left[ 6 3 : 6 0 \right] :$ Reserved [59]: Comparison Mode (0: Per Lane; 1: Aggregate) [58:43]: Iteration Count Settings $\left[ 4 2 : 2 7 \right] : I d l e \quad C o u n t \quad s e t t i n g s$ [26:11]: Burst Count settings [10]: Pattern Mode (0: continuous mode, 1: Burst Mode) $\begin{array}{} { \text { \left[9:6\right]: Clock Phase control at Transmitter } } \\ { \text { \left(0h: Clock PI Center, 1h: Left Edge, } 2 h : } \end{array} :$ $\left[ 5 : 3 \right] : V a l i d \quad P a t t e r n \left( O h : F u n c t i o n a l \quad p a t t e r n \right)$ [2:0]: Data pattern (0h: LFSR, 1h: Per Lane ID)</td>
</tr>
<tr>
<td>$\begin{array}{} { \left\{ R \times \text { Init } D \text { to } C \right. } \\ { \left. \text { results resp } \right\} } \end{array}$</td>
<td>$\begin{array}{} { \left[ 1 5 : 6 \right] : \text { Reservea } } \\ { \left[ 5 \right] : \text { Valid Lane comparison } } \end{array}$ result [4]: Cumulative Results of all Lanes (0: Fail (Errors &gt; Max Error Threshold), $P a s s \left( E r r o r s < = M a x \quad E r r o r \right.$ $U C I e - A : C o m p a r e \quad r e s u l t s$ from Fail (Errors &gt; Max Error $\begin{array}{} \left. \text { Threshold\right), 1h: Pass\left(Error: } \\ < = \text { Max Error Threshold } \right) \end{array}$ (RRD_L [3], RRD_L[2], RRD_L [1], RRD_L [0]) UCIe-S: Reserved $\mathrm { R e D } _ { - } L \left[ 3 \right] \text { and } R R D _ { L } \left[ 2 \right]$ $\begin{array}{} { \text { are reserved for UCIe-A } \times 3 2 } \\ { \text { as a transmitter of this } } \end{array}$ message.</td>
<td>8Ah</td>
<td>0Bh</td>
<td>[63:0]: Compare Results of individual Data Lanes (Oh: Fail (Errors &gt; Max Error $\begin{array}{} \left. \text { Threshold } \right) \\ \text { Threshold } \end{array} ,$ 1h: Pass (Errors &lt;= Max Error $\begin{array}{} { \text { UCIe-A } \left\{ R D L \left[ 6 3 \right] , R D _ { - } L \left[ 6 2 \right] , \cdots , \right. } \\ { \left. \text { RD LII } , R D L \left[ 0 \right] \right\} } \end{array} ,$ UCIe-S {48'h0, RD_L [15], RD_L [14], ... , $\mathrm { R D } \mathrm { L } \left[ 1 \right] ,$ RD_L $\begin{array}{} { \text { UCIe-A } \times 3 2 \left\{ 3 2 ^ { \prime } h 0 , R D , L \left[ 3 1 \right] , R D _ { - } L \left[ 3 0 \right] \right. } \\ { \left. \cdots , R D L \left[ 0 \right] \right\} } \end{array} ,$ $\begin{array}{} { \text { UCIe-S } \times 8 \left\{ 5 6 ^ { \prime } h 0 , R D , L \left[ 7 \right] , R D _ { - } L \left[ 6 \right] , \ldots , \right. } \\ { \left. \text { RD } _ { - } L \left[ 1 \right] , R D _ { - } L \left[ 0 \right] \right\} ^ { - } } \end{array} ,$</td>
</tr>
<tr>
<td>$R x \quad I n i t \quad D \quad t o \quad C$ sweep done with results}</td>
<td>$0 0 0 0 h$</td>
<td>81h</td>
<td>$0 C h$</td>
<td>$\left[ 6 3 : 1 6 \right] :$ Reserved $\left[ 1 5 : 8 \right] :$ $\begin{array}{} { 1 6 3 : 1 0 1 : \text { Right Edge } } \\ { 1 1 5 : 8 1 : \text { Right Edge } } \end{array}$ $\left[ 7 : 0 \right] : L e f t \quad E d g e$</td>
</tr>
<tr>
<td>$\left\{ \mathrm { M B I N I T } . \mathrm { P A R A M } \right.$</td>
<td>0000h</td>
<td>$A 5 h$</td>
<td>$0 0 h$</td>
<td>[63:16]: Reserved $\begin{array}{} { \left[ 1 5 \right] : \text { Tx Adjustment during Runtime } } \\ { \text { Recalibration \left(TARR\right) is supported } \left( 1 \right) \text { or not } } \end{array}$ supported (0) $\begin{array}{} { \left[ 1 4 \right] : \text { Sideband feature extensions is } } \\ { \text { supported } \left( 1 \right) \text { or not supported } \left( 0 \right) } \end{array}$ $\begin{array}{} { \left[ 1 3 \right] : \text { UCIe-A x32 if Advanced Package; } } \\ { \text { UCIe-S x8 if Standard Package. } } \end{array}$ [12:11]: Module ID: 0h: 0, 1h: 1, 2h: 2, 3h:3 $\left[ 1 0 \right] : C l o c k \quad P h a s e : 0 b :$ Differential clock, 1b: Quadrature phase 0b: Strobe mode; 1b: $C o n t i n u o u s \quad m o d e$ [8:4]: Voltage Swing - The encodings are the same as the "Supported Tx Vswing encodings" field of the PHY Capability register $\left[ 3 : 0 \right] : M a x \quad I O \quad L i n k \quad S p e e d \quad - \quad T h e \quad e n c o d i n g s$ $\begin{array}{} { \text { are une same as whax Link Speeds^{\prime\prime } \text { field of } } } \\ { \text { the UCIe Link Capability register } } \end{array}$</td>
</tr>
</table>

<table>
<caption>Table 7-11. Link Training State Machine related encodings (Sheet 4 of 6)</caption>
<tr>
<th>Message</th>
<th>MsgInfo[15:0]</th>
<th>MsgCode $\left[ 7 : 0 \right]$</th>
<th>$\begin{array}{} { \text { MsgSubcouc } } \\ { \left[ 7 : 0 \right] } \end{array}$ $\left[ 7 : 0 \right]$</th>
<th>Data Field [63:0]</th>
</tr>
<tr>
<td>{MBINIT.PARAM configuration resp}</td>
<td>0000h</td>
<td>AAh</td>
<td>00h</td>
<td>$\begin{array}{} { \left[ 6 3 : 1 6 \right] : \text { Reserved } } \\ { \left[ 1 5 \right] : \text { Tx Adjustment during Runtime } } \\ { \left[ 1 5 \right] : \text { Tx Adjun \left(TARR\right) is negotiated } \left( 1 \right) \text { or not } } \end{array}$ supported (0) $\begin{array}{} { \left[ 1 4 \right] : \text { Sideband feature extensions is } } \\ { \text { negotiated } \left( 1 \right) \text { or not supported } \left( 0 \right) } \end{array}$ [13:11]: Reserved [10]: Clock Phase: 0b: Differential clock, 1b: Quadrature phase $\left[ 9 \right] : C l o c k \quad M o d e \quad - \quad O b :$ Strobe mode; 1b: [8:4]: Reserved [3:0]: Max $\begin{array}{} { \text { are the same as whax Link Speeds fincodings } } \\ { \text { the UCIe Link Capability reqister } } \end{array}$</td>
</tr>
<tr>
<td>{MBINIT.PARAM $\left. \mathrm { S B F E } \mathrm { r e q } \right\}$</td>
<td>0000h: Regular Message</td>
<td>$A 5 h$</td>
<td>01h</td>
<td>$\begin{array}{} { \left[ 6 3 : 5 \right] : \text { Reserved } } \\ { \left[ 4 \right] : L 2 S P D \text { is supported } \left( 1 \right) \text { or not supportec } } \end{array}$ (0) [3]: PSPT is supported (1) or not supported (0) $\left[ 2 \right] : S i d e b a n d - o n l y \left( S O \right) p o r t \left( 1 \right) , f u l l \quad U C I e$ [1]: Sideband Performant Mode Operation (PMO) is supported (1) or not supported (0) $\begin{array}{} { \text { \left[0\right]: Management Transport protocol is } } \\ { \text { supported } \left( 1 \right) \text { or not supported } \left( 0 \right) } \end{array}$</td>
</tr>
<tr>
<td>{MBINIT.PARAM SBFE resp}</td>
<td>0000h: Regular Message FFFFh: Stall Message</td>
<td>AAh</td>
<td>01h</td>
<td>[63:5]: Reserved [4]: L2SPD is negotiated (1) or not $\begin{array}{} { \text { negotiated \left(0\right) } } \\ { \left[ 3 \right] : \text { PSPT is negotiated } \left( 1 \right) \text { or not negotiatec } } \end{array}$ (0) port (0) [2]: Sideband-only (SO) port (1), full UCIe $\begin{array}{} { \text { \left[1\right]: Sideband Performant Mode Operation } } \\ { \text { \left(PMO\right) is negotiated } \left( 1 \right) \text { or not supported } \left( 0 \right. } \end{array}$ $\begin{array}{} { \text { IOJ: Managernent Transport protocol is } } \\ { \text { supported } \left( 1 \right) \text { or not supported } \left( 0 \right) } \end{array}$</td>
</tr>
<tr>
<td>{MBINIT.REVERSAL MB result resp}</td>
<td>$\begin{array}{} { \text { The error condition for this } } \\ { \text { show is NoT observing } 1 6 } \end{array}$ consecutive iterations of the expected pattern. The error threshold is always 0 for this test. [15:4]: Reserved [3:0]: $\mathrm { J C I e - A : } \text { Compare results }$ Fail (Errors &gt; Max Error $\begin{array}{} \left. \text { Threshold\right), } 1 h : \text { Pass \left(Error\right) } \\ < = \text { Max Error Threshold } \right) \end{array}$ $\left. R R D \_ L \left[ 1 \right] , R R D \_ L \left[ 0 \right] \right)$ $R R D \_ L \left[ 3 \right] a n d \quad R R D \_ L \left[ 2 \right]$ $\begin{array}{} { \text { are reserved for UCIe-A } \times 3 2 } \\ { \text { as a transmitter of this } } \end{array}$</td>
<td>AAh</td>
<td>0Fh</td>
<td>The error condition for this flow is NOT $e x p e c t e d \quad p a t t e r n . T h e \quad e r r o r \quad t h r e s h o l d \quad i s$ [63:0]: Compare Results of individual Data Lanes (Oh: Fail (Errors &gt; Max Error Threshold), 1h: Pass (Errors &lt;= Max Error Threshold)) $\begin{array}{} { \text { UCIe-A } \left\{ R D \text { L } \left[ 6 3 \right] , R D _ { - } L \left[ 6 2 \right] , \cdots , \right. } \\ { \left. \text { RD } _ { - } L \left[ 1 \right] , R D _ { - } L \left[ 0 \right] \right\} } \end{array} ,$ $\begin{array}{} { \text { UCIe-S } \left\{ 4 8 ^ { \prime } h 0 , R D , L \left[ 1 5 \right] , R D _ { - } \left[ \left[ 1 4 \right] , \right. \right. } \\ { \left. \text { RD } _ { - } L \left[ 1 \right] , R D _ { - } L \left[ 0 \right] \right\} } \end{array} .$ , $\begin{array}{} { \text { UCIe-A } \times 3 2 \left\{ 3 2 ^ { 2 } h 0 , R D , L \left[ 3 1 \right] , R D _ { - L } \left[ 3 0 \right] \right. } \\ { \cdots , R D L \left[ 0 1 \right\} ^ { 3 } } \end{array} ,$ $\begin{array}{} { \text { UCIe-S } \times 8 \left\{ 5 6 ^ { \prime } h 0 , R D , L \left[ 7 \right] , R D _ { - } L \left[ 6 \right] , \ldots , \right. } \\ { \left. \text { RD } _ { - } L \left[ 1 \right] , R D _ { - } L \left[ 0 \right] \right\} } \end{array} ,$</td>
</tr>
</table>

<table>
<caption>Table 7-11. Link Training State Machine related encodings (Sheet 5 of 6)</caption>
<tr>
<th>Message</th>
<th>MsgInfo[15:0]</th>
<th>$\begin{array}{} { \text { MsgCod } } \\ { \left[ 7 : 0 \right] } \end{array}$</th>
<th>$\begin{array}{} { \text { MsgSubcoue } } \\ { \left[ 7 : 0 \right] } \end{array}$</th>
<th>Data Field [63:0]</th>
</tr>
<tr>
<td rowspan="2">{MBINIT.REPAIRMB Apply repair req}</td>
<td rowspan="2">0000h</td>
<td rowspan="2">$A 5 h$</td>
<td rowspan="2">$1 2 h$</td>
<td>[31:24]: Repair Address for TRD_P[3]: Indicates the physical Lane repaired when $\begin{array}{} { \text { TRD_P\left[3\right] is used in remapping scheme. Thi } } \\ { \text { is reserved for UCIe-A } x 3 2 \text { as a transmiter } } \end{array}$ of this message. $2 1 h : T D _ { - }$ 22h: TD_P[34] Repaired ...... 3Eh: TD_P[62] Repaired 3Fh: TD_P[63] Repaired F0h: Reserved $\left[ 2 3 : 1 6 \right] : \text { Repair Address for TRD } _ { - } :$ $\begin{array}{} { \text { TRD_P\left[2\right] is used in remapping scheme. This } } \\ { \text { is reserved for UCIe-A x32 as a transmitter } } \end{array}$ 20h: TD_P[32] Repaired $2 1 h : T D _ { - } P \left[ 3 3 \right]$</td>
</tr>
<tr>
<td>$3 E h : T D _ { - } P \left[ 6 2 \right]$ 3Fh: TD_P[63] Repaired F0h: Reserved FFh: No Repair $\begin{array}{} { \left[ 1 5 : 8 \right] : \text { Repar Auquress repared whe } } \\ { \text { Indicates the physical Lane repaired whe } } \\ { \text { Ton pril is lis lin remapping scheme. } } \end{array}$ 00h: Invalid 01h: TD_P[1] Repaired 02h: TD_P[2] Repaired ...... 1Eh: TD_P[30] Repaired 1Fh: TD_P[31] Repaired F0h: Reserved $\begin{array}{} { \text { FFh: No Repair } } \\ { \text { Tr:0\right]: Reparir Address for TRD_PIOI: } } \\ { \text { I7: } 0 \text { l: Repair Address for renaired whe } } \end{array} :$ $\begin{array}{} { \text { Indicates the physical Lane repaired whe } } \\ { \text { TRD PIOI is used in remapping scheme. } } \end{array}$ 00h: TD_P[0] Repaired 01h: TD_P[1] Repaired 02h: TD_P[2] Repaired ...... 1Eh: TD_P[30] Repaired 1Fh: TD_P[31] Repaired F0h: Reserved FFh: No Repair</td>
</tr>
</table>

<table>
<caption>Table 7-11. Link Training State Machine related encodings (Sheet 6 of 6)</caption>
<tr>
<th>Message</th>
<th>MsgInfo[15:0]</th>
<th>$\begin{array}{} { \text { MsgCod } } \\ { \left[ 7 : 0 \right] } \end{array}$</th>
<th>$\begin{array}{} { \text { MsgSubcoue } } \\ { \left[ 7 : 0 \right] } \end{array}$</th>
<th>Data Field[63:0]</th>
</tr>
<tr>
<td>{MBTRAIN.REPAIR Apply repair req}</td>
<td>0000h</td>
<td>B5h</td>
<td>1Ch</td>
<td>[31:24]: Repair Address for TRD_P[3]: Indicates the physical Lane repaired when $\begin{array}{} { \text { TRD_P\left[3\right] is used in remapping scheme. Thi } } \\ { \text { is reserved for UCIe-A } x 3 2 \text { as a transmiter } } \end{array}$ of this message. $2 1 h : T D _ { - }$ 22h: TD_P[34] Repaired ...... 3Eh: TD_P[62] Repaired 3Fh: TD_P[63] Repaired F0h: Reserved $\left[ 2 3 : 1 6 \right] : \text { Repair Address for TRD } _ { - } :$ $\begin{array}{} { \text { TRD_P\left[2\right] is used in remapping scheme. This } } \\ { \text { is reserved for UCIe-A x32 as a transmitter } } \end{array}$ 20h: TD_P[32] Repaired $2 1 h : T D _ { - } P \left[ 3 3 \right]$ $3 E h : T D _ { - } P \left[ 6 2 \right]$ 3Fh: TD_P[63] Repaired F0h: Reserved FFh: No Repair $\begin{array}{} { \left[ 1 5 : 8 \right] : \text { Repar Auquress repared whe } } \\ { \text { Indicates the physical Lane repaired whe } } \\ { \text { Ton pril is lis lin remapping scheme. } } \end{array}$ 00h: Invalid 01h: TD_P[1] Repaired 02h: TD_P[2] Repaired ...... 1Eh: TD_P[30] Repaired 1Fh: TD_P[31] Repaired F0h: Reserved $\begin{array}{} { \text { FFh: No Repair } } \\ { \text { Tr:0\right]: Reparir Address for TRD_PIOI: } } \\ { \text { I7: } 0 \text { l: Repair Address for renaired whe } } \end{array} :$ $\begin{array}{} { \text { Indicates the physical Lane repaired whe } } \\ { \text { TRD PIOI is used in remapping scheme. } } \end{array}$ 00h: TD_P[0] Repaired 01h: TD_P[1] Repaired 02h: TD_P[2] Repaired ...... 1Eh: TD_P[30] Repaired 1Fh: TD_P[31] Repaired F0h: Reserved FFh: No Repair</td>
</tr>
</table>

### 7.1.2.4 Management Port Message (MPM) with Data

As with all sideband messages, Management Port Messages with Data also carry a 1-QWORD header.
This is referred to as "MPM header" (see Figure 7-5) for the remainder of this section. The payload in
these messages is referred to as "MPM payload" for the remainder of this section.

Bits [21:14] in the first DW of the MPM Hdr of an MPM with Data message, forms an 8b msgcode that
denotes a specific MPM with Data message. Table 7-12 summarizes the supported MPM with Data
messages over sideband.

Support for these messages is optional and negotiated as described in Section 8.2.3.1.

<table>
<caption>Table 7-12. Supported MPM with Data Messages on Sideband</caption>
<tr>
<th>msgcode</th>
<th>Message</th>
</tr>
<tr>
<td>01h</td>
<td>Encapsulated MTP Message</td>
</tr>
<tr>
<td>FFh</td>
<td>Vendor-defined Management Port Gateway Message</td>
</tr>
<tr>
<td>Others</td>
<td>Reserved</td>
</tr>
</table>

### 7.1.2.4.1 Common Fields in MPM Header of MPM with Data Messages on Sideband

Figure 7-5 shows and Table 7-13 describes the common fields in the MPM header of MPM with data
messages on the sideband.

<table>
<caption>Figure 7-5. Common Fields in MPM Header of all MPM with Data Messages on Sideband</caption>
<tr>
<th colspan="8">3</th>
<th colspan="8">2</th>
<th colspan="8">1</th>
<th colspan="8">0</th>
</tr>
<tr>
<th colspan="2">31 30</th>
<th>29</th>
<th>28</th>
<th>27</th>
<th>26</th>
<th>25</th>
<th>24</th>
<th>23</th>
<th>22</th>
<th>21</th>
<th>20</th>
<th>19</th>
<th>18</th>
<th>17</th>
<th>16</th>
<th>15</th>
<th>14</th>
<th>13</th>
<th>12</th>
<th>11</th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th>109876543210</th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
</tr>
<tr>
<td colspan="3">srcid=011b</td>
<td></td>
<td colspan="2">rsvd</td>
<td>re sp</td>
<td></td>
<td>VC</td>
<td></td>
<td></td>
<td></td>
<td colspan="4">msgcode</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td colspan="4">length</td>
<td colspan="2"></td>
<td>rs vd</td>
<td colspan="5">opcode $= 1 1 0 0 0 b$</td>
</tr>
<tr>
<td>$r s$ vd</td>
<td>cp</td>
<td colspan="3">rsvd</td>
<td colspan="3">dstid=111b</td>
<td></td>
<td></td>
<td></td>
<td colspan="8">msgcode-specific</td>
<td></td>
<td colspan="4"></td>
<td colspan="2">rsvd</td>
<td colspan="2">msgcode- specific</td>
<td colspan="2">rsvd</td>
<td colspan="2">rxqid</td>
</tr>
</table>

<table>
<caption>Table 7-13. Common Fields in MPM Header of all MPM with Data Messages on Sideband</caption>
<tr>
<th>Field</th>
<th>Description</th>
</tr>
<tr>
<td>opcode</td>
<td>11000b: MPM with Data.</td>
</tr>
<tr>
<td>length</td>
<td>MPM Payload length (i.e., 0h for 1 QWORD, 1h for 2 QWORDs, 2h for 3 QWORDs, etc.).</td>
</tr>
<tr>
<td>msgcode</td>
<td>Message code as defined in Table 7-12.</td>
</tr>
<tr>
<td>$V C$</td>
<td>Virtual Channel ID.</td>
</tr>
<tr>
<td>resp</td>
<td>0: Request MPM. 1: Response MPM. Management Port Gateway Message with Data, this bit is $\mathrm { a l w a y s } 0$ $\left( s e e \quad S e c t i o n \quad 7 . 1 . 2 . 4 . 3 \right) .$</td>
</tr>
<tr>
<td>srcid</td>
<td>011b: Indicates Management Port Gateway as source. Other values: Not applicable to $M P M .$ For details on other values of srcid, see Table 7-2, Table 7-3, and Table 7-4.</td>
</tr>
<tr>
<td>rxqid</td>
<td>$\text { RxQ-ID to which this packet is destined, and } R \times Q \text { and RSSociated with any credits }$</td>
</tr>
<tr>
<td>dstid</td>
<td>$\begin{array}{} { 1 1 1 b : \text { Indicates Managenent Portent Gateway as target. Other values: } \text { Not applicable to } } \\ { \text { MPM. For details on other values of dstid, see Table } 7 - 2 , \text { Table } 7 - 3 , \text { and Table } 7 - 4 . } \end{array}$</td>
</tr>
<tr>
<td>cp</td>
<td>Control parity for the sideband packet header. All fields other than "cp" in the header are protected by Control Parity, and the parity scheme is even (including reserved bits).</td>
</tr>
</table>

#### 7.1.2.4.2 Encapsulated MTP Message

Encapsulated MTP on sideband is an MPM with Data message with a msgcode of 01h.

<table>
<caption>Figure 7-6. Encapsulated MTP on Sideband</caption>
<tr>
<th></th>
<th colspan="7">3</th>
<th colspan="8">2</th>
<th colspan="8">1</th>
<th colspan="7">0</th>
</tr>
<tr>
<th>31</th>
<th>30</th>
<th>29</th>
<th>28</th>
<th>27</th>
<th>26</th>
<th>25</th>
<th>24</th>
<th>23</th>
<th>22</th>
<th>21</th>
<th>20</th>
<th>19</th>
<th>18</th>
<th>17</th>
<th>16</th>
<th>15</th>
<th>14</th>
<th>13</th>
<th>12</th>
<th>11</th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th>109876543210</th>
<th></th>
<th></th>
</tr>
</table>

$\mathrm { s r c i d } =$
011b

rsvd

re
sp

$\mathrm { v c }$

$m s g c o d e = 0 1 h$

length

rs

opcode = 11000b

vd

a

rs
vd

cp

rsvd

$d s t i d = 1 1 1 b$

cr_ret_vc

$c r \_ r e t \left( i n \quad Q W O R D s \right)$

rsvd

s

p

rsvd

rxqid

<table>
<tr>
<td>...</td>
<td>...</td>
<td>DWORD 0: Byte 1</td>
<td>DWORD 0: Byte 0</td>
</tr>
<tr>
<td>...</td>
<td>...</td>
<td>DWORD 1: Byte 1</td>
<td>DWORD 1: Byte 0</td>
</tr>
</table>

b

d

...

1 DWORD padding of all 0s (if required)

e

a. MPM Header.

b. MPM Payload.

c. Management Transport Packet (MTP).

d. Length in MPM Header.

e. DWORD padding.

<table>
<caption>Table 7-14. Encapsulated MTP on Sideband Fields</caption>
<tr>
<th>Location</th>
<th>Bit</th>
<th>Description</th>
</tr>
<tr>
<td rowspan="7">$\mathrm { M P M } \mathrm { H e a d e r } ^ { \mathrm { a } }$</td>
<td>s</td>
<td>Segmented MTP (see Section 8.2.4.2). The first and middle segments in a segmented MTP have this bit set to 1. The last segment in a segmented MTP will have this bit cleared to 0. An unsegmented MTP also has this bit cleared to 0.</td>
</tr>
<tr>
<td>$p$</td>
<td>$I f \quad t h i s \quad i s \quad s e t \quad t o \quad 1 , t h e r e \quad i s \quad 1 - D W O R D \quad p a d d i n g \quad o f \quad a l l \quad O s \quad a d d e d \quad a t \quad t h e \quad e n d \quad o f$</td>
</tr>
<tr>
<td rowspan="3">cr_ret</td>
<td>Value of RxQ credits being returned to the MPG receiving this message, indicated by the rxqid value and its VC: Resp channel indicated via cr_ret_vc/cr_ret_resp fields. 000h indicates 0 credits returned. 001h indicates 1 credit returned.</td>
</tr>
<tr>
<td>3FEh indicates 1022 credits returned. 3FFh is reserved.</td>
</tr>
<tr>
<td>If there is no credit being returned, cr_ret fields must be set to 0h.</td>
</tr>
<tr>
<td>cr_ret_vc</td>
<td>VC associated with the credit returned.</td>
</tr>
<tr>
<td>$\mathrm { c r } _ { - } \mathrm { r e t } _ { - } \mathrm { r e s p }$</td>
<td>Resp value associated with the credit returned. 0=Request channel credit. 1 =Response channel credit.</td>
</tr>
<tr>
<td>MPM Payload</td>
<td>—</td>
<td>See Section 8.2 for details. Note that DWORDx: Bytey in Figure 7-6 refers to the corresponding DWORD, Byte defined in the Management Transport Packet in Figure 8-5.</td>
</tr>
</table>

a. See Section 7.1.2.4.1 for details of header fields common to all MPMs with data on the sideband.

cr
ret
re

sp

c

#### 7.1.2.4.3 Vendor-defined Management Port Gateway Message

The Vendor-defined Management Port Gateway message with data is defined for custom
communication between MPGs on the two ends of a UCIe sideband link. These messages are not part
of the Management transport protocol, and these messages start at an MPG and terminate at the MPG
on the other end of the UCIe sideband link. These messages share the same RxQ-ID request buffers
and credits as encapsulated MTP messages. If an MPG does not support these messages or does not
support vendor-defined messages from a given vendor (identified by the UCIe Vendor ID in the
header), the MPG silently drops those messages. Length of these Vendor defined messages is subject
to the same rules stated in Section 8.2.5.1.2. Ordering of these messages sent over multiple
sideband links is subject to the same rules presented in Section 8.2.4.3 for encapsulated MTPs.

<table>
<caption>Figure 7-7. Vendor-defined Management Port Gateway Message with Data on Sideband</caption>
<tr>
<th colspan="8">3</th>
<th colspan="8">2</th>
<th colspan="8">1</th>
<th colspan="8">0</th>
</tr>
<tr>
<th>31</th>
<th>30</th>
<th>29</th>
<th>28</th>
<th>27</th>
<th>26</th>
<th>25</th>
<th>24</th>
<th>23</th>
<th>22</th>
<th>21</th>
<th>20</th>
<th>19</th>
<th>18</th>
<th>17</th>
<th>16</th>
<th>15</th>
<th>14</th>
<th>13</th>
<th>12</th>
<th>11</th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th>109876543210</th>
<th></th>
<th></th>
<th></th>
<th></th>
</tr>
<tr>
<td colspan="3">$s r c i d = 0 1 1 b$</td>
<td></td>
<td>rsvd</td>
<td></td>
<td>$r e$ sp = 0</td>
<td></td>
<td>VC</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>msgcode</td>
<td colspan="2">= FFh</td>
<td></td>
<td></td>
<td></td>
<td colspan="2"></td>
<td>length</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>rs vd</td>
<td></td>
<td></td>
<td></td>
<td>$o p c o d e = 1 1 0 0 0 b$</td>
<td></td>
</tr>
</table>

<figure>

a

$r s$
vd

cp

rsvd

$d s t i d = 1 1 1 b$

UCIe Vendor ID

rsvd

rxqid

$b$

Vendor-defined payload

c

</figure>

a. MPM Header.

b. MPM Payload.

c. Length in MPM Header.

<table>
<caption>Table 7-15. Vendor-defined Management Port Gateway Message with Data on Sideband Fields</caption>
<tr>
<th>Location</th>
<th>Field</th>
<th>Description</th>
</tr>
<tr>
<td>MPM Headerª</td>
<td>UCIe Vendor ID</td>
<td>UCIe Consortium-assigned unique ID for each vendor.</td>
</tr>
<tr>
<td>MPM Payload</td>
<td>—</td>
<td>Vendor-defined.</td>
</tr>
</table>

a. See Section 7.1.2.4.1 for details of header fields common to all MPMs with data on the sideband.

### 7.1.2.5 MPMs without Data

Bits [21:14] in the first DWORD of the MPM header of an MPM without Data message form an 8b
msgcode that denotes a specific MPM without Data message. Table 7-16 lists the supported
msgcodes.

<table>
<caption>Table 7-16. Supported MPM without Data Messages on Sideband</caption>
<tr>
<th>msgcode</th>
<th>Message</th>
</tr>
<tr>
<td>01h</td>
<td>Management Port Gateway Capabilities Message</td>
</tr>
<tr>
<td>02h</td>
<td>Credit Return Message</td>
</tr>
<tr>
<td>03h</td>
<td>Init Done Message</td>
</tr>
<tr>
<td>04h</td>
<td>PM Message</td>
</tr>
<tr>
<td>FFh</td>
<td>Vendor-defined Management Port Gateway Message</td>
</tr>
<tr>
<td>Others</td>
<td>Reserved</td>
</tr>
</table>

### 7.1.2.5.1 Common Header Fields of MPM without Data Messages on Sideband

Figure 7-8 shows and Table 7-17 describes the common fields in the MPM header of MPM without data
messages on the sideband.

<table>
<caption>Figure 7-8. Common Fields in MPM Header of all MPM without Data Messages on Sideband</caption>
<tr>
<th colspan="8">3</th>
<th colspan="8">2</th>
<th colspan="8">1</th>
<th colspan="8">0</th>
</tr>
<tr>
<th>31</th>
<th>30</th>
<th>29</th>
<th>28</th>
<th>27</th>
<th>26</th>
<th>25</th>
<th>24</th>
<th>23</th>
<th>22</th>
<th>21</th>
<th>20</th>
<th>19</th>
<th>18</th>
<th>17</th>
<th>16</th>
<th>15</th>
<th>14</th>
<th>13</th>
<th>12</th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th>11109876543210</th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
</tr>
<tr>
<td colspan="3">$s r c i d = 0 1 1 b$</td>
<td colspan="2"></td>
<td colspan="3">rsvd</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td colspan="3">msgcode</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td colspan="5">msgcode-specific</td>
<td></td>
<td>rs vd</td>
<td></td>
<td colspan="4">opcode = 10111b</td>
</tr>
<tr>
<td>$r s$ vd</td>
<td>cp</td>
<td></td>
<td colspan="2">rsvd</td>
<td colspan="3">$d s t i d = 1 1 1 b$</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td colspan="4"></td>
<td></td>
<td></td>
<td></td>
<td colspan="6">msgcode-specific</td>
<td></td>
<td></td>
<td></td>
<td colspan="2">rsvd</td>
<td colspan="2">msgcode- specific</td>
</tr>
</table>

<table>
<caption>Table 7-17. Common Fields in MPM Header of all MPM without Data Messages on Sideband</caption>
<tr>
<th>Field</th>
<th>Description</th>
</tr>
<tr>
<td>opcode</td>
<td>10111b: MPM without Data.</td>
</tr>
<tr>
<td>msgcode</td>
<td>Message code as defined in Table 7-16.</td>
</tr>
<tr>
<td>srcid</td>
<td>011b: Indicates Management Port Gateway as source.</td>
</tr>
<tr>
<td>cp</td>
<td>Control parity for the sideband packet header. All fields other than "cp" in the header are protected by Control Parity, and the parity scheme is even (including reserved bits).</td>
</tr>
<tr>
<td>dstid</td>
<td>111b: Indicates Management Port Gateway as target.</td>
</tr>
</table>

### 7.1.2.5.2 Management Port Gateway Capabilities Message

See Section 8.2.3.1.2 for usage of this message during sideband management transport path
initialization.

Figure 7-9 shows and Table 7-18 describes the Management Port Gateway Capabilities message
format on the sideband.

<table>
<caption>Figure 7-9. Management Port Gateway Capabilities MPM on Sideband</caption>
<tr>
<th colspan="8">3</th>
<th></th>
<th colspan="7">2</th>
<th></th>
<th colspan="7">1</th>
<th></th>
<th colspan="7">0</th>
</tr>
<tr>
<th>31</th>
<th>30</th>
<th>29</th>
<th>28</th>
<th>27</th>
<th>26</th>
<th>25</th>
<th>24</th>
<th>23</th>
<th>22</th>
<th>21</th>
<th>20</th>
<th>19</th>
<th>18</th>
<th>17</th>
<th>16</th>
<th>15</th>
<th>14</th>
<th>13</th>
<th>12</th>
<th>11</th>
<th>10</th>
<th>9</th>
<th>8</th>
<th>7</th>
<th>6</th>
<th>5</th>
<th>4</th>
<th></th>
<th></th>
<th></th>
<th>3210</th>
</tr>
</table>

a

<table>
<tr>
<th colspan="3">srcid=011b</th>
<th>rsvd</th>
<th>$m s g c o d e = 0 1 h$</th>
<th>NumVC</th>
<th>rsvd $o p c o d e = 1 0 1 1 1 b$</th>
</tr>
<tr>
<td>rs vd</td>
<td>cp</td>
<td>rsvd</td>
<td>$d s t i d = 1 1 1 b$</td>
<td>Port ID[15:0]</td>
<td></td>
<td>rsvd</td>
</tr>
</table>

a. MPM Header.

<table>
<caption>Table 7-18. Management Port Gateway Capabilities MPM Header Fields on Sidebandª</caption>
<tr>
<th>Field</th>
<th>Description</th>
</tr>
<tr>
<td>NumVC</td>
<td>Number of VCs supported by the Management Port Gateway that is transmitting the message.</td>
</tr>
<tr>
<td>Port ID</td>
<td>Port ID number value of the Management port associated with the Management Port Gateway that is issuing the message (see Section 8.1.3.6.2.1).</td>
</tr>
</table>

a. See Table 7-17 for details of header fields common to all MPMs without data on the sideband.

### 7.1.2.5.3 Credit Return Message

See Section 8.2.3.1.2 for usage of this message during sideband management transport path
initialization.

Figure 7-10 shows and Table 7-19 describes the Credit Return message format on the sideband.
If credit returns a and b carry the same vc:resp fields, then the total credit returned for that
rxqid: vc:resp credit type is the sum of cr_ret_a and cr_ret_b.

Figure 7-10. Credit Return MPM on Sideband

a

<table>
<tr>
<th colspan="8">3</th>
<th colspan="8">2</th>
<th colspan="8">1</th>
<th colspan="8">0</th>
</tr>
<tr>
<th>31</th>
<th>30</th>
<th>29</th>
<th>28</th>
<th>27</th>
<th>26</th>
<th>25</th>
<th>24</th>
<th>23</th>
<th>22</th>
<th>21</th>
<th>20</th>
<th>19</th>
<th>18</th>
<th>17</th>
<th>16</th>
<th>15</th>
<th>14</th>
<th>13</th>
<th>12</th>
<th>11</th>
<th>10</th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th>9876543210</th>
</tr>
<tr>
<td colspan="2">srcid=011b</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>rsvd</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td colspan="4">$m s g c o d e = 0 2 h$</td>
<td></td>
<td></td>
<td>cr ret re sp. a</td>
<td colspan="2">cr_ret_vc_a</td>
<td></td>
<td>cr_ ret re sp b</td>
<td></td>
<td>cr_ret_vc_b</td>
<td></td>
<td>rs vd</td>
<td></td>
<td></td>
<td colspan="3">$o p c o d e = 1 0 1 1 1 b$</td>
</tr>
<tr>
<td>rs $v d$</td>
<td>cp</td>
<td></td>
<td colspan="2">rsvd</td>
<td colspan="3">dstid=111b</td>
<td></td>
<td></td>
<td colspan="6">cr_ret_a</td>
<td></td>
<td></td>
<td></td>
<td colspan="2"></td>
<td colspan="5">cr_ret_b</td>
<td></td>
<td></td>
<td colspan="2">rsvd</td>
<td colspan="2">rxqid</td>
</tr>
</table>

a. MPM Header.

<table>
<caption>Table 7-19. Credit Return MPM Header Fields on Sidebandª</caption>
<tr>
<th>Field</th>
<th>Description</th>
</tr>
<tr>
<td>cr_ret_vc_a(b)</td>
<td>VC for which the credit is being returned.</td>
</tr>
<tr>
<td>$c r \_ r e t \_ r e s p \_ a \left( b \right)$</td>
<td>Resp value associated with the credit returned. 0=Request channel credit. 1=Response channel credit.</td>
</tr>
<tr>
<td>$\mathrm { c r } _ { - } \mathrm { r e t } _ { - } \mathrm { a } \left( \mathrm { b } \right)$</td>
<td>Value of credits returned for the RxQ (in the Management Port Gateway transmitting this and the associated VC: Resp channel indicated via $c r \_ r e t \_ v c \_ a \left( b \right) / c r \_ r e t \_ r e s p \_ a \left( b \right) f i e l d s .$ 001h indicates 1 credit returned. 3FEh indicates 1022 credits returned. 3FFh indicates infinite credits. 3FFh value is legal only on credit returns that happen during VC initialization (i.e., before Init Done message is sent) $\mathrm { a n d } \mathrm { c a n n o t }$ be used after initialization until the transport path is renegotiated/initialized again. If a receiver detects infinite credit returns after VC initialization and during runtime, it silently ignores it.</td>
</tr>
<tr>
<td>rxqid</td>
<td>RxQ-ID of the receiver queue for which the credits are being returned (see Section 8.2.3.1.2 for RxQ details).</td>
</tr>
</table>

a. See Table 7-17 for details of header fields common to all MPMs without data on the sideband.

#### 7.1.2.5.4 Init Done Message

See Section 8.2.5.1.4 for usage of this message during sideband management transport path
initialization.

Figure 7-11 shows and Table 7-20 describes the Init Done message format on the sideband.

<table>
<caption>Figure 7-11. Init Done MPM on Sideband</caption>
<tr>
<th colspan="8">3</th>
<th colspan="8">2</th>
<th colspan="8">1</th>
<th></th>
<th colspan="6">0</th>
</tr>
<tr>
<th>31</th>
<th>30</th>
<th>29</th>
<th>28</th>
<th>27</th>
<th>26</th>
<th>25</th>
<th>24</th>
<th>23</th>
<th>22</th>
<th>21</th>
<th>20</th>
<th>19</th>
<th>18</th>
<th>17</th>
<th>16</th>
<th>15</th>
<th>14</th>
<th>13</th>
<th>12</th>
<th>11</th>
<th>10</th>
<th>9</th>
<th>8</th>
<th>7</th>
<th>6</th>
<th>5</th>
<th>4</th>
<th></th>
<th></th>
<th>3210</th>
</tr>
<tr>
<td colspan="3">$\mathrm { s r c i d } = 0 1 1 \mathrm { b }$</td>
<td colspan="5">rsvd</td>
<td></td>
<td></td>
<td></td>
<td colspan="6">$m s g c o d e = 0 3 h$</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td colspan="3">rsvd</td>
<td></td>
<td></td>
<td></td>
<td colspan="4">$o p c o d e = 1 0 1 1 1 b$</td>
</tr>
<tr>
<td>$r s$ vd</td>
<td>cp</td>
<td></td>
<td colspan="2">rsvd</td>
<td colspan="3">$d s t i d = 1 1 1 b$</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td colspan="3"></td>
<td></td>
<td></td>
<td>rsvd</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td colspan="2"></td>
<td colspan="2">rxqid</td>
</tr>
</table>

a

a. MPM Header.

<table>
<caption>Table 7-20. Init Done MPM Header Fields on Sidebandª</caption>
<tr>
<th>Field</th>
<th>Description</th>
</tr>
<tr>
<td>rxqid</td>
<td>RxQ-ID of the receiver queue that has completed initializing credits (see Section 8.2.3.1.2 for RxQ details).</td>
</tr>
</table>

a. See Table 7-17 for details of header fields common to all MPMs without data on the sideband.

#### 7.1.2.5.5 PM Message

See Section 8.2.5.1.4 for usage of this message during sideband management transport PM flows.

Figure 7-12 shows and Table 7-21 describes the PM message format on the sideband.

<table>
<caption>Figure 7-12. PM MPM on Sideband</caption>
<tr>
<th colspan="8">3</th>
<th colspan="8">2</th>
<th colspan="8">1</th>
<th></th>
<th colspan="7">0</th>
</tr>
<tr>
<th>31</th>
<th>30</th>
<th>29</th>
<th>28</th>
<th>27</th>
<th>26</th>
<th>25</th>
<th>24</th>
<th>23</th>
<th>22</th>
<th>21</th>
<th>20</th>
<th>19</th>
<th>18</th>
<th>17</th>
<th>16</th>
<th>15</th>
<th>14</th>
<th>13</th>
<th>12</th>
<th>11</th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th>109876543210</th>
<th></th>
</tr>
</table>

a

<table>
<tr>
<th colspan="3">$s r c i d = 0 1 1 b$</th>
<th>rsvd</th>
<th>$m s g c o d e = 0 4 h$</th>
<th>pmcode</th>
<th colspan="2">rsvd $o p c o d e = 1 0 1 1 1 b$</th>
</tr>
<tr>
<th>$r s$ $v d$</th>
<th>cp</th>
<th>rsvd</th>
<th>dstid=111b</th>
<th></th>
<th>rsvd</th>
<th></th>
<th>rxqid</th>
</tr>
</table>

a. MPM Header.

<table>
<caption>Table 7-21. PM MPM Header Fields on Sidebandª</caption>
<tr>
<th>Field</th>
<th>Description</th>
</tr>
<tr>
<td>pmcode</td>
<td>1h: Wake Req; 2h: Wake ack: 3h; Sleep Req; 4h: Sleep ack; 5h: Sleep nak; Others: Rsvd.</td>
</tr>
<tr>
<td>rxqid</td>
<td>RxQ details). RxQ-ID of the receiver queue to which the message applies (see Section 8.2.3.1.2 for</td>
</tr>
</table>

a. See Table 7-17 for details of header fields common to all MPMs without data on the sideband.

### 7.1.2.5.6 Vendor-defined Management Port Gateway Message

The Vendor-defined Management Port Gateway message without data is defined for custom
communication between the MPGs on both ends of a UCIe sideband link. These messages are not part
of the management transport protocol, and these messages start at an MPG and terminate at the
MPG on the other end of the UCIe sideband link. These messages share the same RxQ-ID request
buffers as encapsulated MTP messages. If an MPG does not support these messages or does not

support these messages from a given vendor (identified by the UCIe Vendor ID in the header), the
MPG silently drops those messages.

The Vendor-defined Management Port Gateway message without data on the sideband has the format
shown in Figure 7-13.

Figure 7-13. Vendor-defined Management Port Gateway MPM without Data on Sideband

a

<table>
<tr>
<th colspan="8">3</th>
<th colspan="8">2</th>
<th colspan="8">1</th>
<th colspan="8">0</th>
</tr>
<tr>
<th>31</th>
<th>30</th>
<th>29</th>
<th>28</th>
<th>27</th>
<th>26</th>
<th>25</th>
<th>24</th>
<th>23</th>
<th>22</th>
<th>21</th>
<th>20</th>
<th>19</th>
<th>18</th>
<th>17</th>
<th>16</th>
<th>15</th>
<th>14</th>
<th>13</th>
<th>12</th>
<th>11</th>
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
<th>109876543210</th>
</tr>
<tr>
<td colspan="2">srcid=011b</td>
<td></td>
<td></td>
<td>rsvd</td>
<td></td>
<td>re sp = 0</td>
<td></td>
<td>VC</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td colspan="3">msgcode = FFh</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td colspan="4">Vendor-defined</td>
<td></td>
<td></td>
<td>rs vd</td>
<td></td>
<td></td>
<td colspan="3">$o p c o d e = 1 0 1 1 1 b$</td>
</tr>
<tr>
<td>$r s$ vd</td>
<td>cp</td>
<td></td>
<td colspan="2">rsvd</td>
<td colspan="3">$d s t i d = 1 1 1 b$</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td colspan="7">UCIe Vendor ID</td>
<td colspan="5"></td>
<td></td>
<td></td>
<td colspan="2">rsvd</td>
<td colspan="2"></td>
<td colspan="2">rxqid</td>
</tr>
</table>

a. MPM Header.

<table>
<caption>Table 7-22. MPM Header Vendor-defined Management Port Gateway Message without Data on Sidebandª</caption>
<tr>
<th>Field</th>
<th>Descriptions</th>
</tr>
<tr>
<td>Vendor-defined</td>
<td>Defined by the vendor specified in the UCIe Vendor ID field.</td>
</tr>
<tr>
<td>VC</td>
<td>Virtual Channel ID.</td>
</tr>
<tr>
<td>resp</td>
<td>Vendor-defined Management Port Gateway message without data always uses the Request channel. The value must be 0.</td>
</tr>
<tr>
<td>UCIe Vendor ID</td>
<td>UCIe Consortium-assigned unique ID for each vendor.</td>
</tr>
<tr>
<td>rxqid</td>
<td>RxQ details). RxQ-ID of the receiver queue to which the message belongs (see Section 8.2.3.1.2 for</td>
</tr>
</table>

a. See Table 7-17 for details of header fields common to all MPMs without data on the sideband.

### 7.1.2.6 Priority Sideband Traffic Packets

See Section 4.1.5.2 for the rules associated with priority sideband traffic packets. Figure 7-14 shows
the packet format. Note that Byte 0[6, 5] must always be 11b for all priority sideband traffic packets
to avoid aliasing with other packet types in case there are single bit errors during transmission. Bit 31
is a Parity (P) bit, calculated by XORing bits 0 through 30 of the priority sideband traffic packet (i.e.,
P = ^ {PSPT[30:0]}, where PSTP is the priority sideband traffic packet).

<table>
<caption>Figure 7-14. Format for Priority Sideband Traffic Packets</caption>
<tr>
<th colspan="20">Priority Sideband Traffic Packet</th>
</tr>
<tr>
<th>Bytes</th>
<th colspan="3">3</th>
<th colspan="2">2</th>
<th colspan="4">1</th>
<th colspan="2"></th>
<th></th>
<th colspan="5">0</th>
<th colspan="2"></th>
</tr>
<tr>
<td>Bits</td>
<td>31</td>
<td>30 29 28 27 26 25</td>
<td>24</td>
<td>23 22 21 20 19</td>
<td>18 17 16</td>
<td>15</td>
<td>14</td>
<td>13 12</td>
<td></td>
<td></td>
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
<td>Header / Data</td>
<td colspan="17">11109876543210 Header</td>
<td colspan="2"></td>
</tr>
<tr>
<td>Phase0</td>
<td>P</td>
<td colspan="2"></td>
<td colspan="4">Payload (LSB is on bit 8)</td>
<td></td>
<td></td>
<td colspan="2"></td>
<td>rsvd</td>
<td>1</td>
<td>1</td>
<td colspan="3">$o p c o d e \left[ 4 : 0 \right]$</td>
<td></td>
<td></td>
</tr>
</table>

### 7.1.3 Flow Control and Data Integrity

Sideband packets can be transferred across FDI, RDI or the UCIe sideband Link. Each of these have
independent flow control.

#### 7.1.3.1 Flow Control and Data Integrity over FDI and RDI

For each Transmitter associated with FDI or RDI, a design time parameter of the interface is used to
determine the number of credits advertised by the Receiver, with a maximum of 32 credits. Each
credit corresponds to 64 bits of header and 64 bits of potentially associated data. Thus, there is only
one type of credit for all sideband packets, regardless of how much data they carry. Every
Transmitter/Receiver pair has an independent credit loop. For example, on RDI, credits are advertised
from Physical Layer to Adapter for sideband packets transmitted from the Adapter to the Physical
Layer; and credits are also advertised from Adapter to the Physical Layer for sideband packets
transmitted from the Physical Layer to the Adapter.

The Transmitter must check for available credits before sending Register Access requests and
Messages. The Transmitter must not check for credits before sending Register Access Completions,
and the Receiver must guarantee unconditional sinking for any Register Access Completion packets.
Messages carrying requests or responses consume a credit on FDI and RDI, but they must be
guaranteed to make forward progress by the Receiver and not get blocked behind Register Access
requests. Both RDI and FDI give a dedicated signal for sideband credit returns across those
interfaces.

All Receivers associated with RDI and FDI must check received messages for data or control parity
errors, and these errors must be mapped to Uncorrectable Internal Errors (UIE) and transition RDI to
LinkError state. All receivers of the Priority Sideband Traffic Packet (PSTP) must check for parity
errors, and these errors must be mapped to Uncorrectable Internal Errors (UIE) and transition RDI to
LinkError state.

When supporting Management Port Messages over sideband, the Physical Layer maintains separate
credited buffers (which is a design time parameter) per RxQ-ID it supports to which it can receive
Management Port Messages from Management Port Gateway over the RDI configuration bus. Whether
received over FDI or RDI, Management Port Messages are always sunk unconditionally in the
Management Port Gateway.

#### 7.1.3.2 Flow Control and Data Integrity over UCIe sideband Link between dies

The BER of the sideband Link is 1e-27 or better. Hence, no retry mechanism is provided for the
sideband packets. Receivers of sideband packets must check for Data or Control parity errors, and
any of these errors is mapped to a fatal UIE.

#### 7.1.3.3 End-to-End flow control and forward progress for UCIe Link sideband

It is important for deadlock avoidance to ensure that there is sufficient space at the Receiver to sink
all possible outstanding requests from the Transmitter, so that the requests do not get blocked at any
intermediate buffers that would thereby prevent subsequent completions from making progress.

Sideband access for Remote Link partner's Adapter or Physical Layer registers is only accessible via
the indirect mailbox mechanism, and the number of outstanding transactions is limited to four at a
time. Although four credits are provisioned, there is only a single mailbox register, and this limits the
number of outstanding requests that can use this mechanism to one at a time. The extra credits allow
additional debug-related register access requests in case of register access timeouts. These credits
are separate from local FDI or RDI accesses, and thus the Physical Layer must provision for sinking at
least one register access request and completion each from remote die and local Adapter in addition
to other sideband request credits (see Implementation Note below). The Adapter provisions for at
least four remote register access requests from remote die Adapter. Each credit corresponds to 64b of
header and 64b of data. Even requests that send no data or only send 32b of data consume one
credit. Register Access completions do not consume a credit and must always sink.

If Management Transport Protocol is not supported, the Adapter credit counters for register access
request are initialized to 4 on Domain Reset exit OR whenever RDI transitions from Reset to Active.

If Management Transport Protocol is supported, the Adapter credit counters for register access
request are initialized to 4 on [Domain Reset exit] OR whenever [RDI transitions from Reset to Active
AND SB_MGMT_UP=0].

It is permitted to send an extra (N-4) credit returns to remote Link partner if a UCIe implementation
is capable of sinking a total of N requests once RDI has transitioned to Active state. The Adapter must
implement a saturating credit counter capable of accumulating at least 4 credits, and hence prevent
excess credit returns from overflowing the counter.

All other messages except Vendor Defined messages must always sink and make forward progress,
and not block any messages on the sideband interface behind them. All Link Management message
requests have an associated response, and the source of these messages must only have one
outstanding request at a time (i.e., one outstanding message per "Link Management Request"
MsgCode encoding). Priority Sideband Traffic Packets (PSTPs) must always be accepted and make
forward progress - there is no flow control check at the Transmitter for them.

For vendor defined messages, there must be a vendor defined cap on the number of outstanding
messages, and the Receiver must guarantee sufficient space so as to not block any messages behind
the vendor defined messages on any of the interfaces.

# IMPLEMENTATION NOTE

Figure 7-15 shows an example of an end-to-end register access request to remote die
and the corresponding completion returning back.

<figure>
<figcaption>Figure 7-15. Example Flow for Remote Register Access Request (Local FDI/RDI Credit Checks Are Not Explicitly Shown)</figcaption>

1a. Mailbox request completed over FDI cfg
as soon as mailbox register is updated.

1\. Mailbox targeted
request over FDI cfg.

10\. Adapter updates mailbox with relevant
information. Status is updated, Read/Write
Trigger is cleared by Adapter HW.

Adapter Die 0

2\. Adapter checks credits
for remote Adapter;
generates remote die request.

9\. Response from remote die over RDI cfg.

3\. Remote die request over RDI cfg.

Physical Layer Die 0

8\. Response for remote die over UCIe sideband.

4\. Remote die request over UCIe sideband.

Physical Layer Die 1

6\. Adapter decoded the request to
local Physical Layer and performs
the transaction using RDI cfg.

7\. Response for remote die over RDI cfg.

5\. Request from remote die over RDI cfg.

Adapter Die 1

</figure>

In Step 1 shown in Figure 7-15, the Protocol Layer checks for FDI credits before
sending the request to Adapter Die 0. Adapter Die 0 completes the mailbox request
as soon as the mailbox register is updated (shown in Step 1a). FDI credits are
returned once its internal buffer space is free. In Step 2, Adapter Die 0 checks credits
for remote Adapter as well as credits for local RDI before sending the remote die
request to Physical Layer Die 0 in Step 3. Physical Layer schedules the request over
UCIe sideband and returns the RDI credit to Adapter Die 0 once it has freed up its
internal buffer space.

