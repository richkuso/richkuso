<figure>

ichUcle®
Universal Chiplet
Interconnect Express

</figure>

# Universal Chiplet Interconnect Express™ (UCIe™)

Specification

August 5, 2025
Revision 3.0, Version 1.0

# LEGAL NOTICE FOR THIS PUBLICLY AVAILABLE SPECIFICATION FROM UNIVERSAL CHIPLET INTERCONNECT EXPRESS, INC.

@ 2022-2025 UNIVERSAL CHIPLET INTERCONNECT EXPRESS, INC. ALL RIGHTS RESERVED.

This Universal Chiplet Interconnect Express, Inc. Specification (this "UCIe Specification" or this "document") is owned by and
is proprietary to Universal Chiplet Interconnect Express, Inc., a Delaware nonprofit corporation (sometimes referred to as "UCIe"
or the "UCIe Consortium" or the "Company") and/or its successors and assigns.

NOTICE TO USERS WHO ARE MEMBERS OF UNIVERSAL CHIPLET INTERCONNECT EXPRESS, INC .:

If you are a Member of Universal Chiplet Interconnect Express, Inc. (herein referred to as a "UCIe Member"), and even if you
have received this publicly available version of this UCIe Specification after agreeing to the UCIE Consortium's Evaluation Copy
Agreement (a copy of which is available at www.uciexpress.org/specifications, each such UCIE Member must also be in
compliance with all of the following UCIe Consortium documents, policies and/or procedures (collectively, the "UCIe Governing
Documents") in order for such UCIe Member's use and/or implementation of this UCIe Specification to receive and enjoy all of
the rights, benefits, privileges and protections of UCIe Consortium membership: (i) the UCIe Consortium's Intellectual Property
Policy; (ii) the UCIe Consortium's Bylaws; (iii) any and all other UCIe Consortium policies and procedures; and (iv) the UCIe
Member's Participation Agreement.

## NOTICE TO NON-MEMBERS OF UNIVERSAL CHIPLET INTERCONNECT EXPRESS, INC .:

If you are not a UCIe Member and have received this publicly available version of this UCIe Specification, your use of this
document is subject to your compliance with, and is limited by, all of the terms and conditions of the UCIe Consortium's
Evaluation Copy Agreement (a copy of which is available at www.uciexpress.org/specifications).

In addition to the restrictions set forth in the UCIe Consortium's Evaluation Copy Agreement, any references or citations to this
document must acknowledge Universal Chiplet Interconnect Express, Inc.'s sole and exclusive copyright ownership of this UCIe
Specification. The proper copyright citation or reference is as follows: "@ 2022-2025 UNIVERSAL CHIPLET INTERCONNECT
EXPRESS, INC. ALL RIGHTS RESERVED." When making any such citation or reference to this document you are not permitted
to revise, alter, modify, make any derivatives of, or otherwise amend the referenced portion of this document in any way without
the prior express written permission of Universal Chiplet Interconnect Express, Inc.

Except for the limited rights explicitly given to a non-UCIe Member pursuant to the explicit provisions of the UCIe Consortium's
Evaluation Copy Agreement which governs the publicly available version of this UCIe Specification, nothing contained in this UCIe
Specification shall be deemed as granting (either expressly or impliedly) to any party that is not a UCIe Member: (i) any kind of
license to implement or use this UCIe Specification or any portion or content described or contained therein, or any kind of license
in or to any other intellectual property owned or controlled by the UCIe Consortium, including without limitation any trademarks
of the UCIe Consortium; or (ii) any benefits and/or rights as a UCIe Member under any UCIe Governing Documents. For clarity,
and without limiting the foregoing notice in any way, if you are not a UCIe Member but still elect to implement this UCIe
Specification or any portion described herein, you are hereby given notice that your election to do so does not give you any of the
rights, benefits, and/or protections of the UCIe Members, including without limitation any of the rights, benefits, privileges or
protections given to a UCIe Member under the UCIe Consortium's Intellectual Property Policy.

## LEGAL DISCLAIMERS AND ADDITIONAL NOTICE TO ALL PARTIES:

THIS DOCUMENT AND ALL SPECIFICATIONS AND/OR OTHER CONTENT PROVIDED HEREIN IS PROVIDED ON AN "AS IS" BASIS.
TO THE MAXIMUM EXTENT PERMITTED BY APPLICABLE LAW, UNIVERSAL CHIPLET INTERCONNECT EXPRESS, INC. (ALONG WITH
THE CONTRIBUTORS TO THIS DOCUMENT) HEREBY DISCLAIM ALL REPRESENTATIONS, WARRANTIES AND/OR COVENANTS,
EITHER EXPRESS OR IMPLIED, STATUTORY OR AT COMMON LAW, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, TITLE, VALIDITY, AND/OR NON-INFRINGEMENT.

In the event this UCIe Specification makes any references (including without limitation any incorporation by reference) to another
standard's setting organization's or any other party's ("Third Party") content or work, including without limitation any
specifications or standards of any such Third Party ("Third Party Specification"), you are hereby notified that your use or
implementation of any Third Party Specification: (i) is not governed by any of the UCIe Governing Documents; (ii) may require
your use of a Third Party's patents, copyrights or other intellectual property rights, which in turn may require you to
independently obtain a license or other consent from that Third Party in order to have full rights to implement or use that Third
Party Specification; and/or (iii) may be governed by the intellectual property policy or other policies or procedures of the Third
Party which owns the Third Party Specification. Any trademarks or service marks of any Third Party which may be referenced in
this UCIe Specification are owned by the respective owner of such marks.

The UCIe™ and UNIVERSAL CHIPLET INTERCONNECT EXPRESS™ trademarks and logos (the "UCIe Trademarks") are
trademarks owned by the UCIe Consortium. The UCIe Consortium reserves all rights in and to all of its UCIe Trademarks.

NOTICE TO ALL PARTIES REGARDING THE PCI-SIG UNIQUE VALUE PROVIDED IN THIS SPECIFICATION:

NOTICE TO USERS: THE UNIQUE VALUE THAT IS PROVIDED IN THIS SPECIFICATION FOR USE IN VENDOR DEFINED MESSAGE
FIELDS, DESIGNATED VENDOR SPECIFIC EXTENDED CAPABILITIES, AND ALTERNATE PROTOCOL NEGOTIATION ONLY AND MAY
NOT BE USED IN ANY OTHER MANNER, AND A USER OF THE UNIQUE VALUE MAY NOT USE THE UNIQUE VALUE IN A MANNER
THAT (A) ALTERS, MODIFIES, HARMS OR DAMAGES THE TECHNICAL FUNCTIONING, SAFETY OR SECURITY OF THE PCI-SIG
ECOSYSTEM OR ANY PORTION THEREOF, OR (B) COULD OR WOULD REASONABLY BE DETERMINED TO ALTER, MODIFY, HARM OR
DAMAGE THE TECHNICAL FUNCTIONING, SAFETY OR SECURITY OF THE PCI-SIG ECOSYSTEM OR ANY PORTION THEREOF (FOR
PURPOSES OF THIS NOTICE, "PCI-SIG ECOSYSTEM" MEANS THE PCI-SIG SPECIFICATIONS, MEMBERS OF PCI-SIG AND THEIR
ASSOCIATED PRODUCTS AND SERVICES THAT INCORPORATE ALL OR A PORTION OF A PCI-SIG SPECIFICATION AND EXTENDS
TO THOSE PRODUCTS AND SERVICES INTERFACING WITH PCI-SIG MEMBER PRODUCTS AND SERVICES).

# Contents

<table>
<tr>
<td colspan="3">Terminology</td>
<td>28</td>
</tr>
<tr>
<td colspan="3">Reference Documents</td>
<td>37</td>
</tr>
<tr>
<td colspan="3">Revision History</td>
<td>37</td>
</tr>
<tr>
<td>1.0</td>
<td colspan="2">Introduction</td>
<td>38</td>
</tr>
<tr>
<td></td>
<td colspan="2">1.1 UCIe Components</td>
<td>42</td>
</tr>
<tr>
<td></td>
<td colspan="2">1.1.1 Protocol Layer</td>
<td>42</td>
</tr>
<tr>
<td></td>
<td></td>
<td>1.1.2 Die-to-Die (D2D) Adapter</td>
<td>43</td>
</tr>
<tr>
<td></td>
<td></td>
<td>1.1.3 Physical Layer</td>
<td>43</td>
</tr>
<tr>
<td></td>
<td></td>
<td>1.1.4 Interfaces</td>
<td>44</td>
</tr>
<tr>
<td></td>
<td colspan="2">1.2 UCIe Configurations</td>
<td>44</td>
</tr>
<tr>
<td></td>
<td colspan="2">1.2.1 Single Module Configuration</td>
<td>44</td>
</tr>
<tr>
<td></td>
<td colspan="2">1.2.2 Multi-module Configurations</td>
<td>45</td>
</tr>
<tr>
<td></td>
<td colspan="2">1.2.3 Sideband-only Configurations</td>
<td>46</td>
</tr>
<tr>
<td></td>
<td colspan="2">1.3 UCIe Retimers</td>
<td>47</td>
</tr>
<tr>
<td></td>
<td colspan="2">1.4 UCIe Key Performance Targets</td>
<td>49</td>
</tr>
<tr>
<td></td>
<td colspan="2">1.5 Interoperability</td>
<td>50</td>
</tr>
<tr>
<td>2.0</td>
<td colspan="2">Protocol Layer</td>
<td>51</td>
</tr>
<tr>
<td></td>
<td>2.1</td>
<td>PCIe</td>
<td>53</td>
</tr>
<tr>
<td></td>
<td colspan="2">2.1.1 Raw Format</td>
<td>53</td>
</tr>
<tr>
<td></td>
<td colspan="2">2.1.2 Standard 256B End Header Flit Format</td>
<td>53</td>
</tr>
<tr>
<td></td>
<td colspan="2">2.1.3 68B Flit Format</td>
<td>53</td>
</tr>
<tr>
<td></td>
<td colspan="2">2.1.4 Standard 256B Start Header Flit Format</td>
<td>53</td>
</tr>
<tr>
<td></td>
<td colspan="2">2.1.5 Latency-Optimized 256B with Optional Bytes Flit Format.</td>
<td>54</td>
</tr>
<tr>
<td></td>
<td colspan="2">2.2 CXL 256B Flit Mode</td>
<td>54</td>
</tr>
<tr>
<td></td>
<td colspan="2">2.2.1 Raw Format</td>
<td>54</td>
</tr>
<tr>
<td colspan="3">2.2.2 Latency-Optimized 256B Flit Formats</td>
<td>54</td>
</tr>
<tr>
<td></td>
<td colspan="2">2.2.3 Standard 256B Start Header Flit Format</td>
<td>55</td>
</tr>
<tr>
<td colspan="3">2.3 CXL 68B Flit Mode</td>
<td>55</td>
</tr>
<tr>
<td></td>
<td colspan="2">2.3.1 Raw Format</td>
<td>55</td>
</tr>
<tr>
<td></td>
<td></td>
<td>2.3.2 68B Flit Format</td>
<td>55</td>
</tr>
<tr>
<td></td>
<td colspan="2">2.4 Streaming Protocol</td>
<td>56</td>
</tr>
<tr>
<td></td>
<td></td>
<td>2.4.1 Raw Format</td>
<td>56</td>
</tr>
<tr>
<td></td>
<td></td>
<td>2.4.2 68B Flit Format</td>
<td>56</td>
</tr>
<tr>
<td></td>
<td colspan="2">2.4.3 Standard 256B Flit Formats</td>
<td>57</td>
</tr>
<tr>
<td></td>
<td colspan="2">2.4.4 Latency-Optimized 256B Flit Formats</td>
<td>57</td>
</tr>
<tr>
<td></td>
<td colspan="2">2.5 Management Transport Protocol</td>
<td>57</td>
</tr>
<tr>
<td>3.0</td>
<td colspan="2">Die-to-Die Adapter</td>
<td>58</td>
</tr>
<tr>
<td></td>
<td colspan="2">3.1 Stack Multiplexing</td>
<td>59</td>
</tr>
<tr>
<td></td>
<td colspan="2">3.2 Link Initialization</td>
<td>62</td>
</tr>
<tr>
<td></td>
<td colspan="2">3.2.1 Stage 3 of Link Initialization: Adapter Initialization</td>
<td>62</td>
</tr>
<tr>
<td></td>
<td colspan="2">3.2.1.1 Part 1: Determine Local Capabilities</td>
<td>62</td>
</tr>
<tr>
<td></td>
<td colspan="2">3.2.1.2 Part 2: Parameter Exchange with Remote Link Partner</td>
<td>63</td>
</tr>
<tr>
<td></td>
<td colspan="2">3.2.1.3 Part 3: FDI bring up</td>
<td>70</td>
</tr>
<tr>
<td></td>
<td colspan="2">3.3 Operation Formats</td>
<td>71</td>
</tr>
<tr>
<td></td>
<td colspan="2">3.3.1 Raw Format for All Protocols</td>
<td>71</td>
</tr>
<tr>
<td></td>
<td colspan="2">3.3.2 68B Flit Format</td>
<td>71</td>
</tr>
<tr>
<td></td>
<td colspan="2">3.3.2.1 68B Flit Format Alignment and Padding Rules</td>
<td>73</td>
</tr>
<tr>
<td></td>
<td colspan="2">3.3.3 Standard 256B Flit Formats</td>
<td>75</td>
</tr>
<tr>
<td></td>
<td></td>
<td>3.3.4 Latency-Optimized 256B Flit Formats</td>
<td>80</td>
</tr>
</table>

## 4.0

<table>
<tr>
<th></th>
<th></th>
<th>Contents</th>
</tr>
<tr>
<td></td>
<td>3.3.5 Flit Format-related Implementation Requirements</td>
<td></td>
</tr>
<tr>
<td></td>
<td>for Protocol Layer and Adapter</td>
<td>84</td>
</tr>
<tr>
<td>3.4</td>
<td>Decision Table for Flit Format and Protocol</td>
<td>85</td>
</tr>
<tr>
<td>3.5</td>
<td>State Machine Hierarchy</td>
<td>89</td>
</tr>
<tr>
<td>3.6</td>
<td>Power Management Link States</td>
<td>90</td>
</tr>
<tr>
<td>3.7</td>
<td>CRC Computation</td>
<td>92</td>
</tr>
<tr>
<td>3.8</td>
<td>Retry Rules</td>
<td>93</td>
</tr>
<tr>
<td>3.9</td>
<td>Runtime Link Testing using Parity</td>
<td>95</td>
</tr>
<tr>
<td colspan="2">Logical Physical Layer</td>
<td>98</td>
</tr>
<tr>
<td>4.1</td>
<td>Data and Sideband Transmission Flow</td>
<td>98</td>
</tr>
<tr>
<td></td>
<td>4.1.1 Byte to Lane Mapping</td>
<td>98</td>
</tr>
<tr>
<td></td>
<td>4.1.2 Valid Framing</td>
<td>100</td>
</tr>
<tr>
<td></td>
<td>4.1.2.1 Valid Framing for Retimers</td>
<td>101</td>
</tr>
<tr>
<td></td>
<td>4.1.3 Clock Gating</td>
<td>101</td>
</tr>
<tr>
<td colspan="2">4.1.4 Free Running Clock Mode</td>
<td>101</td>
</tr>
<tr>
<td></td>
<td>4.1.5 Sideband transmission</td>
<td>102</td>
</tr>
<tr>
<td></td>
<td>4.1.5.1 Sideband Performant Mode Operation (PMO)</td>
<td>102</td>
</tr>
<tr>
<td></td>
<td>4.1.5.2 Priority Sideband Packet Transfer</td>
<td>103</td>
</tr>
<tr>
<td></td>
<td>4.1.5.2.1 PSPT Rules</td>
<td>103</td>
</tr>
<tr>
<td>4.2</td>
<td>Lane Reversal</td>
<td>104</td>
</tr>
<tr>
<td></td>
<td>4.2.1 Lane ID</td>
<td>105</td>
</tr>
<tr>
<td>4.3</td>
<td>Interconnect redundancy remapping</td>
<td>107</td>
</tr>
<tr>
<td></td>
<td>4.3.1 Data Lane repair</td>
<td>107</td>
</tr>
<tr>
<td></td>
<td>4.3.2 Data Lane repair with Lane reversal</td>
<td>109</td>
</tr>
<tr>
<td></td>
<td>4.3.3 Data Lane repair implementation</td>
<td>109</td>
</tr>
<tr>
<td></td>
<td>4.3.3.1 Single Lane repair</td>
<td>109</td>
</tr>
<tr>
<td></td>
<td>4.3.3.2 Two Lane repair</td>
<td>111</td>
</tr>
<tr>
<td></td>
<td>4.3.3.3 Single Lane repair with Lane reversal</td>
<td>113</td>
</tr>
<tr>
<td></td>
<td>4.3.3.3.1 x64 Advanced Package Pseudo Codes</td>
<td>113</td>
</tr>
<tr>
<td></td>
<td>4.3.3.3.2 x32 Advanced Package Pseudo Codes</td>
<td>113</td>
</tr>
<tr>
<td></td>
<td>4.3.3.4 Two Lane repair with Lane reversal</td>
<td>114</td>
</tr>
<tr>
<td></td>
<td>4.3.3.4.1 x64 Advanced Package Pseudo Codes</td>
<td>114</td>
</tr>
<tr>
<td></td>
<td>4.3.3.4.2 x32 Advanced Package Pseudo Codes</td>
<td>115</td>
</tr>
<tr>
<td></td>
<td>4.3.4 Clock and Track Lane remapping</td>
<td>115</td>
</tr>
<tr>
<td></td>
<td>4.3.5 Clock and Track Lane repair implementation</td>
<td>116</td>
</tr>
<tr>
<td></td>
<td>4.3.6 Valid Repair and implementation</td>
<td>118</td>
</tr>
<tr>
<td></td>
<td>4.3.7 Width Degrade in Standard Package Interfaces</td>
<td>118</td>
</tr>
<tr>
<td>4.4</td>
<td>Data to Clock Training and Test Modes</td>
<td>119</td>
</tr>
<tr>
<td></td>
<td>4.4.1 Scrambling and training pattern generation</td>
<td>120</td>
</tr>
<tr>
<td>4.5</td>
<td>Link Initialization and Training</td>
<td>124</td>
</tr>
<tr>
<td></td>
<td>4.5.1 Link Training Basic Operations</td>
<td>125</td>
</tr>
<tr>
<td></td>
<td>4.5.1.1 Transmitter initiated Data to Clock Point Test</td>
<td>125</td>
</tr>
<tr>
<td></td>
<td>4.5.1.2 Transmitter initiated Data to Clock Eye Width Sweep</td>
<td>127</td>
</tr>
<tr>
<td></td>
<td>4.5.1.3 Receiver initiated Data to Clock point test</td>
<td>128</td>
</tr>
<tr>
<td></td>
<td>4.5.1.4 Receiver initiated Data to Clock Eye Width Sweep</td>
<td>129</td>
</tr>
<tr>
<td colspan="2">4.5.2 Link Training with Retimer</td>
<td>130</td>
</tr>
<tr>
<td></td>
<td>4.5.3 Link Training State Machine</td>
<td>131</td>
</tr>
<tr>
<td></td>
<td>4.5.3.1 RESET</td>
<td>132</td>
</tr>
<tr>
<td></td>
<td>4.5.3.2 Sideband Initialization (SBINIT)</td>
<td>133</td>
</tr>
<tr>
<td></td>
<td>4.5.3.3 MBINIT</td>
<td>136</td>
</tr>
<tr>
<td></td>
<td>4.5.3.3.1 MBINIT.PARAM</td>
<td>137</td>
</tr>
<tr>
<td></td>
<td>4.5.3.3.2 MBINIT. CAL</td>
<td>146</td>
</tr>
<tr>
<td></td>
<td>4.5.3.3.3 MBINIT.REPAIRCLK</td>
<td>146</td>
</tr>
<tr>
<td></td>
<td>4.5.3.3.4 MBINIT.REPAIRVAL</td>
<td>149</td>
</tr>
<tr>
<td></td>
<td>4.5.3.3.5 MBINIT.REVERSALMB</td>
<td>151</td>
</tr>
</table>

4.6

4.7

4.7.1

4.7.2

4.8

5.0

5.1

5.1.1

5.1.2

5.2

5.2.1

5.2.2

5.3

5.3.1

5.3.2

5.3.3

5.3.4

5.4

5.4.1

5.4.2

5.4.3

<table>
<tr>
<th></th>
<th>Contents</th>
</tr>
<tr>
<td>4.5.3.3.6 MBINIT.REPAIRMB</td>
<td>153</td>
</tr>
<tr>
<td>4.5.3.4 MBTRAIN</td>
<td>155</td>
</tr>
<tr>
<td>4.5.3.4.1 MBTRAIN.VALVREF</td>
<td>156</td>
</tr>
<tr>
<td>4.5.3.4.2 MBTRAIN.DATAVREF</td>
<td>157</td>
</tr>
<tr>
<td>4.5.3.4.3 MBTRAIN.SPEEDIDLE</td>
<td>158</td>
</tr>
<tr>
<td>4.5.3.4.4 MBTRAIN.TXSELFCAL</td>
<td>158</td>
</tr>
<tr>
<td>4.5.3.4.5 MBTRAIN.RXCLKCAL</td>
<td>158</td>
</tr>
<tr>
<td>4.5.3.4.6 MBTRAIN.VALTRAINCENTER</td>
<td>159</td>
</tr>
<tr>
<td>4.5.3.4.7 MBTRAIN. VALTRAINVREF</td>
<td>160</td>
</tr>
<tr>
<td>4.5.3.4.8 MBTRAIN.DATATRAINCENTER1</td>
<td>161</td>
</tr>
<tr>
<td>4.5.3.4.9 MBTRAIN.DATATRAINVREF</td>
<td>161</td>
</tr>
<tr>
<td>4.5.3.4.10 MBTRAIN.RXDESKEW</td>
<td>162</td>
</tr>
<tr>
<td>4.5.3.4.11 MBTRAIN.DATATRAINCENTER2</td>
<td>164</td>
</tr>
<tr>
<td>4.5.3.4.12 MBTRAIN.LINKSPEED</td>
<td>164</td>
</tr>
<tr>
<td>$4 . 5 . 3 . 4 . 1 3$ MBTRAIN.REPAIR</td>
<td>167</td>
</tr>
<tr>
<td>4.5.3.5 LINKINIT</td>
<td>168</td>
</tr>
<tr>
<td>4.5.3.6 ACTIVE</td>
<td>168</td>
</tr>
<tr>
<td>4.5.3.7 PHYRETRAIN</td>
<td>168</td>
</tr>
<tr>
<td>4.5.3.7.1 Adapter initiated PHY retrain</td>
<td>170</td>
</tr>
<tr>
<td>4.5.3.7.2 PHY initiated PHY retrain</td>
<td>170</td>
</tr>
<tr>
<td>4.5.3.7.3 Remote Die requested PHY retrain</td>
<td>171</td>
</tr>
<tr>
<td>4.5.3.7.4 PHY retrain from LINKSPEED</td>
<td>171</td>
</tr>
<tr>
<td>4.5.3.8 TRAINERROR</td>
<td>171</td>
</tr>
<tr>
<td>4.5.3.9</td>
<td>172</td>
</tr>
<tr>
<td>$\begin{array}{} { L 1 / L 2 } \\ { 4 . 5 . 3 . 9 . 1 } \end{array}$ Powering down Sideband in L2 State</td>
<td>172</td>
</tr>
<tr>
<td>Runtime Recalibration</td>
<td>173</td>
</tr>
<tr>
<td>Multi-module Link</td>
<td>175</td>
</tr>
<tr>
<td>Multi-module initialization</td>
<td>175</td>
</tr>
<tr>
<td>4.7.1.1 Sideband Assignment and Retimer Credits for Multi-module</td>
<td></td>
</tr>
<tr>
<td>Configurations</td>
<td>178</td>
</tr>
<tr>
<td>4.7.1.2 Examples of MMPL Synchronization</td>
<td>178</td>
</tr>
<tr>
<td>4.7.1.2.1 Example 1: MMPL Resolution results</td>
<td></td>
</tr>
<tr>
<td>in a Width Degrade per Module</td>
<td>179</td>
</tr>
<tr>
<td>$4 . 7 . 1 . 2 . 2$ Example 2: MMPL Resolution results</td>
<td></td>
</tr>
<tr>
<td>in a Speed Degrade</td>
<td>180</td>
</tr>
<tr>
<td>4.7.1.2.3 Example 3: MMPL Resolution results</td>
<td></td>
</tr>
<tr>
<td>in a Module Disable</td>
<td>180</td>
</tr>
<tr>
<td>Multi-module Interoperability between x64 and x32 Advanced Packages</td>
<td>181</td>
</tr>
<tr>
<td>Sideband PHY Arbitration between MPMs and Link Management Packets</td>
<td>182</td>
</tr>
<tr>
<td>Electrical Layer (2D and 2.5D)</td>
<td>184</td>
</tr>
<tr>
<td>Interoperability</td>
<td>184</td>
</tr>
<tr>
<td>Data rates</td>
<td>184</td>
</tr>
<tr>
<td>Reference Clock (REFCLK)</td>
<td>185</td>
</tr>
<tr>
<td>Overview</td>
<td>186</td>
</tr>
<tr>
<td>Interface Overview</td>
<td>186</td>
</tr>
<tr>
<td>Electrical Summary</td>
<td>188</td>
</tr>
<tr>
<td>Transmitter Specification</td>
<td>190</td>
</tr>
<tr>
<td>Driver Topology</td>
<td>191</td>
</tr>
<tr>
<td>Transmitter Electrical parameters</td>
<td>191</td>
</tr>
<tr>
<td>24 GT/s and 32 GT/s Transmitter Equalization</td>
<td>193</td>
</tr>
<tr>
<td>48 GT/s and 64 GT/s Transmitter Equalization</td>
<td>194</td>
</tr>
<tr>
<td>Receiver Specification</td>
<td>195</td>
</tr>
<tr>
<td>Receiver Electrical Parameters for &lt;= 32 GT/s</td>
<td>196</td>
</tr>
<tr>
<td>Receiver Electrical Parameters for 48 GT/s and 64 GT/s</td>
<td>197</td>
</tr>
<tr>
<td>Rx Termination</td>
<td>197</td>
</tr>
</table>

<table>
<tr>
<th></th>
<th></th>
<th>Contents</th>
</tr>
<tr>
<td></td>
<td>5.4.4 Receiver Equalization &gt; 16 GT/s</td>
<td>200</td>
</tr>
<tr>
<td>5.5</td>
<td>Clocking</td>
<td>201</td>
</tr>
<tr>
<td></td>
<td>5.5.1 Track</td>
<td>202</td>
</tr>
<tr>
<td>5.6</td>
<td>Supply noise and clock skew</td>
<td>205</td>
</tr>
<tr>
<td>5.7</td>
<td>Ball-out and Channel Specification</td>
<td>205</td>
</tr>
<tr>
<td></td>
<td>5.7.1 Voltage Transfer Function</td>
<td>208</td>
</tr>
<tr>
<td></td>
<td>5.7.2 Advanced Package</td>
<td>209</td>
</tr>
<tr>
<td></td>
<td>5.7.2.1 Loss and Crosstalk Mask</td>
<td>210</td>
</tr>
<tr>
<td></td>
<td>5.7.2.2 x64 Advanced Package Module Bump Map</td>
<td>211</td>
</tr>
<tr>
<td></td>
<td>5.7.2.2.1 x64 Advanced Package Module Bump Map</td>
<td></td>
</tr>
<tr>
<td></td>
<td>for 48 GT/s and 64 GT/s</td>
<td>219</td>
</tr>
<tr>
<td></td>
<td>5.7.2.3 x32 Advanced Package Module Bump Map</td>
<td>221</td>
</tr>
<tr>
<td></td>
<td>5.7.2.4 x64 and x32 Advanced Package Module Interoperability</td>
<td>228</td>
</tr>
<tr>
<td></td>
<td>5.7.2.5 Module Naming of Advanced Package Modules</td>
<td>231</td>
</tr>
<tr>
<td></td>
<td>5.7.3 Standard Package</td>
<td>235</td>
</tr>
<tr>
<td></td>
<td>5.7.3.1 x16 Standard Package Module Bump Map</td>
<td>236</td>
</tr>
<tr>
<td></td>
<td>5.7.3.2 x8 Standard Package Module Bump Map</td>
<td>240</td>
</tr>
<tr>
<td></td>
<td>5.7.3.3 x16 and x8 Standard Package Module Interoperability</td>
<td>241</td>
</tr>
<tr>
<td></td>
<td>5.7.3.4 Module Naming of Standard Package Modules</td>
<td>241</td>
</tr>
<tr>
<td></td>
<td>5.7.3.4.1 Module Degrade Rules</td>
<td>246</td>
</tr>
<tr>
<td></td>
<td>5.7.4 UCIe-S Sideband-only Port</td>
<td>248</td>
</tr>
<tr>
<td>5.8</td>
<td>Tightly Coupled Mode</td>
<td>249</td>
</tr>
<tr>
<td>5.9</td>
<td>Interconnect redundancy Remapping</td>
<td>249</td>
</tr>
<tr>
<td></td>
<td>5.9.1 Advanced Package Lane Remapping</td>
<td>249</td>
</tr>
<tr>
<td></td>
<td>5.9.2 Standard Package Lane remapping</td>
<td>250</td>
</tr>
<tr>
<td>5.10</td>
<td>BER Requirements, CRC, and Retry</td>
<td>250</td>
</tr>
<tr>
<td>5.11</td>
<td>Valid and Clock Gating</td>
<td>251</td>
</tr>
<tr>
<td>5.12</td>
<td>Electrical Idle</td>
<td>253</td>
</tr>
<tr>
<td>5.13</td>
<td>Sideband signaling</td>
<td>254</td>
</tr>
<tr>
<td></td>
<td>5.13.1 Sideband Electrical Parameters</td>
<td>254</td>
</tr>
<tr>
<td></td>
<td>5.13.2 Auxiliary Clock (AUXCLK)</td>
<td>255</td>
</tr>
<tr>
<td>5.14</td>
<td>Open Drain</td>
<td>255</td>
</tr>
<tr>
<td></td>
<td>5.14.1 Open Drain Usage</td>
<td>256</td>
</tr>
<tr>
<td></td>
<td>5.14.2 External Open Drain Connections</td>
<td>257</td>
</tr>
<tr>
<td colspan="2">UCIe-3D</td>
<td>258</td>
</tr>
<tr>
<td>6.1</td>
<td>Introduction</td>
<td>258</td>
</tr>
<tr>
<td>6.2</td>
<td>UCIe-3D Features and Summary</td>
<td>258</td>
</tr>
<tr>
<td>6.3</td>
<td>UCIe-3D Tx, $R x _ { 1 } ,$ and Clocking</td>
<td>260</td>
</tr>
<tr>
<td>6.4</td>
<td>Electrical Specification</td>
<td>261</td>
</tr>
<tr>
<td></td>
<td>6.4.1 Timing Budget</td>
<td>261</td>
</tr>
<tr>
<td></td>
<td>6.4.2 ESD and Energy Efficiency</td>
<td>263</td>
</tr>
<tr>
<td></td>
<td>6.4.3 UCIe-3D Module and Bump Map</td>
<td>264</td>
</tr>
<tr>
<td></td>
<td>6.4.4 Repair Strategy</td>
<td>265</td>
</tr>
<tr>
<td></td>
<td>6.4.5 Channel and Data Rate Extension</td>
<td>267</td>
</tr>
<tr>
<td colspan="2">Sideband</td>
<td>268</td>
</tr>
<tr>
<td>7.1</td>
<td>Protocol Specification</td>
<td>268</td>
</tr>
<tr>
<td></td>
<td>7.1.1 Sideband Packet Types</td>
<td>269</td>
</tr>
<tr>
<td></td>
<td>7.1.2 Sideband Packet Formats</td>
<td>272</td>
</tr>
<tr>
<td></td>
<td>7.1.2.1 Register Access Packets</td>
<td>272</td>
</tr>
<tr>
<td></td>
<td>7.1.2.2 Messages without Data</td>
<td>275</td>
</tr>
<tr>
<td></td>
<td>7.1.2.3 Messages with data payloads</td>
<td>282</td>
</tr>
<tr>
<td></td>
<td>7.1.2.4 Management Port Message (MPM) with Data</td>
<td>291</td>
</tr>
<tr>
<td></td>
<td>7.1.2.4.1 Common Fields in MPM Header of MPM</td>
<td></td>
</tr>
<tr>
<td></td>
<td>with Data Messages on Sideband</td>
<td>291</td>
</tr>
<tr>
<td></td>
<td>7.1.2.4.2 Encapsulated MTP Message</td>
<td>292</td>
</tr>
<tr>
<td>UCIe Specification</td>
<td>Revision 3.0, Version 1.0</td>
<td>6</td>
</tr>
<tr>
<td>August 5, 2025</td>
<td>Property of Universal Chiplet Interconnect Express (UCIe) @ 2022-2025</td>
<td></td>
</tr>
</table>

## 6.0

7.0

7.1.2.5

7.1.2.6

7.1.3

7.1.3.1

7.1.3.2

7.1.3.3

### 7.1.4

## 8.0 System Architecture

### 8.1 UCIe Manageability

8.1.1
Overview

8.1.2

8.1.3

8.1.3.1

8.1.3.2

8.1.3.3

8.1.3.4

8.1.3.5

8.1.3.6

8.1.4

8.1.4.1

8.1.4.2

8.1.5

8.1.5.1

<table>
<tr>
<th colspan="2">7.1.2.4.3</th>
<th>Vendor-defined Management Port</th>
<th></th>
</tr>
<tr>
<th colspan="2"></th>
<th>Gateway Message</th>
<th>293</th>
</tr>
<tr>
<td colspan="3">MPMs without Data</td>
<td>293</td>
</tr>
<tr>
<td colspan="2">7.1.2.5.1</td>
<td>Common Header Fields of MPM</td>
<td></td>
</tr>
<tr>
<td colspan="2"></td>
<td>without Data Messages on Sideband</td>
<td>294</td>
</tr>
<tr>
<td colspan="2">7.1.2.5.2</td>
<td>Management Port Gateway Capabilities Message</td>
<td>294</td>
</tr>
<tr>
<td colspan="2">7.1.2.5.3</td>
<td>Credit Return Message</td>
<td>295</td>
</tr>
<tr>
<td colspan="2">7.1.2.5.4</td>
<td>Init Done Message</td>
<td>296</td>
</tr>
<tr>
<td colspan="2">7.1.2.5.5</td>
<td>PM Message</td>
<td>296</td>
</tr>
<tr>
<td colspan="2">7.1.2.5.6</td>
<td>Vendor-defined Management Port</td>
<td></td>
</tr>
<tr>
<td colspan="2"></td>
<td>Gateway Message</td>
<td>296</td>
</tr>
<tr>
<td colspan="3">Priority Sideband Traffic Packets</td>
<td>297</td>
</tr>
<tr>
<td colspan="3">Flow Control and Data Integrity</td>
<td>297</td>
</tr>
<tr>
<td colspan="2">Flow Control</td>
<td>and Data Integrity over FDI and RDI</td>
<td>298</td>
</tr>
<tr>
<td colspan="3">Flow Control and Data Integrity over</td>
<td></td>
</tr>
<tr>
<td colspan="2">UCIe sideband</td>
<td>Link between dies</td>
<td>298</td>
</tr>
<tr>
<td colspan="3">End-to-End flow control and forward progress</td>
<td rowspan="2">298</td>
</tr>
<tr>
<td colspan="3">for UCIe Link sideband</td>
</tr>
<tr>
<td colspan="2">Operation on RDI and</td>
<td>FDI</td>
<td>302</td>
</tr>
<tr>
<td colspan="2"></td>
<td></td>
<td>303</td>
</tr>
<tr>
<td colspan="2"></td>
<td></td>
<td>303</td>
</tr>
<tr>
<td colspan="2"></td>
<td></td>
<td>303</td>
</tr>
<tr>
<td colspan="2">Theory of Operation</td>
<td></td>
<td>304</td>
</tr>
<tr>
<td colspan="3">UCIe Management Transport</td>
<td>307</td>
</tr>
<tr>
<td colspan="3">UCIe Management Transport Packet</td>
<td>307</td>
</tr>
<tr>
<td colspan="2">8.1.3.1.1</td>
<td>Traffic Class and Packet Ordering Requirements</td>
<td>309</td>
</tr>
<tr>
<td colspan="2">8.1.3.1.2</td>
<td>Packet Length</td>
<td>311</td>
</tr>
<tr>
<td colspan="2">8.1.3.1.3</td>
<td>Management Protocol</td>
<td>311</td>
</tr>
<tr>
<td></td>
<td colspan="2">Management Network ID</td>
<td>312</td>
</tr>
<tr>
<td colspan="2">Routing</td>
<td></td>
<td>313</td>
</tr>
<tr>
<td colspan="2">8.1.3.3.1</td>
<td rowspan="2">Routing of a Packet from a Management Entity within the Chiplet</td>
<td rowspan="2">313</td>
</tr>
<tr>
<td colspan="2"></td>
</tr>
<tr>
<td colspan="2">8.1.3.3.2</td>
<td>Routing of a Packet Received on a Management Port</td>
<td>315</td>
</tr>
<tr>
<td></td>
<td colspan="2">Packet Integrity Protection</td>
<td>315</td>
</tr>
<tr>
<td colspan="2">8.1.3.4.1</td>
<td>CRC Integrity Protection</td>
<td>315</td>
</tr>
<tr>
<td colspan="3">Access Control</td>
<td>316</td>
</tr>
<tr>
<td colspan="2">8.1.3.5.1</td>
<td>Standard Asset Classes</td>
<td>318</td>
</tr>
<tr>
<td colspan="2">8.1.3.5.2</td>
<td>Security Director</td>
<td>320</td>
</tr>
<tr>
<td colspan="2">Initialization</td>
<td>and Configuration</td>
<td>320</td>
</tr>
<tr>
<td colspan="2">8.1.3.6.1</td>
<td>Management Capability Directory</td>
<td>323</td>
</tr>
<tr>
<td colspan="2">8.1.3.6.2</td>
<td>Chiplet Capability Structure</td>
<td>325</td>
</tr>
<tr>
<td colspan="2">8.1.3.6.3</td>
<td>Access Control Capability Structure</td>
<td>334</td>
</tr>
<tr>
<td colspan="2">8.1.3.6.4</td>
<td>Security Clearance Group Capability Structure</td>
<td>340</td>
</tr>
<tr>
<td colspan="3">UCIe Memory Access Protocol</td>
<td>341</td>
</tr>
<tr>
<td></td>
<td colspan="2">UCIe Memory Access Protocol Packets</td>
<td>342</td>
</tr>
<tr>
<td colspan="2">8.1.4.1.1</td>
<td>UCIe Memory Request Packet</td>
<td>342</td>
</tr>
<tr>
<td colspan="2">8.1.4.1.2</td>
<td>UCIe Memory Access Response Packet</td>
<td>344</td>
</tr>
<tr>
<td colspan="2">UCIe Memory</td>
<td>Access Protocol Capability Structure</td>
<td>346</td>
</tr>
<tr>
<td colspan="3">Common Data Structures</td>
<td>349</td>
</tr>
<tr>
<td colspan="3">Circular Buffer</td>
<td>349</td>
</tr>
<tr>
<td colspan="2">8.1.5.1.1</td>
<td>Circular Buffer Theory of Operation</td>
<td>349</td>
</tr>
<tr>
<td colspan="2">8.1.5.1.2</td>
<td>Circular Buffer State Machine</td>
<td>350</td>
</tr>
<tr>
<td colspan="2">8.1.5.1.3</td>
<td>Circular Buffer Initialization</td>
<td>352</td>
</tr>
<tr>
<td colspan="2">8.1.5.1.4</td>
<td>Circular Buffer Features</td>
<td>352</td>
</tr>
</table>

#### 8.1.6

8.1.6.1

8.2

8.2.1

8.2.2
$8 . 2 . 2 . 1$

8.2.3

8.2.3.1

8.2.3.2

8.2.4

8.2.4.1

8.2.4.2

8.2.4.3

8.2.5
8.2.4.4

8.2.5.1

8.2.5.2

<table>
<tr>
<th></th>
<th></th>
<th>Contents</th>
</tr>
<tr>
<td>8.1.5.1.5</td>
<td>Circular Buffer State and Errors</td>
<td>352</td>
</tr>
<tr>
<td>8.1.5.1.6</td>
<td>Control Register</td>
<td>355</td>
</tr>
<tr>
<td>8.1.5.1.7</td>
<td>Circular Buffer Common Fields</td>
<td>355</td>
</tr>
<tr>
<td>8.1.5.1.8</td>
<td>Sink Circular Buffer Structure</td>
<td>356</td>
</tr>
<tr>
<td>8.1.5.1.9</td>
<td>Source Circular Buffer Structure</td>
<td>358</td>
</tr>
<tr>
<td>8.1.5.1.10</td>
<td>UMAP Requester Coordination</td>
<td>359</td>
</tr>
<tr>
<td>8.1.5.1.11</td>
<td>How to Use Circular Buffer</td>
<td>359</td>
</tr>
<tr>
<td colspan="2">Open Drain Configuration Structure</td>
<td>359</td>
</tr>
<tr>
<td>Example</td>
<td>Usage</td>
<td>360</td>
</tr>
<tr>
<td colspan="2">Management Transport Packet (MTP) Encapsulation</td>
<td>361</td>
</tr>
<tr>
<td colspan="2">MTP Encapsulation Architecture Overview</td>
<td>361</td>
</tr>
<tr>
<td colspan="2">Management Port Messages</td>
<td>365</td>
</tr>
<tr>
<td>Sideband</td>
<td></td>
<td>365</td>
</tr>
<tr>
<td>Mainband</td>
<td></td>
<td>366</td>
</tr>
<tr>
<td>8.2.2.2.1</td>
<td>MPMs with Data</td>
<td>366</td>
</tr>
<tr>
<td>8.2.2.2.2</td>
<td>MPMs without Data</td>
<td>368</td>
</tr>
<tr>
<td colspan="2">Management Transport Path Setup</td>
<td>371</td>
</tr>
<tr>
<td>Sideband</td>
<td></td>
<td>371</td>
</tr>
<tr>
<td>8.2.3.1.1</td>
<td>Negotiation Phase Steps</td>
<td>371</td>
</tr>
<tr>
<td>8.2.3.1.2</td>
<td>Initialization Phase Steps</td>
<td>371</td>
</tr>
<tr>
<td>8.2.3.1.3</td>
<td>Other Sideband Management Transport</td>
<td></td>
</tr>
<tr>
<td></td>
<td>Path Rules</td>
<td>375</td>
</tr>
<tr>
<td>Mainband</td>
<td></td>
<td>375</td>
</tr>
<tr>
<td>8.2.3.2.1</td>
<td>Negotiation Phase Steps</td>
<td>375</td>
</tr>
<tr>
<td>8.2.3.2.2</td>
<td>Initialization Phase Steps</td>
<td>375</td>
</tr>
<tr>
<td>8.2.3.2.3</td>
<td>Other Mainband Management Transport</td>
<td></td>
</tr>
<tr>
<td></td>
<td>Path Rules</td>
<td>377</td>
</tr>
<tr>
<td colspan="2">Common Rules for Management Transport</td>
<td></td>
</tr>
<tr>
<td colspan="2">over Sideband and Mainband</td>
<td>378</td>
</tr>
<tr>
<td>Management</td>
<td>Packet Flow Control</td>
<td>378</td>
</tr>
<tr>
<td>Segmentation</td>
<td></td>
<td>379</td>
</tr>
<tr>
<td colspan="2">Interleaving and Multi-module Sideband</td>
<td></td>
</tr>
<tr>
<td colspan="2">and Multi-stack Mainband Ordering</td>
<td>380</td>
</tr>
<tr>
<td>8.2.4.3.1</td>
<td>Transmitter Rules</td>
<td>380</td>
</tr>
<tr>
<td>8.2.4.3.2</td>
<td>Receiver Rules</td>
<td>381</td>
</tr>
<tr>
<td>`Init Done'</td>
<td>Timeout Flow</td>
<td>383</td>
</tr>
<tr>
<td colspan="2">Other Management Transport Details</td>
<td>383</td>
</tr>
<tr>
<td>Sideband</td>
<td></td>
<td>383</td>
</tr>
<tr>
<td>8.2.5.1.1</td>
<td>Management Port Gateway Flow Control over</td>
<td>RDI 383</td>
</tr>
<tr>
<td>8.2.5.1.2</td>
<td>MPMs with Data Length Rules</td>
<td>383</td>
</tr>
<tr>
<td>8.2.5.1.3</td>
<td>Sideband Runtime Management Transport Path</td>
<td></td>
</tr>
<tr>
<td></td>
<td>Monitoring - Heartbeat Mechanism</td>
<td>384</td>
</tr>
<tr>
<td>8.2.5.1.4</td>
<td>Sideband Management Path Power</td>
<td></td>
</tr>
<tr>
<td></td>
<td>Management Rules</td>
<td>385</td>
</tr>
<tr>
<td>8.2.5.1.5</td>
<td>Management Port Gateway Mux Arbitration</td>
<td>386</td>
</tr>
<tr>
<td>Mainband</td>
<td></td>
<td>386</td>
</tr>
<tr>
<td>8.2.5.2.1</td>
<td>NOP Message</td>
<td>386</td>
</tr>
<tr>
<td>8.2.5.2.2</td>
<td>Credit Return DWORD Format</td>
<td>386</td>
</tr>
<tr>
<td>8.2.5.2.3</td>
<td>Management Flit Formats</td>
<td>387</td>
</tr>
<tr>
<td>8.2.5.2.4</td>
<td>L1/L2 Link States and Management Transport</td>
<td>390</td>
</tr>
<tr>
<td>8.2.5.2.5</td>
<td>Link Reset/Link Disable and</td>
<td></td>
</tr>
<tr>
<td></td>
<td>Management Transport</td>
<td>390</td>
</tr>
<tr>
<td>Retimers and Management</td>
<td>Transport</td>
<td>391</td>
</tr>
</table>

### 8.2.6

### 8.3

8.3.1

8.3.2

8.3.3

8.3.4

8.3.5

<table>
<tr>
<th colspan="3">UCIe Debug and Test Architecture (UDA)</th>
<th>391</th>
</tr>
<tr>
<td>Overview</td>
<td></td>
<td></td>
<td>391</td>
</tr>
<tr>
<td>8.3.1.1</td>
<td>DFx Management</td>
<td>Hub (DMH)</td>
<td>392</td>
</tr>
<tr>
<td>8.3.1.2</td>
<td colspan="2">DFx Management Spoke (DMS)</td>
<td>392</td>
</tr>
<tr>
<td>8.3.1.3</td>
<td colspan="2">Supported Protocols</td>
<td>393</td>
</tr>
<tr>
<td></td>
<td>8.3.1.3.1</td>
<td>UCIe Memory Access Protocol (UMAP)</td>
<td>393</td>
</tr>
<tr>
<td></td>
<td>8.3.1.3.2</td>
<td>Vendor-defined Test and Debug Protocol</td>
<td>393</td>
</tr>
<tr>
<td>8.3.1.4</td>
<td colspan="2">UDM and UCIe Memory Access Protocol Message</td>
<td></td>
</tr>
<tr>
<td></td>
<td colspan="2">Encapsulation over UCIe</td>
<td>394</td>
</tr>
<tr>
<td>8.3.1.5</td>
<td colspan="2">UCIe Test Port Options and Other Considerations</td>
<td>394</td>
</tr>
<tr>
<td></td>
<td>8.3.1.5.1</td>
<td>Determinism Considerations</td>
<td>394</td>
</tr>
<tr>
<td>8.3.1.6</td>
<td>DFx Security</td>
<td></td>
<td>394</td>
</tr>
<tr>
<td colspan="3">Sort/Pre-bond Chiplet Testing with UDA</td>
<td>395</td>
</tr>
<tr>
<td>SiP-level</td>
<td>Chiplet Testing</td>
<td>with UDA</td>
<td>396</td>
</tr>
<tr>
<td colspan="2">System Debug with</td>
<td>UDA</td>
<td>397</td>
</tr>
<tr>
<td>DMH/DMS</td>
<td>Registers</td>
<td></td>
<td>397</td>
</tr>
<tr>
<td></td>
<td>DMH/DMS</td>
<td>Register Address Space and Access Mechanism</td>
<td>397</td>
</tr>
<tr>
<td>$\begin{array}{} { 8 . 3 . 5 . 1 } \\ { 8 . 3 . 5 . 2 } \end{array}$</td>
<td colspan="2">DMH Registers</td>
<td>398</td>
</tr>
<tr>
<td></td>
<td>8.3.5.2.1</td>
<td>Ver (Offset 00h)</td>
<td>399</td>
</tr>
<tr>
<td></td>
<td>8.3.5.2.2</td>
<td>Capability ID (Offset 02h)</td>
<td>399</td>
</tr>
<tr>
<td></td>
<td>8.3.5.2.3</td>
<td>DBG_CAP - Debug Capabilities (Offset 04h)</td>
<td>400</td>
</tr>
<tr>
<td></td>
<td>8.3.5.2.4</td>
<td>DBG_CTL - Debug Control (Offset 08h)</td>
<td>400</td>
</tr>
<tr>
<td></td>
<td>8.3.5.2.5</td>
<td>DBG_STS - Debug Status (Offset Ah)</td>
<td>400</td>
</tr>
<tr>
<td></td>
<td>8.3.5.2.6</td>
<td>DMH_Length_Low - DMH Register Space</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>Length Low (Offset 10h)</td>
<td>400</td>
</tr>
<tr>
<td></td>
<td>8.3.5.2.7</td>
<td>DMH_Length_High - DMH Register Space</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>Length High (Offset 14h)</td>
<td>400</td>
</tr>
<tr>
<td></td>
<td>8.3.5.2.8</td>
<td>DMH_Ext_Cap_Low - DMH Extended Capability</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>Pointer Low (Offset 18h)</td>
<td>401</td>
</tr>
<tr>
<td></td>
<td>8.3.5.2.9</td>
<td>DMH_Ext_Cap_High - DMH Extended Capability</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>Pointer High</td>
<td>401</td>
</tr>
<tr>
<td></td>
<td>8.3.5.2.10</td>
<td>DMS_Start_Low $- \quad D M S$ Starting Address</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>Low (Offset 20h)</td>
<td>401</td>
</tr>
<tr>
<td></td>
<td>8.3.5.2.11</td>
<td>DMS_Start_High - DMS Starting Address</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>High (Offset 24h)</td>
<td>401</td>
</tr>
<tr>
<td>8.3.5.3</td>
<td colspan="2">DMS Registers</td>
<td>401</td>
</tr>
<tr>
<td></td>
<td>8.3.5.3.1</td>
<td>"Empty" Spoke Registers</td>
<td>402</td>
</tr>
<tr>
<td></td>
<td>8.3.5.3.2</td>
<td>Common DMS Registers for</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>All Non-empty Spokes</td>
<td>402</td>
</tr>
<tr>
<td></td>
<td>8.3.5.3.3</td>
<td>DMS Registers of UCIe Spoke Types</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>('Spoke Type' = 0 through 2)</td>
<td>407</td>
</tr>
<tr>
<td></td>
<td>8.3.5.3.4</td>
<td>DMS Registers of Vendor-defined Spoke Types</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>('Spoke Type' = 128 through 255)</td>
<td>411</td>
</tr>
<tr>
<td></td>
<td>8.3.5.3.5</td>
<td>DMS Register Implementation in UCIe Adapter</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>and in UCIe Physical Layer</td>
<td>412</td>
</tr>
<tr>
<td colspan="2">Management Capabilities</td>
<td></td>
<td>412</td>
</tr>
<tr>
<td colspan="2">Early Firmware Download</td>
<td></td>
<td>412</td>
</tr>
<tr>
<td>8.4.1.1</td>
<td colspan="2">Early Firmware Download Guidelines</td>
<td>412</td>
</tr>
<tr>
<td>8.4.1.2</td>
<td colspan="2">Early Firmware Download Capability</td>
<td>413</td>
</tr>
<tr>
<td>8.4.1.3</td>
<td>Early Firmware</td>
<td>Download Asset Class ID</td>
<td>414</td>
</tr>
<tr>
<td>8.4.1.4</td>
<td>Early Firmware</td>
<td>Download Initialization</td>
<td>415</td>
</tr>
<tr>
<td>8.4.1.5</td>
<td>Early Firmware</td>
<td>Download States and Error</td>
<td>415</td>
</tr>
<tr>
<td>8.4.1.6</td>
<td>Early Firmware</td>
<td>Download Capabilities</td>
<td>416</td>
</tr>
<tr>
<td>8.4.1.7</td>
<td colspan="2">Early Firmware Download Control</td>
<td>417</td>
</tr>
<tr>
<td>8.4.1.8</td>
<td colspan="2">Early Firmware Download Flow</td>
<td>417</td>
</tr>
<tr>
<td>8.4.1.9</td>
<td colspan="2">Circular Buffer Requirements for Early Firmware Download</td>
<td>418</td>
</tr>
</table>

8.4

8.4.1

8.4.2

9.0

9.1

9.2

9.3

9.4

9.5

9.5.1

9.5.2

9.5.3

<table>
<tr>
<td colspan="2">Power</td>
<td>Management</td>
<td>418</td>
</tr>
<tr>
<td colspan="2">8.4.2.1</td>
<td>Fast Throttle</td>
<td>418</td>
</tr>
<tr>
<td colspan="2"></td>
<td>8.4.2.1.1 Fast Throttle Overview</td>
<td>418</td>
</tr>
<tr>
<td colspan="2"></td>
<td>$8 . 4 . 2 . 1 . 2$ Fast Throttle Capability Structures</td>
<td>421</td>
</tr>
<tr>
<td colspan="2"></td>
<td>8.4.2.1.3 Fast Throttle Control Structures</td>
<td>428</td>
</tr>
<tr>
<td colspan="2"></td>
<td>8.4.2.1.4 Fast Throttle Logging Structures</td>
<td>434</td>
</tr>
<tr>
<td colspan="2"></td>
<td>8.4.2.1.5 Fast Throttle Address Map</td>
<td>436</td>
</tr>
<tr>
<td colspan="2">8.4.2.2</td>
<td>$\begin{array}{} { \text { Emergency } } \\ { 8 4 2 7 1 } \end{array}$ Shutdown</td>
<td>437</td>
</tr>
<tr>
<td colspan="2"></td>
<td>Emergency Shutdown Overview</td>
<td>437</td>
</tr>
<tr>
<td colspan="2"></td>
<td>$8 . 4 . 2 . 2 . 2$ Emergency Shutdown Capability Structures</td>
<td>440</td>
</tr>
<tr>
<td colspan="2"></td>
<td>Emergency Shutdown Control Structures</td>
<td>447</td>
</tr>
<tr>
<td colspan="2"></td>
<td>8.4.2.2.4 Emergency Shutdown Logging Structures</td>
<td>453</td>
</tr>
<tr>
<td colspan="2"></td>
<td>8.4.2.2.5 Emergency Shutdown Address Map</td>
<td>455</td>
</tr>
<tr>
<td colspan="3">Configuration and Parameters</td>
<td>456</td>
</tr>
<tr>
<td colspan="2">High-level Software</td>
<td>View of UCIe</td>
<td>456</td>
</tr>
<tr>
<td colspan="2">SW Discovery of</td>
<td>UCIe Links</td>
<td>457</td>
</tr>
<tr>
<td colspan="2">Register Location</td>
<td>Details and Access Mechanism</td>
<td>457</td>
</tr>
<tr>
<td colspan="2">Software view</td>
<td>Examples</td>
<td>459</td>
</tr>
<tr>
<td colspan="2">UCIe Registers</td>
<td></td>
<td>462</td>
</tr>
<tr>
<td colspan="3">UCIe Link DVSEC</td>
<td>462</td>
</tr>
<tr>
<td colspan="2">9.5.1.1</td>
<td>PCI Express Extended Capability Header (Offset 0h)</td>
<td>464</td>
</tr>
<tr>
<td colspan="2">9.5.1.2</td>
<td>Designated Vendor Specific Header 1, 2 (Offsets 4h and 8h)</td>
<td>464</td>
</tr>
<tr>
<td colspan="2"></td>
<td>Capability Descriptor (Offset Ah)</td>
<td>465</td>
</tr>
<tr>
<td colspan="2">$\begin{array}{} { 9 . 5 . 1 . 3 } \\ { 9 . 5 . 1 . 4 } \end{array}$</td>
<td>UCIe Link DVSEC - UCIe Link Capability (Offset Ch)</td>
<td>466</td>
</tr>
<tr>
<td colspan="2">9.5.1.5</td>
<td>UCIe Link DVSEC - UCIe Link Control (Offset 10h)</td>
<td>468</td>
</tr>
<tr>
<td colspan="2">9.5.1.6</td>
<td>UCIe Link DVSEC - UCIe Link Status (Offset 14h)</td>
<td>470</td>
</tr>
<tr>
<td colspan="2">9.5.1.7</td>
<td>UCIe Link DVSEC - Link Event Notification Control (Offset 18h)</td>
<td>472</td>
</tr>
<tr>
<td colspan="2">9.5.1.8</td>
<td>UCIe Link DVSEC - Error Notification Control (Offset 1Ah)</td>
<td>473</td>
</tr>
<tr>
<td colspan="2">9.5.1.9</td>
<td>UCIe Link DVSEC - Register Locator 0, 1, 2, 3 Low</td>
<td rowspan="2"></td>
</tr>
<tr>
<td colspan="2" rowspan="2"></td>
<td>(Offset 1Ch and when Register Locators 1, 2, 3</td>
</tr>
<tr>
<td>are present Offsets 24h, 2Ch, and 34h respectively)</td>
<td>476</td>
</tr>
<tr>
<td colspan="2">9.5.1.10</td>
<td rowspan="2">UCIe Link DVSEC - Register Locator 0, 1, 2, 3 High (Offset 20h and when Register Locators 1, 2, 3</td>
<td rowspan="2"></td>
</tr>
<tr>
<td colspan="2"></td>
</tr>
<tr>
<td colspan="2"></td>
<td>Are Present Offsets 28h, 30h, and 38h respectively)</td>
<td>477</td>
</tr>
<tr>
<td colspan="2">9.5.1.11</td>
<td>UCIe Link DVSEC - Sideband Mailbox Index Low (Offset is design dependent)</td>
<td>477</td>
</tr>
<tr>
<td colspan="2">9.5.1.12</td>
<td>UCIe Link DVSEC - Sideband Mailbox Index High (Offset is design dependent)</td>
<td>478</td>
</tr>
<tr>
<td colspan="2">9.5.1.13</td>
<td>UCIe Link DVSEC - Sideband Mailbox Data Low (Offset is design dependent)</td>
<td>478</td>
</tr>
<tr>
<td colspan="2">9.5.1.14</td>
<td>UCIe Link DVSEC - Sideband Mailbox Data High (Offset is design dependent)</td>
<td>478</td>
</tr>
<tr>
<td colspan="2">9.5.1.15</td>
<td>UCIe Link DVSEC - Sideband Mailbox Control</td>
<td></td>
</tr>
<tr>
<td colspan="2"></td>
<td>(Offset is design dependent)</td>
<td>479</td>
</tr>
<tr>
<td colspan="2">9.5.1.16</td>
<td>UCIe Link DVSEC - Sideband Mailbox Status</td>
<td></td>
</tr>
<tr>
<td colspan="2"></td>
<td>(Offset is design dependent)</td>
<td>479</td>
</tr>
<tr>
<td colspan="2">9.5.1.17</td>
<td>- Requester ID (Offset is design dependent)</td>
<td>479</td>
</tr>
<tr>
<td colspan="2">9.5.1.18</td>
<td>$\begin{array}{} \text { UCIe Link DVSEC } \\ \text { UCIe Link DVSEC } \end{array}$ - Associated Port Numbers</td>
<td rowspan="2">480</td>
</tr>
<tr>
<td colspan="2"></td>
<td>(Offset is design dependent)</td>
</tr>
<tr>
<td colspan="2">9.5.1.19</td>
<td>Examples of setting the Length field in DVSEC for various Scenarios</td>
<td>480</td>
</tr>
<tr>
<td></td>
<td colspan="2">UCIe Switch Register Block (UiSRB) DVSEC Capability</td>
<td>480</td>
</tr>
<tr>
<td colspan="2">9.5.2.1</td>
<td>PCI Express Extended Capability Header (Offset 0h)</td>
<td>480</td>
</tr>
<tr>
<td colspan="2">9.5.2.2</td>
<td>Designated Vendor Specific Header 1, 2 (Offsets 4h and 8h)</td>
<td>480</td>
</tr>
<tr>
<td colspan="2">9.5.2.3</td>
<td>UCIe Switch Register Block (UiSRB) Base Address (Offset Ch)</td>
<td>481</td>
</tr>
<tr>
<td colspan="2">D2D/PHY</td>
<td>Register Block</td>
<td>482</td>
</tr>
<tr>
<td colspan="2">9.5.3.1</td>
<td>UCIe Register Block Header</td>
<td>482</td>
</tr>
</table>

<table>
<tr>
<th></th>
<th></th>
<th>Contents</th>
</tr>
<tr>
<td>9.5.3.2</td>
<td>Uncorrectable Error Status Register (Offset 10h)</td>
<td>482</td>
</tr>
<tr>
<td>9.5.3.3</td>
<td>Uncorrectable Error Mask Register (Offset 14h)</td>
<td>483</td>
</tr>
<tr>
<td>9.5.3.4</td>
<td>Uncorrectable Error Severity Register (Offset 18h)</td>
<td>484</td>
</tr>
<tr>
<td>9.5.3.5</td>
<td>Correctable Error Status Register (Offset 1Ch)</td>
<td>484</td>
</tr>
<tr>
<td>9.5.3.6</td>
<td>Correctable Error Mask Register (Offset 20h)</td>
<td>485</td>
</tr>
<tr>
<td>9.5.3.7</td>
<td>Header Log 1 Register (Offset 24h)</td>
<td>485</td>
</tr>
<tr>
<td>9.5.3.8</td>
<td>Header Log 2 Register (Offset 2Ch)</td>
<td>486</td>
</tr>
<tr>
<td>9.5.3.9</td>
<td>Error and Link Testing Control Register (Offset 30h)</td>
<td>488</td>
</tr>
<tr>
<td>9.5.3.10</td>
<td>Runtime Link Testing Parity Log 0 (Offset 34h)</td>
<td>489</td>
</tr>
<tr>
<td>9.5.3.11</td>
<td>Runtime Link Testing Parity Log 1 (Offset 3Ch)</td>
<td>489</td>
</tr>
<tr>
<td>9.5.3.12</td>
<td>Runtime Link Testing Parity Log 2 (Offset 44h)</td>
<td>489</td>
</tr>
<tr>
<td>9.5.3.13</td>
<td>Runtime Link Testing Parity Log 3 (Offset 4Ch)</td>
<td>489</td>
</tr>
<tr>
<td>9.5.3.14</td>
<td>Advertised Adapter Capability Log (Offset 54h)</td>
<td>490</td>
</tr>
<tr>
<td>9.5.3.15</td>
<td>Finalized Adapter Capability Log (Offset 5Ch)</td>
<td>490</td>
</tr>
<tr>
<td>$9 . 5 . 3 . 1 6$</td>
<td>Advertised CXL Capability Log (Offset 64h)</td>
<td>490</td>
</tr>
<tr>
<td></td>
<td>Finalized CXL Capability Log (Offset 6Ch)</td>
<td>490</td>
</tr>
<tr>
<td>9.5.3.18</td>
<td>Advertised Multi-Protocol Capability Log Register (Offset 78h)</td>
<td>490</td>
</tr>
<tr>
<td>9.5.3.19</td>
<td>Finalized Multi-Protocol Capability Log Register (Offset 80h)</td>
<td>491</td>
</tr>
<tr>
<td>9.5.3.20</td>
<td>Advertised CXL Capability Log Register for Stack 1</td>
<td></td>
</tr>
<tr>
<td></td>
<td>(Offset 88h)</td>
<td>491</td>
</tr>
<tr>
<td>9.5.3.21</td>
<td>Finalized CXL Capability Log Register for Stack 1 (Offset 90h)</td>
<td>491</td>
</tr>
<tr>
<td>9.5.3.22</td>
<td>PHY Capability (Offset 1000h)</td>
<td>492</td>
</tr>
<tr>
<td>9.5.3.23</td>
<td>PHY Control (Offset 1004h)</td>
<td>493</td>
</tr>
<tr>
<td>9.5.3.24</td>
<td>PHY Status (Offset 1008h)</td>
<td>495</td>
</tr>
<tr>
<td>9.5.3.25</td>
<td>PHY Initialization and Debug (Offset 100Ch)</td>
<td>496</td>
</tr>
<tr>
<td>9.5.3.26</td>
<td>Training Setup 1 (Offset 1010h)</td>
<td>497</td>
</tr>
<tr>
<td>9.5.3.27</td>
<td>Training Setup 2 (Offset 1020h)</td>
<td>497</td>
</tr>
<tr>
<td>9.5.3.28</td>
<td>Training Setup 3 (Offset 1030h)</td>
<td>498</td>
</tr>
<tr>
<td>9.5.3.29</td>
<td>Training Setup 4 (Offset 1050h)</td>
<td>498</td>
</tr>
<tr>
<td>9.5.3.30</td>
<td>Current Lane Map Module 0 (Offset 1060h)</td>
<td>499</td>
</tr>
<tr>
<td>9.5.3.31</td>
<td>Current Lane Map Module 1 (Offset 1068h)</td>
<td>499</td>
</tr>
<tr>
<td>9.5.3.32</td>
<td>Current Lane Map Module 2 (Offset 1070h)</td>
<td>499</td>
</tr>
<tr>
<td>9.5.3.33</td>
<td>Current Lane Map Module 3 (Offset 1078h)</td>
<td>499</td>
</tr>
<tr>
<td>9.5.3.34</td>
<td>Error Log 0 (Offset 1080h)</td>
<td>500</td>
</tr>
<tr>
<td>9.5.3.35</td>
<td>Error Log 1 (Offset 1090h)</td>
<td>501</td>
</tr>
<tr>
<td>9.5.3.36</td>
<td>Runtime Link Test Control (Offset 1100h)</td>
<td>501</td>
</tr>
<tr>
<td>9.5.3.37</td>
<td>Runtime Link Test Status (Offset 1108h)</td>
<td>503</td>
</tr>
<tr>
<td>9.5.3.38</td>
<td>Mainband Data Repair (Offset 110Ch)</td>
<td>503</td>
</tr>
<tr>
<td>9.5.3.39</td>
<td>Clock, Track, Valid and Sideband Repair (Offset 1134h)</td>
<td>504</td>
</tr>
<tr>
<td>9.5.3.40</td>
<td>UCIe Link Health Monitor (UHM) DVSEC</td>
<td>505</td>
</tr>
<tr>
<td></td>
<td>9.5.3.40.1 UHM Status (Offset Eh)</td>
<td>506</td>
</tr>
<tr>
<td></td>
<td>9.5.3.40.2 Eye Margin (Starting Offset 18h)</td>
<td>506</td>
</tr>
<tr>
<td colspan="2">Test/Compliance Register Block</td>
<td>507</td>
</tr>
<tr>
<td>9.5.4.1</td>
<td>UCIe Register Block Header</td>
<td>507</td>
</tr>
<tr>
<td>9.5.4.2</td>
<td>D2D Adapter Test/Compliance Register Block Offset</td>
<td>508</td>
</tr>
<tr>
<td>9.5.4.3</td>
<td>PHY Test/Compliance Register Block Offset</td>
<td>508</td>
</tr>
<tr>
<td>9.5.4.4</td>
<td>D2D Adapter Test/Compliance Register Block</td>
<td>509</td>
</tr>
<tr>
<td></td>
<td>9.5.4.4.1 Adapter Compliance Control</td>
<td>509</td>
</tr>
<tr>
<td></td>
<td>9.5.4.4.2 Flit Tx Injection Control</td>
<td>509</td>
</tr>
<tr>
<td></td>
<td>9.5.4.4.3 Adapter Test Status (Offset 30h from D2DOFF)</td>
<td>511</td>
</tr>
<tr>
<td></td>
<td>9.5.4.4.4 Link State Injection Control Stack 0</td>
<td></td>
</tr>
<tr>
<td></td>
<td>(Offset 34h from D2DOFF)</td>
<td>512</td>
</tr>
<tr>
<td></td>
<td>9.5.4.4.5 Link State Injection Control Stack 1</td>
<td></td>
</tr>
<tr>
<td></td>
<td>(Offset 38h from D2DOFF)</td>
<td>512</td>
</tr>
<tr>
<td></td>
<td>9.5.4.4.6 Retry Injection Control (Offset 40h from D2DOFF)</td>
<td>513</td>
</tr>
<tr>
<td>9.5.4.5</td>
<td>PHY Test/Compliance Register Block</td>
<td>514</td>
</tr>
<tr>
<td colspan="3">9.5.4.5.1 Physical Layer Compliance Control 1 (Offsets 000h,</td>
</tr>
<tr>
<td></td>
<td>400h, 800h, and C00h from PHYOFF)</td>
<td>514</td>
</tr>
</table>

9.5.4

9.5.4.5.2
Physical Layer Compliance Control 2 (Offsets 008h,

408h, 808h, and C08h from PHYOFF)
516

9.5.4.5.3
Physical Layer Compliance Status 1 (Offsets 010h,

410h, 810h, and C10h from PHYOFF)
517

9.5.4.5.4
Physical Layer Compliance Status 2 (Offsets 018h,
518

418h, 818h, and C18h from PHYOFF)

9.5.4.5.5
Physical Layer Compliance Status 3 (Offsets 020h,
420h, 820h, and C20h from PHYOFF)
518

9.6

UCIe Link Registers in Streaming Mode and System SW/FW Implications
519

9.7
MSI and MSI-X Capability in Hosts/Switches for UCIe Interrupt
519

9.8
UCIe Early Discovery Table (UEDT)
520

10.0
0 Interface Definitions
521

10.1
Raw Die-to-Die Interface (RDI)
521

10.1.1
Interface reset requirements
529

10.1.2
Interface clocking requirements
529

10.1.3
Dynamic clock gating
530

10.1.3.1
Rules and description for
Ip_wake_req/pl_wake_ack handshake
530

10.1.3.2
Rules and description for pl_clk_req/lp_clk_ack handshake
530

532

10.1.5
RDI State Machine

533

10.1.6
RDI bring up flow

534

10.1.7
RDI PM flow
535

10.2
Flit-Aware Die-to-Die Interface (FDI)

539

10.2.1
Interface reset requirements
547

10.2.2
Interface clocking requirements
547

10.2.3
Dynamic clock gating
547

10.2.3.1
Rules and description for

Ip_wake_req/pl_wake_ack $P _ { R }$ handshake
547

10.2.3.2
description for pl_clk_req/Ip_clk_ack handshake
548

10.2.4
Data Transfer

549

10.2.5
Examples of pl_flit_cancel Timing Relationships

551

10.2.6
FDI State Machine

552

$1 0 . 2 . 7$
Rx_active_req/Sts Handshake

552

$1 0 . 2 . 9$
FDI PM Flow

555

10.3

Common rules for FDI and RDI

559

10.3.1
Byte Mapping for FDI and RDI

559

10.3.2
Stallreq/Ack Mechanism

563

10.3.3
State Request and Status

564

10.3.3.1
Reset State rules

565

$1 0 . 3 . 3 . 2$
Active State rules

566

10.3.3.4
Retrain State Rules

566

10.3.3.5
LinkReset State Rules

567

10.3.3.6
Disabled State Rules
568

10.3.3.7
LinkError State Rules
568

10.3.3.8
Common State Rules

569

10.3.4
Vendor-defined Signals

572

10.3.5
Example Flow Diagrams

575

10.3.5.1
LinkReset Entry and Exit
575

10.3.5.2
LinkError

576

10.3.5.3
Example of L2 Cross Product with Retrain on RDI
577

PM Entry/Exit Rules
566

FDI Bring up flow

553

10.2.4.1
DLLP transfer rules for 256B Flit Mode

550

10.1.4
Data Transfer

9.5.5
Implementation Specific Register Blocks
518

<table>
<tr>
<th colspan="2"></th>
<th>Contents</th>
</tr>
<tr>
<td></td>
<td>10.3.5.4 L2 Exit Example for RDI</td>
<td>578</td>
</tr>
<tr>
<td colspan="2">11.0 Compliance</td>
<td>579</td>
</tr>
<tr>
<td>11.1</td>
<td>Protocol Layer Compliance</td>
<td>580</td>
</tr>
<tr>
<td colspan="2">11.2 Adapter Compliance</td>
<td>580</td>
</tr>
<tr>
<td colspan="2">11.3 PHY Compliance</td>
<td>581</td>
</tr>
<tr>
<td colspan="2">A CXL/PCIe Register applicability to UCIe</td>
<td>582</td>
</tr>
<tr>
<td>A.1</td>
<td>CXL Registers applicability to UCIe</td>
<td>582</td>
</tr>
<tr>
<td colspan="2">A.2 PCIe Register applicability to UCIe</td>
<td>582</td>
</tr>
<tr>
<td>A.3</td>
<td>PCIe/CXL registers that need to be part of D2D</td>
<td>584</td>
</tr>
<tr>
<td colspan="2">B AIB Interoperability</td>
<td>585</td>
</tr>
<tr>
<td>B.1</td>
<td>AIB Signal Mapping</td>
<td>585</td>
</tr>
<tr>
<td></td>
<td>B.1.1 Data path</td>
<td>585</td>
</tr>
<tr>
<td></td>
<td>B.1.2 Always high Valid</td>
<td>585</td>
</tr>
<tr>
<td></td>
<td>B.1.3 Sideband</td>
<td>585</td>
</tr>
<tr>
<td></td>
<td>B.1.4 Raw Die-to-Die interface</td>
<td>586</td>
</tr>
<tr>
<td colspan="2">B.2 Initialization</td>
<td>587</td>
</tr>
<tr>
<td>B.3</td>
<td>Bump Map</td>
<td>587</td>
</tr>
</table>

#### Figures

<table>
<tr>
<td>1-1</td>
<td>A Package Composed of CPU Dies, Accelerator Die(s), and I/O Tile Die Connected through UCIe</td>
<td>39</td>
</tr>
<tr>
<td>1-2</td>
<td>UCIe enabling long-reach connectivity at Rack/Pod Level</td>
<td>39</td>
</tr>
<tr>
<td>1-3</td>
<td>Standard Package interface</td>
<td>40</td>
</tr>
<tr>
<td>1-4</td>
<td>Advanced Package interface: Example 1</td>
<td>41</td>
</tr>
<tr>
<td>1-5</td>
<td>Advanced Package interface: Example 2</td>
<td>41</td>
</tr>
<tr>
<td>1-6</td>
<td>Advanced Package interface: Example 3</td>
<td>41</td>
</tr>
<tr>
<td>1-7</td>
<td>Example of UCIe-3D</td>
<td>41</td>
</tr>
<tr>
<td>1-8</td>
<td>UCIe Layers and functionalities</td>
<td>42</td>
</tr>
<tr>
<td>1-9</td>
<td>Physical Layer components</td>
<td>43</td>
</tr>
<tr>
<td>1-10</td>
<td>Single module configuration: Advanced Package</td>
<td>44</td>
</tr>
<tr>
<td>1-11</td>
<td>Single module configuration: Standard Package</td>
<td>45</td>
</tr>
<tr>
<td>1-12</td>
<td>Two-module configuration for Standard Package</td>
<td>45</td>
</tr>
<tr>
<td>1-13</td>
<td>Four-module configuration for Standard Package</td>
<td>45</td>
</tr>
<tr>
<td>1-14</td>
<td>Example of a Two-module Configuration for Advanced Package</td>
<td>46</td>
</tr>
<tr>
<td>1-15</td>
<td>One-port Sideband-only Link</td>
<td>46</td>
</tr>
<tr>
<td>1-16</td>
<td>Two-port Sideband-only Link</td>
<td>46</td>
</tr>
<tr>
<td>1-17</td>
<td>Four-port Sideband-only Link</td>
<td>47</td>
</tr>
<tr>
<td>1-18</td>
<td>Block Diagram for UCIe Retimer Connection</td>
<td>47</td>
</tr>
<tr>
<td>2-1</td>
<td>Color-coding Convention in Flit Format Byte Map Figures</td>
<td>52</td>
</tr>
<tr>
<td>2-2</td>
<td>68B Flit Format on FDI</td>
<td>56</td>
</tr>
<tr>
<td></td>
<td>Functionalities in the Die-to-Die Adapter</td>
<td>58</td>
</tr>
<tr>
<td></td>
<td>Example Configurations</td>
<td>61</td>
</tr>
<tr>
<td>$\begin{array}{} { 3 - 1 } \\ { 3 - 2 } \\ { 3 - 3 } \\ { 3 - 4 } \end{array}$</td>
<td>Stages of UCIe Link Initialization</td>
<td>62</td>
</tr>
<tr>
<td></td>
<td>Parameter Exchange for CXL or PCIe (i.e., "68B Flit Mode" or "CXL 256B Flit Mode" is 1 in {FinCap.Adapter} )</td>
<td>66</td>
</tr>
<tr>
<td>3-5</td>
<td>Both Stacks are CXL or PCIe</td>
<td>68</td>
</tr>
<tr>
<td>3-6</td>
<td>$S t a c k \quad 0 \quad i s \quad P C I e ,$ Stack 1 is Streaming</td>
<td>68</td>
</tr>
<tr>
<td>3-7</td>
<td>Stack 0 is Streaming, Stack 1 is PCIe</td>
<td>69</td>
</tr>
<tr>
<td>3-8</td>
<td>Both Stacks are Streaming</td>
<td>69</td>
</tr>
<tr>
<td>3-9</td>
<td>Stack 0 is Streaming, Stack 1 is CXL</td>
<td>70</td>
</tr>
<tr>
<td>3-10</td>
<td>Format 1: Raw Format</td>
<td>71</td>
</tr>
<tr>
<td>3-11</td>
<td>Format 2: 68B Flit Format</td>
<td>74</td>
</tr>
<tr>
<td>3-12</td>
<td>Format 2: 68B Flit Format PDS Example 1</td>
<td>75</td>
</tr>
<tr>
<td>3-13</td>
<td>Format 2: 68B Flit Format PDS Example 2 - Extra Os Padded to Make the Data Transfer a Multiple of 256B</td>
<td>75</td>
</tr>
<tr>
<td></td>
<td>Format 3: Standard 256B End Header Flit Format for PCIe</td>
<td>77</td>
</tr>
<tr>
<td>$\begin{array}{} { 3 - 1 4 } \\ { 3 - 1 5 } \\ { 3 - 1 6 } \end{array}$</td>
<td>Format 3: Standard 256B End Header Flit Format for Streaming Protocol</td>
<td>77</td>
</tr>
<tr>
<td></td>
<td>Format 3: Standard 256B End Header Flit Format for Management Transport Protocol</td>
<td>77</td>
</tr>
<tr>
<td>3-17</td>
<td>Format 4: Standard 256B Start Header Flit Format for CXL.cachemem or Streaming Protocol</td>
<td>78</td>
</tr>
<tr>
<td>3-18</td>
<td>Format 4: Standard 256B Start Header Flit Format for CXL.io or PCIe</td>
<td>78</td>
</tr>
<tr>
<td>3-19</td>
<td>Format 4: Standard 256B Start Header Flit Format for Management Transport Protocol</td>
<td>78</td>
</tr>
<tr>
<td>3-20</td>
<td>Format 5: Latency-Optimized 256B without Optional Bytes Flit Format for CXL.io</td>
<td>81</td>
</tr>
<tr>
<td>3-21</td>
<td>Format 5: Latency-Optimized 256B without Optional Bytes Flit Format for CXL.cachemem and Streaming Protocol</td>
<td>82</td>
</tr>
<tr>
<td>3-22</td>
<td>Format 5: Latency-Optimized 256B without Optional Bytes Flit Format for Management Transport Protocol</td>
<td>82</td>
</tr>
</table>

<table>
<tr>
<td>3-23</td>
<td>Format 6: Latency-Optimized 256B with Optional Bytes Flit Format for CXL.io or PCIe</td>
<td>82</td>
</tr>
<tr>
<td>3-24</td>
<td>Format 6: Latency-Optimized 256B with Optional Bytes Flit Format for CXL.cachemem</td>
<td>83</td>
</tr>
<tr>
<td>3-25</td>
<td>Format 6: Latency-Optimized 256B with Optional Bytes Flit Format for Streaming Protocol</td>
<td>83</td>
</tr>
<tr>
<td>3-26</td>
<td>Format 6: Latency-Optimized 256B with Optional Bytes Flit Format for Management Transport Protocol</td>
<td>83</td>
</tr>
<tr>
<td>3-27</td>
<td>State Machine Hierarchy Examples</td>
<td>89</td>
</tr>
<tr>
<td>3-28</td>
<td>Example of Hierarchical PM Entry for CXL</td>
<td>91</td>
</tr>
<tr>
<td>3-29</td>
<td>Diagram of CRC Calculation</td>
<td>92</td>
</tr>
<tr>
<td>3-30</td>
<td>Successful Parity Feature negotiation between Die 1 Tx and Die 0 Rx</td>
<td>96</td>
</tr>
<tr>
<td>3-31</td>
<td>Unsuccessful Parity Feature negotiation between Die 1 Tx and Die 0 Rx</td>
<td>97</td>
</tr>
<tr>
<td>4-1</td>
<td>Bit arrangement within a byte transfer</td>
<td>98</td>
</tr>
<tr>
<td>4-2</td>
<td>Byte map for x64 interface</td>
<td>99</td>
</tr>
<tr>
<td>4-3</td>
<td>Byte map for x32 interface</td>
<td>99</td>
</tr>
<tr>
<td>4-4</td>
<td>Byte map for x16 interface</td>
<td>99</td>
</tr>
<tr>
<td>4-5</td>
<td>Byte to Lane mapping for Standard package x16 degraded to x8</td>
<td>100</td>
</tr>
<tr>
<td>4-6</td>
<td>Valid framing example</td>
<td>101</td>
</tr>
<tr>
<td>4-7</td>
<td>Example 64-bit Sideband Serial Packet Transfer</td>
<td>102</td>
</tr>
<tr>
<td>4-8</td>
<td>Sideband Packet Transmission: Back-to-Back</td>
<td>102</td>
</tr>
<tr>
<td>4-9</td>
<td>Example 64-bit Sideband Serial Packet Transfer in Sideband Performant Mode</td>
<td>103</td>
</tr>
<tr>
<td>4-10</td>
<td>Sideband Packet Transmission: Back-to-Back in Sideband Performant Mode</td>
<td>103</td>
</tr>
<tr>
<td>4-11</td>
<td>Example of a Normal Traffic Packet Interrupted by a Single Priority Traffic Packet</td>
<td>104</td>
</tr>
<tr>
<td>4-12</td>
<td>Data Lane remapping possibilities to fix potential defects</td>
<td>107</td>
</tr>
<tr>
<td>4-13</td>
<td>Data Lane remapping: Mux chain</td>
<td>108</td>
</tr>
<tr>
<td>4-14</td>
<td>Example of Single Lane failure remapping</td>
<td>110</td>
</tr>
<tr>
<td>4-15</td>
<td>Example of Single Lane remapping implementation</td>
<td>110</td>
</tr>
<tr>
<td>4-16</td>
<td>Example of Two Lane failure remapping</td>
<td>112</td>
</tr>
<tr>
<td>4-17</td>
<td>Example of Two Lane remapping implementation</td>
<td>112</td>
</tr>
<tr>
<td>4-18</td>
<td>Clock and Track repair</td>
<td>115</td>
</tr>
<tr>
<td>4-19</td>
<td>Clock and track repair: Differential Rx</td>
<td>116</td>
</tr>
<tr>
<td>4-20</td>
<td>Clock and track repair: Pseudo Differential Rx</td>
<td>116</td>
</tr>
<tr>
<td>4-21</td>
<td>Clock and Track Lane repair scheme</td>
<td>117</td>
</tr>
<tr>
<td>4-22</td>
<td>Clock and track repair: CKP repair</td>
<td>117</td>
</tr>
<tr>
<td>4-23</td>
<td>Clock and track repair: CKN repair</td>
<td>117</td>
</tr>
<tr>
<td>4-24</td>
<td>Clock and track repair: Track repair</td>
<td>118</td>
</tr>
<tr>
<td>4-25</td>
<td>Valid repair: Normal Path</td>
<td>118</td>
</tr>
<tr>
<td>4-26</td>
<td>Valid Repair: Repair Path</td>
<td>118</td>
</tr>
<tr>
<td>4-27</td>
<td>Test and training logic</td>
<td>119</td>
</tr>
<tr>
<td>4-28</td>
<td>Lane failure detection</td>
<td>120</td>
</tr>
<tr>
<td>4-29</td>
<td>All Lane error detection</td>
<td>120</td>
</tr>
<tr>
<td>4-30</td>
<td>LFSR implementation</td>
<td>122</td>
</tr>
<tr>
<td>4-31</td>
<td>LFSR alternate implementation</td>
<td>123</td>
</tr>
<tr>
<td>4-32</td>
<td>Example Retimer bring up when performing speed/width match</td>
<td>130</td>
</tr>
<tr>
<td>4-33</td>
<td>Link Training State Machine</td>
<td>131</td>
</tr>
<tr>
<td>4-34</td>
<td>MBINIT: Mainband Initialization and Repair Flow</td>
<td>137</td>
</tr>
<tr>
<td>4-35</td>
<td>Example Sideband Management Transport Protocol Negotiation - Single-module Scenario</td>
<td>140</td>
</tr>
<tr>
<td>$4 - 3 6$</td>
<td>Example Sideband Management Transport Protocol Negotiation - Two-module Scenario</td>
<td>140</td>
</tr>
<tr>
<td>4-37</td>
<td>Example Sideband MPM Logical Flow with Two Modules and No Module Reversal</td>
<td>142</td>
</tr>
<tr>
<td>4-38</td>
<td>Example Sideband MPM Logical Flow with Two Modules and Module Reversal</td>
<td>143</td>
</tr>
<tr>
<td>4-39</td>
<td>MBINIT "Stall" Example 1</td>
<td>144</td>
</tr>
<tr>
<td>4-40</td>
<td>MBINIT "Stall" Example 2</td>
<td>145</td>
</tr>
</table>

<table>
<tr>
<th></th>
<th></th>
<th>Figures</th>
</tr>
<tr>
<td>$4 - 4 1$</td>
<td>Mainband Training</td>
<td>156</td>
</tr>
<tr>
<td>4-42</td>
<td>Example L2 Exit Flow with L2SPD Capability</td>
<td>173</td>
</tr>
<tr>
<td>4-43</td>
<td>Example of Byte Mapping for Matching Module IDs</td>
<td>175</td>
</tr>
<tr>
<td>4-44</td>
<td>Example of Byte Mapping for Differing Module IDs</td>
<td>175</td>
</tr>
<tr>
<td>4-45</td>
<td>Example of Width Degradation with Byte Mapping for Differing Module IDs</td>
<td>176</td>
</tr>
<tr>
<td>4-46</td>
<td>Example of Byte Mapping with Module Disable</td>
<td>176</td>
</tr>
<tr>
<td>4-47</td>
<td>Decision Flow Chart for Multi-module Advanced Package</td>
<td>177</td>
</tr>
<tr>
<td>4-48</td>
<td>Decision Flow Chart for Multi-module Standard Package</td>
<td>178</td>
</tr>
<tr>
<td>4-49</td>
<td>Implementation Example Showing Two Different Operating Modes of the Same Hardware Implementation</td>
<td>181</td>
</tr>
<tr>
<td>4-50</td>
<td>RDI Byte-to-Module Assignment Example for x64 Interop with x32</td>
<td>182</td>
</tr>
<tr>
<td>4-51</td>
<td>Example of Encapsulated MTPs Transmitted on Sideband Link without Sideband PMO</td>
<td>183</td>
</tr>
<tr>
<td>4-52</td>
<td>Example of a Large Management Packet Split into Two Encapsulated MTPs, with No Segmentation, No Sideband PMO, and with</td>
<td></td>
</tr>
<tr>
<td></td>
<td>Two Link Management Packets between the Two Encapsulated MTPs</td>
<td>183</td>
</tr>
<tr>
<td>5-1</td>
<td>Example Common Reference Clock</td>
<td>185</td>
</tr>
<tr>
<td>5-2</td>
<td>x64 or x32 Advanced Package Module</td>
<td>187</td>
</tr>
<tr>
<td>5-3</td>
<td>x16 or x8 Standard Package Module</td>
<td>187</td>
</tr>
<tr>
<td>5-4</td>
<td>Transmitter</td>
<td>190</td>
</tr>
<tr>
<td>5-5</td>
<td>Transmitter driver example circuit</td>
<td>191</td>
</tr>
<tr>
<td>5-6</td>
<td>Transmitter de-emphasis</td>
<td>193</td>
</tr>
<tr>
<td>5-7</td>
<td>Transmitter de-emphasis waveform</td>
<td>193</td>
</tr>
<tr>
<td>5-8</td>
<td>3-tap Transmitter Equalization (Used at 48 GT/s and 64 GT/s)</td>
<td>194</td>
</tr>
<tr>
<td>5-9</td>
<td>Receiver topology</td>
<td>195</td>
</tr>
<tr>
<td>5-10</td>
<td>Receiver Termination Map for Table 5-10 (Tx Swing = 0.4 V)</td>
<td>198</td>
</tr>
<tr>
<td>5-11</td>
<td>Receiver termination</td>
<td>198</td>
</tr>
<tr>
<td>5-12</td>
<td>Receiver termination map for Table 5-11 (TX Swing = 0.85 V)</td>
<td>199</td>
</tr>
<tr>
<td>5-13</td>
<td>Reference Rx CTLE for 24 GT/s</td>
<td>200</td>
</tr>
<tr>
<td>5-14</td>
<td>Reference Rx CTLE for 64 GT/s</td>
<td>201</td>
</tr>
<tr>
<td>5-15</td>
<td>Clocking architecture</td>
<td>202</td>
</tr>
<tr>
<td>5-16</td>
<td>Track Usage Example</td>
<td>204</td>
</tr>
<tr>
<td>5-17</td>
<td>Example Rectangular Eye Mask Diagram for &lt;= 32 GT/s</td>
<td>205</td>
</tr>
<tr>
<td>5-18</td>
<td>Diamond Eye Mask for 48 GT/s and 64 GT/s</td>
<td>206</td>
</tr>
<tr>
<td>5-19</td>
<td>Example Eye Simulation Setup</td>
<td>207</td>
</tr>
<tr>
<td>5-20</td>
<td>Circuit for VTF calculation</td>
<td>208</td>
</tr>
<tr>
<td>5-21</td>
<td>Loss and Crosstalk Mask</td>
<td>211</td>
</tr>
<tr>
<td>5-22</td>
<td>Viewer Orientation Looking at the Defined UCIe Bump Matrix</td>
<td>211</td>
</tr>
<tr>
<td>5-23</td>
<td>10-column x64 Advanced Package Bump Map for $< = 3 2 \quad G T / s$</td>
<td>212</td>
</tr>
<tr>
<td>5-24</td>
<td>16-column x64 Advanced Package Bump Map for $< = 3 2 \quad G T / s$</td>
<td>213</td>
</tr>
<tr>
<td>5-25</td>
<td>8-column x64 Advanced Package Bump Map for $< = 3 2 \quad G T / s$</td>
<td>214</td>
</tr>
<tr>
<td>5-26</td>
<td>10-column x64 Advanced Package Bump map: Signal exit order</td>
<td>215</td>
</tr>
<tr>
<td>5-27</td>
<td>Enhanced 10-column x64 Advanced Package Bump Map Example for 32 GT/s Implementation</td>
<td>216</td>
</tr>
<tr>
<td>5-28</td>
<td>Enhanced 16-column x64 Advanced Package Bump Map Example for 16 GT/s Implementation</td>
<td>217</td>
</tr>
<tr>
<td>5-29</td>
<td>Enhanced 8-column x64 Advanced Package Bump Map Example for 32 GT/s Implementation</td>
<td>218</td>
</tr>
<tr>
<td>5-30</td>
<td>10-column $\times 6 4$ Package Bump Map for 48 GT/s and 64 GT/s</td>
<td>220</td>
</tr>
<tr>
<td>5-31</td>
<td>10-column x32 Package Bump Map for $< = 3 2 \quad G T / s$</td>
<td>222</td>
</tr>
<tr>
<td>5-32</td>
<td>16-column x32 Advanced Package Bump Map for $< = 3 2 \quad G T / s$</td>
<td>222</td>
</tr>
<tr>
<td>5-33</td>
<td>8-column x32 Advanced Package Bump Map for $< = 3 2 \quad G T / s$</td>
<td>223</td>
</tr>
<tr>
<td>5-34</td>
<td>10-column x32 Advanced Package Bump Map: Signal Exit Order</td>
<td>223</td>
</tr>
<tr>
<td>5-35</td>
<td>Enhanced 10-column x32 Advanced Package Bump Map Example for 32 GT/s Implementation</td>
<td>225</td>
</tr>
</table>

<table>
<tr>
<td>5-36</td>
<td>Enhanced 16-column x32 Advanced Package Bump Map Example for 16 GT/s Implementation</td>
<td>226</td>
</tr>
<tr>
<td>5-37</td>
<td>Enhanced 8-column x32 Advanced Package Bump Map Example for 32 GT/s Implementation</td>
<td>227</td>
</tr>
<tr>
<td>5-38</td>
<td>Example of Normal and Mirrored x64-to-x32 Advanced Package Module Connection</td>
<td>230</td>
</tr>
<tr>
<td>5-39</td>
<td>Example of Normal and Mirrored x32-to-x32 Advanced Package Module Connection</td>
<td>231</td>
</tr>
<tr>
<td>$5 - 4 0$</td>
<td>Naming Convention for One-, Two-, and Four-module Advanced Package Paired with "Standard Die Rotate" Configurations</td>
<td>232</td>
</tr>
<tr>
<td>5-41</td>
<td>Naming Convention for One-, Two-, and Four-module Advanced Package Paired with "Mirrored Die Rotate" Configurations</td>
<td>232</td>
</tr>
<tr>
<td>$5 - 4 2$</td>
<td>Examples for Advanced Package Configurations Paired with "Standard Die Rotate" Counterparts, with a Different Number of Modules</td>
<td>233</td>
</tr>
<tr>
<td>$5 - 4 3$</td>
<td>Examples for Advanced Package Configurations Paired with "Mirrored Die Rotate" Counterparts, with a Different Number of Modules</td>
<td>234</td>
</tr>
<tr>
<td>5-44</td>
<td>Standard Package Bump Map: x16 interface</td>
<td>237</td>
</tr>
<tr>
<td>5-45</td>
<td>Standard Package x16 interface: Signal exit order</td>
<td>237</td>
</tr>
<tr>
<td>5-46</td>
<td>Standard Package Bump Map: x32 interface</td>
<td>237</td>
</tr>
<tr>
<td>5-49</td>
<td>Standard Package reference configuration</td>
<td>238</td>
</tr>
<tr>
<td>5-47</td>
<td>Standard Package x32 interface: Signal exit routing</td>
<td>238</td>
</tr>
<tr>
<td>5-48</td>
<td>Standard Package cross section for stacked module</td>
<td>238</td>
</tr>
<tr>
<td>5-50</td>
<td>Standard Package Bump Map: 48 GT/s and 64 GT/s x32 Interface</td>
<td>239</td>
</tr>
<tr>
<td>5-51</td>
<td>x16 Standard Package Potential Bump Map: 48 GT/s and 64 GT/s x16</td>
<td>240</td>
</tr>
<tr>
<td>5-52</td>
<td>Standard Package Bump Map: x8 Interface</td>
<td>241</td>
</tr>
<tr>
<td>5-53</td>
<td>Naming Convention for One-, Two-, and Four-module Standard Package Paired with "Standard Die Rotate" Configurations</td>
<td>242</td>
</tr>
<tr>
<td>$5 - 5 4$</td>
<td>Naming Convention for One-, Two-, and Four-module Standard Package Paired with "Mirrored Die Rotate" Configurations</td>
<td>242</td>
</tr>
<tr>
<td>5-55</td>
<td>Examples for Standard Package Configurations Paired with "Standard Die Rotate" Counterparts, with a Different Number of Modules</td>
<td>244</td>
</tr>
<tr>
<td>5-56</td>
<td>Examples for Standard Package Configurations Paired with "Mirrored Die Rotate" Counterparts, with a Different Number of Modules</td>
<td>245</td>
</tr>
<tr>
<td>5-57</td>
<td>Additional Examples for Standard Package Configurations Paired with "Mirrored Die Rotate" Counterparts, with a Different Number of Modules</td>
<td>245</td>
</tr>
<tr>
<td>5-58</td>
<td>Example of a Configuration for Standard Package, with Some Modules Disabled</td>
<td>247</td>
</tr>
<tr>
<td>5-59</td>
<td>UCIe-S Sideband-only Port Bump Map</td>
<td>248</td>
</tr>
<tr>
<td>5-60</td>
<td>UCIe-S Sideband-only Port Supported Configurations</td>
<td>248</td>
</tr>
<tr>
<td>5-61</td>
<td>Data Lane repair resources</td>
<td>250</td>
</tr>
<tr>
<td>5-62</td>
<td>Data Lane repair</td>
<td>250</td>
</tr>
<tr>
<td>5-63</td>
<td>Valid Framing</td>
<td>251</td>
</tr>
<tr>
<td>5-64</td>
<td>Data, Clock, Valid Levels for Half-rate Clocking: Clock-gated Unterminated Link</td>
<td>251</td>
</tr>
<tr>
<td>5-65</td>
<td>Data, Clock, Valid Levels for Quarter-rate Clocking: Clock-gated Unterminated Link</td>
<td>252</td>
</tr>
<tr>
<td>$5 - 6 6$</td>
<td>Data, Clock, Valid Levels for Half-rate Clocking: Continuous Clock Unterminated Link</td>
<td>252</td>
</tr>
<tr>
<td>$5 - 6 7$</td>
<td>Data, Clock, Valid Gated Levels for Half-rate Clocking: Terminated Link</td>
<td>252</td>
</tr>
<tr>
<td>5-68</td>
<td>Data, Clock, Valid Gated Levels for Quarter-rate Clocking: Terminated Link</td>
<td>253</td>
</tr>
<tr>
<td>$5 - 6 9$</td>
<td>Data, Clock, Valid Gated Levels for Half-rate Clocking: Continuous Clock Terminated Link</td>
<td>253</td>
</tr>
<tr>
<td>5-70</td>
<td>Sideband signaling</td>
<td>254</td>
</tr>
<tr>
<td>5-71</td>
<td>Example Package Route for Open Drain Signal</td>
<td>256</td>
</tr>
<tr>
<td>5-72</td>
<td>Example Bridging between Internal and External Event Pin</td>
<td>257</td>
</tr>
</table>

6-1

6-2

6-3

6-4

6-5

6-6

6-7

6-8

7-1

7-2

7-3

7-4

7-5

7-6

7-7

7-8

7-9

7-10

7-11

7-12

7-13

7-14

7-15

8-1

8-2

8-3

8-4

8-5

8-6

8-7

8-8

8-9

8-10

8-11

8-12

8-13

8-14

8-15

8-16

8-17

8-18

8-19

8-20

8-21

8-22

8-23

8-24

8-25

8-26

8-27

8-28

<table>
<tr>
<th></th>
<th>Figures</th>
</tr>
<tr>
<td>Example of 3D Die Stacking</td>
<td>258</td>
</tr>
<tr>
<td>UCIe-3D Illustration</td>
<td>259</td>
</tr>
<tr>
<td>UCIe-3D PHY</td>
<td>260</td>
</tr>
<tr>
<td>Start Edge and Sample Edge</td>
<td>261</td>
</tr>
<tr>
<td>Dtx and Drx Spec Range for 4 GT/s</td>
<td>263</td>
</tr>
<tr>
<td>UCIe-3D Module Bump Map</td>
<td>264</td>
</tr>
<tr>
<td>x70 Module</td>
<td>265</td>
</tr>
<tr>
<td>Bundle Repair</td>
<td>266</td>
</tr>
<tr>
<td>Format for Register Access Request</td>
<td>273</td>
</tr>
<tr>
<td>Format for Register Access Completions</td>
<td>274</td>
</tr>
<tr>
<td>Format for Messages without Data</td>
<td>275</td>
</tr>
<tr>
<td>Format for Messages with data payloads</td>
<td>283</td>
</tr>
<tr>
<td>Common Fields in MPM Header of all MPM with Data Messages on Sideband</td>
<td>291</td>
</tr>
<tr>
<td>Encapsulated MTP on Sideband</td>
<td>292</td>
</tr>
<tr>
<td>Vendor-defined Management Port Gateway Message with Data on Sideband</td>
<td>293</td>
</tr>
<tr>
<td>Common Fields in MPM Header of all MPM without Data Messages on Sideband</td>
<td>294</td>
</tr>
<tr>
<td>Management Port Gateway Capabilities MPM on Sideband</td>
<td>294</td>
</tr>
<tr>
<td>Credit Return MPM on Sideband</td>
<td>295</td>
</tr>
<tr>
<td>Init Done MPM on Sideband</td>
<td>296</td>
</tr>
<tr>
<td>PM MPM on Sideband</td>
<td>296</td>
</tr>
<tr>
<td>Vendor-defined Management Port Gateway MPM without Data on Sideband</td>
<td>297</td>
</tr>
<tr>
<td>Format for Priority Sideband Traffic Packets</td>
<td>297</td>
</tr>
<tr>
<td>Example Flow for Remote Register Access Request (Local FDI/RDI Credit Checks Are Not Explicitly Shown)</td>
<td>300</td>
</tr>
<tr>
<td>Example UCIe Chiplet that Supports Manageability</td>
<td>304</td>
</tr>
<tr>
<td>Example SiP that Supports Manageability</td>
<td>305</td>
</tr>
<tr>
<td>UCIe Manageability Protocol Hierarchy</td>
<td>306</td>
</tr>
<tr>
<td>Relationship Between the Various Types of Management Entities</td>
<td>307</td>
</tr>
<tr>
<td>UCIe Management Transport Packet</td>
<td>308</td>
</tr>
<tr>
<td>Management Network ID Format</td>
<td>312</td>
</tr>
<tr>
<td>Access Control Determination in a Responder Management Entity</td>
<td>318</td>
</tr>
<tr>
<td>Memory Map for Management Entities</td>
<td>321</td>
</tr>
<tr>
<td>Management Capability Structure Organization</td>
<td>322</td>
</tr>
<tr>
<td>Vendor Defined Management Capability Structure Organization</td>
<td>323</td>
</tr>
<tr>
<td>Management Capability Directory</td>
<td>323</td>
</tr>
<tr>
<td>Capability Pointer</td>
<td>324</td>
</tr>
<tr>
<td>Chiplet Capability Structure Organization</td>
<td>325</td>
</tr>
<tr>
<td>Chiplet Capability Structure</td>
<td>325</td>
</tr>
<tr>
<td>Management Port Structure</td>
<td>328</td>
</tr>
<tr>
<td>Route Entry</td>
<td>333</td>
</tr>
<tr>
<td>Access Control Capability Structure</td>
<td>335</td>
</tr>
<tr>
<td>Standard Asset Class Access Table</td>
<td>337</td>
</tr>
<tr>
<td>Vendor Defined Asset Class Access Table</td>
<td>337</td>
</tr>
<tr>
<td>Security Clearance Group Capability Structure</td>
<td>340</td>
</tr>
<tr>
<td>Security Clearance Group Context</td>
<td>341</td>
</tr>
<tr>
<td>UCIe Memory Access Request Packet Format</td>
<td>342</td>
</tr>
<tr>
<td>UCIe Memory Access Response Packet</td>
<td>346</td>
</tr>
<tr>
<td>UCIe Memory Access Protocol Capability Structure</td>
<td>347</td>
</tr>
<tr>
<td>Empty Circular Buffer</td>
<td>349</td>
</tr>
<tr>
<td>Full Circular Buffer with Write Offset below Read Offset</td>
<td>350</td>
</tr>
<tr>
<td>Full Circular Buffer with Write Offset above Read Offset</td>
<td>350</td>
</tr>
<tr>
<td>Circular Buffer State Machine</td>
<td>351</td>
</tr>
</table>

<table>
<tr>
<td>8-29</td>
<td>Sink Circular Buffer, UMAP Requester Write to and Management Entity Read from</td>
<td>356</td>
</tr>
<tr>
<td>8-30</td>
<td>Source Circular Buffer, UMAP Requester Read from and Management Entity Write to</td>
<td>358</td>
</tr>
<tr>
<td>8-31</td>
<td>Open Drain Detection Capability Structure</td>
<td>360</td>
</tr>
<tr>
<td>8-32</td>
<td>Valid Sample Count Example</td>
<td>361</td>
</tr>
<tr>
<td>8-33</td>
<td>UCIe Sideband Management Path Architecture</td>
<td>362</td>
</tr>
<tr>
<td>8-34</td>
<td>UCIe Mainband Management Path Architecture</td>
<td>363</td>
</tr>
<tr>
<td>8-35</td>
<td>Supported Configurations for Management Port Gateway Connectivity to D2D Adapter on Mainband</td>
<td>365</td>
</tr>
<tr>
<td>8-36</td>
<td>Common Fields in MPM Header of all MPM with Data Messages on Mainband</td>
<td>366</td>
</tr>
<tr>
<td>8-37</td>
<td>Encapsulated MTP on Mainband</td>
<td>367</td>
</tr>
<tr>
<td>8-38</td>
<td>Vendor-defined Management Port Gateway Message with Data on Mainband</td>
<td>368</td>
</tr>
<tr>
<td>8-39</td>
<td>Common Fields in MPM Header of all MPM without Data Messages on Mainband</td>
<td>369</td>
</tr>
<tr>
<td>8-40</td>
<td>Management Port Gateway Capabilities MPM on Mainband</td>
<td>369</td>
</tr>
<tr>
<td>8-41</td>
<td>Init Done MPM on Mainband</td>
<td>370</td>
</tr>
<tr>
<td>8-42</td>
<td>Vendor-defined Management Port Gateway Message without Data on Mainband</td>
<td>370</td>
</tr>
<tr>
<td>8-43</td>
<td>Sideband Management Transport Initialization Phase Example with RxQ-ID=0 and One VC (VC0)</td>
<td>373</td>
</tr>
<tr>
<td>8-44</td>
<td>Sideband Management Transport Initialization Phase Example with RxQ-ID=0, 1 and One VC (VC0)</td>
<td>373</td>
</tr>
<tr>
<td>$8 - 4 5$</td>
<td>Sideband Management Transport Initialization Phase Example with RxQ-ID=0 and Two VCs (VC0, VC1)</td>
<td>374</td>
</tr>
<tr>
<td>$8 - 4 6$</td>
<td>Mainband Management Transport Initialization Phase Example with $R x Q - I D = 0$ and One VC (VC0)</td>
<td>376</td>
</tr>
<tr>
<td>8-47</td>
<td>Mainband Management Transport Initialization Phase Example with RxQ-ID=0, 1 and One VC (VC0)</td>
<td>377</td>
</tr>
<tr>
<td>8-48</td>
<td>Mainband Management Transport Initialization Phase Example with RxQ-ID=0 and Two VCs (VC0, VC1)</td>
<td>377</td>
</tr>
<tr>
<td>8-49</td>
<td>Example Illustration of a Large MTP Transmitted over Multiple RxQ-IDs on Sideband with Segmentation</td>
<td>380</td>
</tr>
<tr>
<td>8-50</td>
<td>Conceptual Illustration of Sideband Multi-module Ordering with Three RxQs</td>
<td>382</td>
</tr>
<tr>
<td>8-51</td>
<td>Example Illustration of a Large MTP Split into Multiple Smaller Encapsulated-MTPs for Transport over Sideband, without Segmentation</td>
<td>384</td>
</tr>
<tr>
<td>8-52</td>
<td>Management Flit NOP Message on Mainband</td>
<td>386</td>
</tr>
<tr>
<td>8-53</td>
<td>Management Transport Credit Return DWORD (CRD) Format on Mainband</td>
<td>386</td>
</tr>
<tr>
<td>8-54</td>
<td>Valid MPM Header Start Locations for Various Flit Formats</td>
<td>388</td>
</tr>
<tr>
<td>8-55</td>
<td>Example Mapping of MPMs and NOPs in Flit of Format 3</td>
<td>389</td>
</tr>
<tr>
<td>8-56</td>
<td>Example Mapping of MPMs and NOPs in Flit of Format 5</td>
<td>389</td>
</tr>
<tr>
<td>8-57</td>
<td>Example MPM Mapping to Management Flit for Format 3 with MPM Rollover to Next Flit</td>
<td>390</td>
</tr>
<tr>
<td>8-58</td>
<td>UDA Overview in Each Chiplet - Illustration</td>
<td>392</td>
</tr>
<tr>
<td>8-59</td>
<td>Vendor-defined Test and Debug UDM</td>
<td>394</td>
</tr>
<tr>
<td>8-60</td>
<td>UCIe-based Chiplet Testing/Debugging at Sort</td>
<td>395</td>
</tr>
<tr>
<td>8-61</td>
<td>UCIe-based Testing of Chiplets in an SiP</td>
<td>396</td>
</tr>
<tr>
<td>8-62</td>
<td>UCIe-based System Testing/Debug</td>
<td>397</td>
</tr>
<tr>
<td>8-63</td>
<td>DMH/DMS Address Mapping</td>
<td>398</td>
</tr>
<tr>
<td>8-64</td>
<td>DMH Capability Register Map</td>
<td>399</td>
</tr>
<tr>
<td>8-65</td>
<td>Empty Spoke Register Map</td>
<td>402</td>
</tr>
<tr>
<td>8-66</td>
<td>Common DMS Registers for All Non-empty Spokes Register Map</td>
<td>403</td>
</tr>
<tr>
<td>8-67</td>
<td>DMS Register Map for UCIe Spoke Types</td>
<td>407</td>
</tr>
<tr>
<td>8-68</td>
<td>DMS Register Map for Vendor-defined Spoke Types</td>
<td>411</td>
</tr>
<tr>
<td>8-69</td>
<td>Early Firmware Download Capability Structure</td>
<td>413</td>
</tr>
<tr>
<td>8-70</td>
<td>Early Firmware Download State Machine</td>
<td>415</td>
</tr>
<tr>
<td>8-71</td>
<td>Example Use of Fast Throttle</td>
<td>419</td>
</tr>
<tr>
<td>8-72</td>
<td>Overview of the Fast Throttle Data Structures</td>
<td>421</td>
</tr>
</table>

<table>
<tr>
<td>8-73</td>
<td>Fast Throttle Trigger Capability Structure</td>
<td>421</td>
</tr>
<tr>
<td>8-74</td>
<td>Fast Throttle Trigger Capability Format</td>
<td>422</td>
</tr>
<tr>
<td>8-75</td>
<td>Fast Throttle Response Capability Structure</td>
<td>424</td>
</tr>
<tr>
<td>8-76</td>
<td>Fast Throttle Response State Format</td>
<td>424</td>
</tr>
<tr>
<td>8-77</td>
<td>Fast Throttle Logging Capability Structure</td>
<td>426</td>
</tr>
<tr>
<td>8-78</td>
<td>Fast Throttle Logging Capability Format</td>
<td>426</td>
</tr>
<tr>
<td>8-79</td>
<td>Fast Throttle Trigger Control Structure</td>
<td>429</td>
</tr>
<tr>
<td>8-80</td>
<td>Fast Throttle Trigger Control Format</td>
<td>429</td>
</tr>
<tr>
<td>8-81</td>
<td>Fast Throttle Trigger Assertion and De-assertion</td>
<td>431</td>
</tr>
<tr>
<td>8-82</td>
<td>Chiplet Fast Throttle Assertion and De-assertion Timing</td>
<td>432</td>
</tr>
<tr>
<td>8-83</td>
<td>Fast Throttle Response Control Structure</td>
<td>432</td>
</tr>
<tr>
<td>8-84</td>
<td>Fast Throttle Logging Control Structure</td>
<td>433</td>
</tr>
<tr>
<td>8-85</td>
<td>Fast Throttle Logging Control Format</td>
<td>433</td>
</tr>
<tr>
<td>8-86</td>
<td>Fast Throttle Logging Structure</td>
<td>435</td>
</tr>
<tr>
<td>8-87</td>
<td>Fast Throttle Address Map</td>
<td>436</td>
</tr>
<tr>
<td>8-88</td>
<td>Example Use of Emergency Shutdown</td>
<td>437</td>
</tr>
<tr>
<td>8-89</td>
<td>Overview of Emergency Shutdown Data Structures</td>
<td>439</td>
</tr>
<tr>
<td>8-90</td>
<td>Emergency Shutdown Trigger Capability Structure</td>
<td>440</td>
</tr>
<tr>
<td>8-91</td>
<td>Emergency Shutdown Trigger Capability Format</td>
<td>440</td>
</tr>
<tr>
<td>8-92</td>
<td>Emergency Shutdown Response Capability Structure</td>
<td>442</td>
</tr>
<tr>
<td>8-93</td>
<td>Emergency Shutdown Response State Format</td>
<td>443</td>
</tr>
<tr>
<td>8-94</td>
<td>Emergency Shutdown Logging Capability Structure</td>
<td>445</td>
</tr>
<tr>
<td>8-95</td>
<td>Emergency Shutdown Logging Capability Format</td>
<td>445</td>
</tr>
<tr>
<td>8-96</td>
<td>Emergency Shutdown Trigger Control Structure</td>
<td>448</td>
</tr>
<tr>
<td>8-97</td>
<td>Emergency Shutdown Trigger Control Format</td>
<td>448</td>
</tr>
<tr>
<td>8-98</td>
<td>Emergency Shutdown Assertion</td>
<td>450</td>
</tr>
<tr>
<td>8-99</td>
<td>Emergency Shutdown Timing Diagram</td>
<td>450</td>
</tr>
<tr>
<td>8-100</td>
<td>Emergency Shutdown Response Control Structure</td>
<td>451</td>
</tr>
<tr>
<td>8-101</td>
<td>Emergency Shutdown Logging Control Structure</td>
<td>452</td>
</tr>
<tr>
<td>8-102</td>
<td>Emergency Shutdown Logging Control Format</td>
<td>452</td>
</tr>
<tr>
<td>8-103</td>
<td>Emergency Shutdown Logging Structure</td>
<td>453</td>
</tr>
<tr>
<td>8-104</td>
<td>Emergency Shutdown Address Map</td>
<td>455</td>
</tr>
<tr>
<td>9-1</td>
<td>Software view Example with Root Ports and Endpoints</td>
<td>459</td>
</tr>
<tr>
<td>9-2</td>
<td>Software view Example with Switch and Endpoints</td>
<td>460</td>
</tr>
<tr>
<td>9-3</td>
<td>Software view Example of UCIe Endpoint</td>
<td>461</td>
</tr>
<tr>
<td>9-4</td>
<td>UCIe Link DVSEC</td>
<td>463</td>
</tr>
<tr>
<td>9-5</td>
<td>UCIe Link Health Monitor (UHM) DVSEC</td>
<td>505</td>
</tr>
<tr>
<td>9-6</td>
<td>UCIe Test/Compliance Register Block</td>
<td>507</td>
</tr>
<tr>
<td>10-1</td>
<td>Example configurations using RDI</td>
<td>522</td>
</tr>
<tr>
<td>10-2</td>
<td>Example Waveform Showing Handling of Level Transition</td>
<td>531</td>
</tr>
<tr>
<td>10-3</td>
<td>Data Transfer from Adapter to Physical Layer</td>
<td>532</td>
</tr>
<tr>
<td>10-4</td>
<td>$I p \_ i r d y \quad a s s e r t i n g$ two cycles before Ip_valid</td>
<td>533</td>
</tr>
<tr>
<td>10-5</td>
<td>lp_irdy asserting at the same cycle as lp_valid</td>
<td>533</td>
</tr>
<tr>
<td>10-6</td>
<td>RDI State Machine</td>
<td>533</td>
</tr>
<tr>
<td>10-7</td>
<td>Example flow of Link bring up on RDI</td>
<td>534</td>
</tr>
<tr>
<td>10-8</td>
<td>Successful PM entry flow</td>
<td>537</td>
</tr>
<tr>
<td>10-9</td>
<td>PM Abort flow</td>
<td>537</td>
</tr>
<tr>
<td>10-10</td>
<td>PM Exit flow</td>
<td>538</td>
</tr>
<tr>
<td>10-11</td>
<td>RDI PM Exit Example Showing Interactions with LTSM</td>
<td>538</td>
</tr>
<tr>
<td>10-12</td>
<td>Example configurations using FDI</td>
<td>539</td>
</tr>
<tr>
<td>10-13</td>
<td>Example Waveform Showing Handling of Level Transition</td>
<td>549</td>
</tr>
<tr>
<td>10-14</td>
<td>Data Transfer from Protocol Layer to Adapter</td>
<td>550</td>
</tr>
<tr>
<td>10-15</td>
<td>Example for pl_flit_cancel for Latency-Optimized Flits</td>
<td></td>
</tr>
<tr>
<td></td>
<td>and CRC Error on First Flit Half</td>
<td>551</td>
</tr>
</table>

<table>
<tr>
<td>10-16</td>
<td>Example for pl_flit_cancel for Latency-Optimized Flits and CRC Error on Second Flit Half</td>
<td>551</td>
</tr>
<tr>
<td>10-17</td>
<td>Example for pl_flit_cancel for Latency-Optimized Flits and CRC Error on Second Flit Half, Alternate Implementation Example</td>
<td>551</td>
</tr>
<tr>
<td>10-18</td>
<td>Example for pl_flit_cancel for Standard 256B Flits</td>
<td>552</td>
</tr>
<tr>
<td>10-19</td>
<td>FDI State Machine</td>
<td>552</td>
</tr>
<tr>
<td>10-20</td>
<td>FDI Bring up flow</td>
<td>554</td>
</tr>
<tr>
<td>10-21</td>
<td>PM Entry example for CXL or PCIe protocols</td>
<td>557</td>
</tr>
<tr>
<td>10-22</td>
<td>PM Entry example for symmetric protocol</td>
<td>557</td>
</tr>
<tr>
<td>10-23</td>
<td>PM Abort Example</td>
<td>558</td>
</tr>
<tr>
<td>10-24</td>
<td>PM Exit Example</td>
<td>558</td>
</tr>
<tr>
<td>10-25</td>
<td>CXL.io Standard 256B Start Header Flit Format Example</td>
<td>559</td>
</tr>
<tr>
<td>10-26</td>
<td>FDI (or RDI) Byte Mapping for 64B Datapath to 256B Flits</td>
<td>560</td>
</tr>
<tr>
<td>10-27</td>
<td>FDI (or RDI) Byte Mapping for 128B Datapath to 256B Flits</td>
<td>560</td>
</tr>
<tr>
<td>10-28</td>
<td>FDI Byte Mapping for 128B Datapath for 68B Flit Format</td>
<td>560</td>
</tr>
<tr>
<td>10-29</td>
<td>RDI Byte Mapping for 128B Datapath for 68B Flit Format</td>
<td>561</td>
</tr>
<tr>
<td>10-30</td>
<td>Example of Byte Transfer on the Rx for One Lane of a Module</td>
<td>574</td>
</tr>
<tr>
<td>10-31</td>
<td>LinkReset Example</td>
<td>575</td>
</tr>
<tr>
<td>10-32</td>
<td>LinkError example</td>
<td>576</td>
</tr>
<tr>
<td>10-33</td>
<td>Example of L2 Cross Product with Retrain on RDI</td>
<td>577</td>
</tr>
<tr>
<td>10-34</td>
<td>L2 Exit Example for RDI</td>
<td>578</td>
</tr>
<tr>
<td>11-1</td>
<td>Examples of Standard and Advanced Package setups for DUT and Golden Die Compliance Testing</td>
<td>580</td>
</tr>
<tr>
<td>B-1</td>
<td>AIB interoperability</td>
<td>585</td>
</tr>
</table>

#### Tables

<table>
<tr>
<td>1</td>
<td>Terms and Definitions</td>
<td>28</td>
</tr>
<tr>
<td>2</td>
<td>Unit of Measure Symbols</td>
<td>36</td>
</tr>
<tr>
<td>3</td>
<td>Reference Documents</td>
<td>37</td>
</tr>
<tr>
<td>4</td>
<td>Revision History</td>
<td>37</td>
</tr>
<tr>
<td>1-1</td>
<td>Characteristics of UCIe on Standard Package</td>
<td>40</td>
</tr>
<tr>
<td>1-2</td>
<td>Characteristics of UCIe on Advanced Package</td>
<td>40</td>
</tr>
<tr>
<td>1-3</td>
<td>Characteristics of UCIe-3D</td>
<td>41</td>
</tr>
<tr>
<td>1-4</td>
<td>UCIe 2D and 2.5D Key Performance Targets</td>
<td>49</td>
</tr>
<tr>
<td>1-5</td>
<td>UCIe-3D Key Performance Targets</td>
<td>49</td>
</tr>
<tr>
<td>1-6</td>
<td>Groups for Different Advanced Package Bump Pitches</td>
<td>50</td>
</tr>
<tr>
<td>2-1</td>
<td>Specification to Protocol Mode Requirements</td>
<td>52</td>
</tr>
<tr>
<td>3-1</td>
<td>Capabilities that Must Be Negotiated between Link Partners</td>
<td>63</td>
</tr>
<tr>
<td>3-2</td>
<td>Flit Header for Format 2 without Retry</td>
<td>72</td>
</tr>
<tr>
<td>3-3</td>
<td>Flit Header for Format 2 with Retry</td>
<td>72</td>
</tr>
<tr>
<td>3-4</td>
<td>Flit Header for Format 3, Format 4, Format 5, and Format 6 without Retry</td>
<td>79</td>
</tr>
<tr>
<td>3-5</td>
<td>Flit Header for Format 3, Format 4, Format 5, and Format 6 with Retry</td>
<td>80</td>
</tr>
<tr>
<td>3-6</td>
<td>Summary of Flit Formats</td>
<td>84</td>
</tr>
<tr>
<td>3-7</td>
<td>Protocol Mapping and Implementation Requirements</td>
<td>85</td>
</tr>
<tr>
<td>3-8</td>
<td>Truth Table for Determining Protocol</td>
<td>86</td>
</tr>
<tr>
<td>3-9</td>
<td>Truth Table 1</td>
<td>88</td>
</tr>
<tr>
<td>3-10</td>
<td>Truth Table 2</td>
<td>88</td>
</tr>
<tr>
<td>4-1</td>
<td>Valid framing for Retimers</td>
<td>101</td>
</tr>
<tr>
<td>4-2</td>
<td>Lane ID: Advanced Package module</td>
<td>105</td>
</tr>
<tr>
<td>4-3</td>
<td>Lane ID: Standard Package Module</td>
<td>106</td>
</tr>
<tr>
<td>4-4</td>
<td>LFSR seed values</td>
<td>121</td>
</tr>
<tr>
<td>4-5</td>
<td>Data-to-Clock Training Parameters</td>
<td>126</td>
</tr>
<tr>
<td>4-6</td>
<td>State Definitions for Initialization</td>
<td>131</td>
</tr>
<tr>
<td>4-7</td>
<td>Per Lane ID Pattern</td>
<td>151</td>
</tr>
<tr>
<td>4-8</td>
<td>Per Lane ID Pattern Examples</td>
<td>152</td>
</tr>
<tr>
<td>4-9</td>
<td>Standard Package Logical Lane Map</td>
<td>155</td>
</tr>
<tr>
<td>4-10</td>
<td>Runtime Link Test Status Register based Retrain encoding</td>
<td>169</td>
</tr>
<tr>
<td>4-11</td>
<td>Retrain encoding</td>
<td>169</td>
</tr>
<tr>
<td>4-12</td>
<td>Retrain exit state resolution</td>
<td>169</td>
</tr>
<tr>
<td>4-13</td>
<td>Messages exchanged that are used to determine resolution for Example 1</td>
<td>179</td>
</tr>
<tr>
<td>4-14</td>
<td>Messages exchanged that are used to determine resolution for Example 2</td>
<td>180</td>
</tr>
<tr>
<td>4-15</td>
<td>Messages exchanged that are used to determine resolution for Example 3</td>
<td>180</td>
</tr>
<tr>
<td rowspan="2">4-16</td>
<td>Capability Register and Link Training Parameter Values</td>
<td></td>
</tr>
<tr>
<td>for RDI Byte-to-Module Assignment Example for x64 Interop with x32</td>
<td>182</td>
</tr>
<tr>
<td>5-1</td>
<td>REFCLK Frequency PPMs and SSC PPMs</td>
<td>185</td>
</tr>
<tr>
<td>5-2</td>
<td>Electrical Summary for 4 GT/s to 32 GT/s</td>
<td>188</td>
</tr>
<tr>
<td>5-3</td>
<td>Electrical Summary for 48 GT/s and 64 GT/s</td>
<td>189</td>
</tr>
<tr>
<td>5-4</td>
<td>Operating Data Rate Ranges for UCIe Link Speed Settings</td>
<td>190</td>
</tr>
<tr>
<td>5-5</td>
<td>Transmitter Electrical Parameters</td>
<td>191</td>
</tr>
<tr>
<td>5-6</td>
<td>Transmitter de-emphasis values</td>
<td>194</td>
</tr>
<tr>
<td>5-7</td>
<td>48 GT/s and 64 GT/s Tx Equalization Coefficient Presets</td>
<td>194</td>
</tr>
<tr>
<td>5-8</td>
<td>Receiver Electrical Parameters for &lt;= 32 GT/s</td>
<td>196</td>
</tr>
<tr>
<td>5-9</td>
<td>Receiver Electrical Parameters for 48 GT/s and 64 GT/s</td>
<td>197</td>
</tr>
<tr>
<td>5-10</td>
<td>Maximum channel reach for unterminated Receiver (Tx = 0.4 V)</td>
<td>197</td>
</tr>
<tr>
<td>5-11</td>
<td>Maximum Channel reach for unterminated Receiver $\left( T X \quad s w i n g = 0 . 8 5 V \right)$</td>
<td>199</td>
</tr>
</table>

<table>
<tr>
<th colspan="2"></th>
<th>Tables</th>
</tr>
<tr>
<td>5-12</td>
<td>Forwarded Clock Frequency and Phase</td>
<td>203</td>
</tr>
<tr>
<td>5-13</td>
<td>I/Q Correction for 48 GT/s and 64 GT/s</td>
<td>203</td>
</tr>
<tr>
<td>5-14</td>
<td>I/O Noise and Clock Skew</td>
<td>205</td>
</tr>
<tr>
<td>5-15</td>
<td>Rectangular Eye Mask Requirements for &lt;= 32 GT/s</td>
<td>206</td>
</tr>
<tr>
<td>5-16</td>
<td>Channel Matching Tolerance of Tx or Rx within a Module</td>
<td>208</td>
</tr>
<tr>
<td>5-17</td>
<td>Channel Characteristics</td>
<td>209</td>
</tr>
<tr>
<td>5-18</td>
<td>x64 Advanced Package Module Signal List</td>
<td>209</td>
</tr>
<tr>
<td>5-19</td>
<td>Bump Map Options and the Recommended Bump Pitch Range and Corresponding Max Speed</td>
<td>215</td>
</tr>
<tr>
<td>5-20</td>
<td>Maximum Systematic Lane-to-lane Length Mismatch in um between the Reference Bump Maps in the Implementation Note</td>
<td>224</td>
</tr>
<tr>
<td>5-21</td>
<td>x64 and x32 Advanced Package Connectivity Matrix</td>
<td>229</td>
</tr>
<tr>
<td>5-22</td>
<td>Summary of Advanced Package Module Connection Combinations with Same Number of Modules on Both Sides</td>
<td>233</td>
</tr>
<tr>
<td>5-23</td>
<td>Summary of Advanced Package Module Connection Combinations with Different Number of Modules on Both Sides</td>
<td>234</td>
</tr>
<tr>
<td>5-24</td>
<td>IL and Crosstalk for Standard Package: With Receiver Termination Enabled</td>
<td>235</td>
</tr>
<tr>
<td>5-25</td>
<td>IL and Crosstalk for Standard Package: No Rx Termination</td>
<td>235</td>
</tr>
<tr>
<td>5-26</td>
<td>Standard Package Module Signal List</td>
<td>235</td>
</tr>
<tr>
<td>5-27</td>
<td>Summary of Standard Package Module Connection Combinations with Same Number of Modules on Both Sides</td>
<td>243</td>
</tr>
<tr>
<td>$5 - 2 8$</td>
<td>Summary of Standard Package Module Connection Combinations with Different Number of Modules on Both Sides</td>
<td>246</td>
</tr>
<tr>
<td>5-29</td>
<td>Summary of Degraded Links when Standard Package Module-pairs Fail</td>
<td>247</td>
</tr>
<tr>
<td>5-30</td>
<td>Tightly Coupled Mode: Eye Mask</td>
<td>249</td>
</tr>
<tr>
<td>5-31</td>
<td>Tightly Coupled Mode Channel for Advanced Package</td>
<td>249</td>
</tr>
<tr>
<td>5-32</td>
<td>Raw BER Requirements</td>
<td>251</td>
</tr>
<tr>
<td>5-33</td>
<td>Sideband Parameters summary</td>
<td>254</td>
</tr>
<tr>
<td>5-34</td>
<td>AUXCLK Frequency Parameters</td>
<td>255</td>
</tr>
<tr>
<td>5-35</td>
<td>Open Drain Specification Summary</td>
<td>256</td>
</tr>
<tr>
<td>6-1</td>
<td>UCIe-3D Key Performance Indicators</td>
<td>259</td>
</tr>
<tr>
<td>6-2</td>
<td>Timing and Mismatch Specification</td>
<td>261</td>
</tr>
<tr>
<td>6-3</td>
<td>ESD Specification for ≤ 10 um Bump Pitch</td>
<td>264</td>
</tr>
<tr>
<td>6-4</td>
<td>Energy Efficiency Target.</td>
<td>264</td>
</tr>
<tr>
<td>7-1</td>
<td>Sideband Packet Opcode Encodings Mapped to Sideband Packet Types</td>
<td>269</td>
</tr>
<tr>
<td>7-2</td>
<td>FDI sideband: srcid and dstid encodings on FDI</td>
<td>270</td>
</tr>
<tr>
<td>7-3</td>
<td>RDI sideband: srcid and dstid encodings on RDI</td>
<td>270</td>
</tr>
<tr>
<td>7-4</td>
<td>UCIe Link sideband: srcid and dstid encodings for UCIe Link</td>
<td>271</td>
</tr>
<tr>
<td>7-5</td>
<td>Field descriptions for Register Access Requests</td>
<td>272</td>
</tr>
<tr>
<td>7-6</td>
<td>Mapping of Addr[23:0] for Different Requests</td>
<td>273</td>
</tr>
<tr>
<td>7-7</td>
<td>Field Descriptions for a Completion</td>
<td>274</td>
</tr>
<tr>
<td>7-8</td>
<td>Message Encodings for Messages without Data</td>
<td>275</td>
</tr>
<tr>
<td>7-9</td>
<td>Link Training State Machine related Message encodings for messages without data</td>
<td>278</td>
</tr>
<tr>
<td>7-10</td>
<td>Message encodings for Messages with Data</td>
<td>283</td>
</tr>
<tr>
<td>7-11</td>
<td>Link Training State Machine related encodings</td>
<td>285</td>
</tr>
<tr>
<td>7-12</td>
<td>Supported MPM with Data Messages on Sideband</td>
<td>291</td>
</tr>
<tr>
<td>7-13</td>
<td>Common Fields in MPM Header of all MPM with Data Messages on Sideband</td>
<td>291</td>
</tr>
<tr>
<td>7-14</td>
<td>Encapsulated MTP on Sideband Fields</td>
<td>292</td>
</tr>
<tr>
<td>7-15</td>
<td>Vendor-defined Management Port Gateway Message with Data on Sideband Fields</td>
<td>293</td>
</tr>
<tr>
<td>7-16</td>
<td>Supported MPM without Data Messages on Sideband</td>
<td>293</td>
</tr>
<tr>
<td>7-17</td>
<td>Common Fields in MPM Header of all MPM without Data Messages on Sideband</td>
<td>294</td>
</tr>
<tr>
<td>7-18</td>
<td>Management Port Gateway Capabilities MPM Header Fields on Sideband</td>
<td>294</td>
</tr>
<tr>
<td>UCIe Specification</td>
<td>Revision 3.0, Version 1.0</td>
<td>23</td>
</tr>
</table>

<table>
<tr>
<td>7-19</td>
<td>Credit Return MPM Header Fields on Sideband</td>
<td>295</td>
</tr>
<tr>
<td>7-20</td>
<td>Init Done MPM Header Fields on Sideband</td>
<td>296</td>
</tr>
<tr>
<td>7-21</td>
<td>PM MPM Header Fields on Sideband</td>
<td>296</td>
</tr>
<tr>
<td>7-22</td>
<td>MPM Header Vendor-defined Management Port Gateway Message without Data on Sideband</td>
<td>297</td>
</tr>
<tr>
<td>8-1</td>
<td>UCIe Management Transport Packet Fields</td>
<td>308</td>
</tr>
<tr>
<td>8-2</td>
<td>Traffic Class Characteristics</td>
<td>310</td>
</tr>
<tr>
<td>8-3</td>
<td>Management Protocol IDs</td>
<td>312</td>
</tr>
<tr>
<td>8-4</td>
<td>Management Protocol use of Access Control Mechanism</td>
<td>316</td>
</tr>
<tr>
<td>8-5</td>
<td>Asset Types</td>
<td>319</td>
</tr>
<tr>
<td>8-6</td>
<td>Asset Contexts</td>
<td>319</td>
</tr>
<tr>
<td>8-7</td>
<td>Standard Security Asset Classes</td>
<td>319</td>
</tr>
<tr>
<td>8-8</td>
<td>UCIe-defined Management Capability IDs</td>
<td>322</td>
</tr>
<tr>
<td>8-9</td>
<td>Management Capability Directory Fields</td>
<td>324</td>
</tr>
<tr>
<td>8-10</td>
<td>Capability Pointer Fields</td>
<td>324</td>
</tr>
<tr>
<td>8-11</td>
<td>Chiplet Capability Structure Fields</td>
<td>326</td>
</tr>
<tr>
<td>8-12</td>
<td>Management Port Structure Fields</td>
<td>328</td>
</tr>
<tr>
<td>8-13</td>
<td>Route Entry Fields</td>
<td>333</td>
</tr>
<tr>
<td>8-14</td>
<td>Access Control Capability Structure Fields</td>
<td>335</td>
</tr>
<tr>
<td>8-15</td>
<td>Read Access Control (RAC) Structure Field Description</td>
<td>338</td>
</tr>
<tr>
<td>8-16</td>
<td>Write Access Control (WAC) Structure Field Description</td>
<td>339</td>
</tr>
<tr>
<td>8-17</td>
<td>Security Clearance Group Capability Structure Fields</td>
<td>340</td>
</tr>
<tr>
<td>8-18</td>
<td>Security Clearance Group Context Fields</td>
<td>341</td>
</tr>
<tr>
<td>8-19</td>
<td>UCIe Memory Access Request Packet Fields</td>
<td>343</td>
</tr>
<tr>
<td>8-20</td>
<td>UCIe Memory Access Response Packet Fields</td>
<td>346</td>
</tr>
<tr>
<td>8-21</td>
<td>UCIe Memory Access Protocol Capability Structure Fields</td>
<td>347</td>
</tr>
<tr>
<td>8-22</td>
<td>CB_CAPABILITIES Circular Buffer Capabilities</td>
<td>352</td>
</tr>
<tr>
<td>8-23</td>
<td>CB_STATE Field Value and Definitions</td>
<td>353</td>
</tr>
<tr>
<td>8-24</td>
<td>CB_ERROR_BITS - Error Vector</td>
<td>353</td>
</tr>
<tr>
<td>8-25</td>
<td>CB_ERROR Values Definitions</td>
<td>353</td>
</tr>
<tr>
<td>8-26</td>
<td>CB_VENDOR_DEFINED_ERROR_STATUS Value Definitions</td>
<td>354</td>
</tr>
<tr>
<td>8-27</td>
<td>CB_CONTROL - Control Register Bit Definition</td>
<td>355</td>
</tr>
<tr>
<td>8-28</td>
<td>Sink and Source Circular Buffer Structure Fields</td>
<td>355</td>
</tr>
<tr>
<td>8-29</td>
<td>Sink Circular Buffer Structure Fields</td>
<td>357</td>
</tr>
<tr>
<td>8-30</td>
<td>Source Circular Buffer Structure Fields</td>
<td>358</td>
</tr>
<tr>
<td>8-31</td>
<td>Open Drain Detection Capability Structure Fields</td>
<td>360</td>
</tr>
<tr>
<td>8-32</td>
<td>MPM Opcodes on Mainband</td>
<td>366</td>
</tr>
<tr>
<td>8-33</td>
<td>Supported MPM with Data Messages on Mainband</td>
<td>366</td>
</tr>
<tr>
<td>8-34</td>
<td>Common Fields in MPM Header of all MPM with Data Messages on Mainband</td>
<td>366</td>
</tr>
<tr>
<td>8-35</td>
<td>Encapsulated MTP on Mainband Fields</td>
<td>367</td>
</tr>
<tr>
<td>8-36</td>
<td>Vendor-defined Management Port Gateway Message with Data on Mainband Fields</td>
<td>368</td>
</tr>
<tr>
<td>8-37</td>
<td>Supported MPM without Data Messages on Mainband</td>
<td>368</td>
</tr>
<tr>
<td>8-38</td>
<td>Common Fields in MPM Header of all MPM without Data Messages on Mainband</td>
<td>369</td>
</tr>
<tr>
<td>8-39</td>
<td>Management Port Gateway Capabilities MPM Header Fields on Mainband</td>
<td>369</td>
</tr>
<tr>
<td>8-40</td>
<td>Init Done MPM Header Fields on Mainband</td>
<td>370</td>
</tr>
<tr>
<td>8-41</td>
<td>MPM Header Vendor-defined Management Port Gateway Message without Data on Mainband</td>
<td>371</td>
</tr>
<tr>
<td>8-42</td>
<td>Version</td>
<td>399</td>
</tr>
<tr>
<td>8-43</td>
<td>Capability ID, Ver</td>
<td>399</td>
</tr>
<tr>
<td>8-44</td>
<td>Debug Capability</td>
<td>400</td>
</tr>
<tr>
<td>8-45</td>
<td>Debug Control</td>
<td>400</td>
</tr>
<tr>
<td>8-46</td>
<td>Debug Status</td>
<td>400</td>
</tr>
<tr>
<td>8-47</td>
<td>DMH_Length_Low</td>
<td>400</td>
</tr>
</table>

<table>
<tr>
<td>8-48</td>
<td>DMH_Length_High</td>
<td>400</td>
</tr>
<tr>
<td>8-49</td>
<td>DMH Extended Capability Pointer Low</td>
<td>401</td>
</tr>
<tr>
<td>8-50</td>
<td>DMH Extended Capability Pointer High</td>
<td>401</td>
</tr>
<tr>
<td>8-51</td>
<td>DMS_Starting_Low</td>
<td>401</td>
</tr>
<tr>
<td>8-52</td>
<td>DMS_Starting_High</td>
<td>401</td>
</tr>
<tr>
<td>8-53</td>
<td>DMS_Next_Low Address</td>
<td>402</td>
</tr>
<tr>
<td>8-54</td>
<td>DMS_Next_High Address</td>
<td>402</td>
</tr>
<tr>
<td>8-55</td>
<td>Spoke Vendor ID</td>
<td>403</td>
</tr>
<tr>
<td>8-56</td>
<td>Spoke Device ID</td>
<td>403</td>
</tr>
<tr>
<td>8-57</td>
<td>DMS_Next_Low Address</td>
<td>404</td>
</tr>
<tr>
<td>8-58</td>
<td>DMS_Next_High Address</td>
<td>404</td>
</tr>
<tr>
<td>8-59</td>
<td>Spoke Revision ID</td>
<td>404</td>
</tr>
<tr>
<td>8-60</td>
<td>DMS-ID</td>
<td>404</td>
</tr>
<tr>
<td>8-61</td>
<td>Associated DMS-ID[0, 1, 2]</td>
<td>404</td>
</tr>
<tr>
<td>8-62</td>
<td>Spoke Capability</td>
<td>405</td>
</tr>
<tr>
<td>8-63</td>
<td>Spoke Control</td>
<td>405</td>
</tr>
<tr>
<td>8-64</td>
<td>Spoke Status</td>
<td>405</td>
</tr>
<tr>
<td>8-65</td>
<td>DMS Register Space Length Low</td>
<td>406</td>
</tr>
<tr>
<td>8-66</td>
<td>DMS Register Space Length High</td>
<td>406</td>
</tr>
<tr>
<td>8-67</td>
<td>DMS Extended Capability Pointer Low</td>
<td>406</td>
</tr>
<tr>
<td>8-68</td>
<td>DMS Extended Capability Pointer High</td>
<td>406</td>
</tr>
<tr>
<td>8-69</td>
<td>Port ID</td>
<td>408</td>
</tr>
<tr>
<td>8-70</td>
<td>Adapter_Physical_Layer_Ptr_Low</td>
<td>408</td>
</tr>
<tr>
<td>8-71</td>
<td>Adapter_Physical_Layer_Ptr_High</td>
<td>408</td>
</tr>
<tr>
<td>8-72</td>
<td>Compliance_Test_Ptr_Low</td>
<td>409</td>
</tr>
<tr>
<td>8-73</td>
<td>Compliance_Test_Ptr_High</td>
<td>409</td>
</tr>
<tr>
<td>8-74</td>
<td>Impl_Spec_Adapter_Ptr_Low</td>
<td>410</td>
</tr>
<tr>
<td>8-75</td>
<td>Impl_Spec_Adapter_Ptr_High</td>
<td>410</td>
</tr>
<tr>
<td>8-76</td>
<td>Impl_Spec_Physical_Layer_Ptr_Low</td>
<td>410</td>
</tr>
<tr>
<td>8-77</td>
<td>Impl_Spec_Physical_Layer_Ptr_High</td>
<td>410</td>
</tr>
<tr>
<td>8-78</td>
<td>Early Firmware Download Capability Structure Fields</td>
<td>414</td>
</tr>
<tr>
<td>8-79</td>
<td>EFD_STATE Field Values Definition</td>
<td>415</td>
</tr>
<tr>
<td>8-80</td>
<td>EFD_ERROR Field Value Definitions</td>
<td>416</td>
</tr>
<tr>
<td>8-81</td>
<td>EFD_VENDOR_DEFINED_ERROR_STATUS Value Definitions</td>
<td>416</td>
</tr>
<tr>
<td>8-82</td>
<td>EFD_CAPABILITIES Bit Definition</td>
<td>416</td>
</tr>
<tr>
<td>8-83</td>
<td>EFD_CONTROL - Early Firmware Download Capability Control Bit Definition</td>
<td>417</td>
</tr>
<tr>
<td>8-84</td>
<td>Fast Throttle Trigger Capability Structure Fields</td>
<td>422</td>
</tr>
<tr>
<td>8-85</td>
<td>Fast Throttle Trigger Capability Format</td>
<td>423</td>
</tr>
<tr>
<td>8-86</td>
<td>Fast Throttle Trigger Type Encoding</td>
<td>423</td>
</tr>
<tr>
<td>8-87</td>
<td>Fast Throttle Response Capability Structure Fields</td>
<td>424</td>
</tr>
<tr>
<td>8-88</td>
<td>Fast Throttle Response State Format</td>
<td>425</td>
</tr>
<tr>
<td>8-89</td>
<td>Fast Throttle Logging Capability Fields</td>
<td>426</td>
</tr>
<tr>
<td>8-90</td>
<td>Fast Throttle Logging Capability Format</td>
<td>427</td>
</tr>
<tr>
<td>8-91</td>
<td>Fast Throttle Logging Capability Types</td>
<td>428</td>
</tr>
<tr>
<td>8-92</td>
<td>Fast Throttle Trigger Control Fields</td>
<td>430</td>
</tr>
<tr>
<td>8-93</td>
<td>Fast Throttle Trigger Control Format</td>
<td>430</td>
</tr>
<tr>
<td>8-94</td>
<td>Fast Throttle Threshold Encoding ID</td>
<td>431</td>
</tr>
<tr>
<td>8-95</td>
<td>Fast Throttle Response Control Fields</td>
<td>433</td>
</tr>
<tr>
<td>8-96</td>
<td>Fast Throttle Logging Control Fields</td>
<td>434</td>
</tr>
<tr>
<td>8-97</td>
<td>Fast Throttle Logging Control Format</td>
<td>434</td>
</tr>
<tr>
<td>8-98</td>
<td>Fast Throttle Logging Fields</td>
<td>435</td>
</tr>
<tr>
<td>8-99</td>
<td>Emergency Shutdown Trigger Capability Structure Fields</td>
<td>440</td>
</tr>
<tr>
<td>8-100</td>
<td>Emergency Shutdown Trigger Capability Format</td>
<td>441</td>
</tr>
<tr>
<td>8-101</td>
<td>Emergency Shutdown Trigger Type Encoding</td>
<td>442</td>
</tr>
<tr>
<td>8-102</td>
<td>Emergency Shutdown Response Capability Structure Fields</td>
<td>443</td>
</tr>
</table>

<table>
<tr>
<th colspan="2"></th>
<th>Tables</th>
</tr>
<tr>
<td>8-103</td>
<td>Emergency Shutdown Response State Format</td>
<td>444</td>
</tr>
<tr>
<td>8-104</td>
<td>Emergency Shutdown Logging Capability Fields</td>
<td>446</td>
</tr>
<tr>
<td>8-105</td>
<td>Emergency Shutdown Logging Capability Format</td>
<td>446</td>
</tr>
<tr>
<td>8-106</td>
<td>Emergency Shutdown Logging Capability Types</td>
<td>447</td>
</tr>
<tr>
<td>8-107</td>
<td>Emergency Shutdown Trigger Control Fields</td>
<td>449</td>
</tr>
<tr>
<td>8-108</td>
<td>Emergency Shutdown Trigger Control Format</td>
<td>449</td>
</tr>
<tr>
<td>8-109</td>
<td>Emergency Shutdown Threshold Encoding ID</td>
<td>450</td>
</tr>
<tr>
<td>8-110</td>
<td>Emergency Shutdown Response Control Fields</td>
<td>451</td>
</tr>
<tr>
<td>8-111</td>
<td>Emergency Shutdown Logging Control Fields</td>
<td>452</td>
</tr>
<tr>
<td>8-112</td>
<td>Emergency Shutdown Logging Control Format</td>
<td>453</td>
</tr>
<tr>
<td>8-113</td>
<td>Emergency Shutdown Logging Fields</td>
<td>454</td>
</tr>
<tr>
<td>9-1</td>
<td>Software view of Upstream and Downstream Device at UCIe interface</td>
<td>456</td>
</tr>
<tr>
<td>9-2</td>
<td>SW discovery of UCIe Links</td>
<td>457</td>
</tr>
<tr>
<td>9-3</td>
<td>Summary of location of various UCIe Link related registers</td>
<td>458</td>
</tr>
<tr>
<td>9-4</td>
<td>Register Attributes</td>
<td>462</td>
</tr>
<tr>
<td>9-5</td>
<td>UCIe Link DVSEC - PCI Express Extended Capability Header</td>
<td>464</td>
</tr>
<tr>
<td>9-6</td>
<td>UCIe Link DVSEC - Designated Vendor Specific Header 1, 2</td>
<td>464</td>
</tr>
<tr>
<td>9-7</td>
<td>UCIe Link DVSEC - Capability Descriptor</td>
<td>465</td>
</tr>
<tr>
<td>9-8</td>
<td>UCIe Link DVSEC - UCIe Link Capability</td>
<td>466</td>
</tr>
<tr>
<td>9-9</td>
<td>UCIe Link DVSEC - UCIe Link Control</td>
<td>468</td>
</tr>
<tr>
<td>9-10</td>
<td>UCIe Link DVSEC - UCIe Link Status</td>
<td>470</td>
</tr>
<tr>
<td>9-11</td>
<td>UCIe Link DVSEC - Link Event Notification Control</td>
<td>472</td>
</tr>
<tr>
<td>9-12</td>
<td>UCIe Link DVSEC - Error Notification Control</td>
<td>473</td>
</tr>
<tr>
<td>9-13</td>
<td>UCIe Link DVSEC - Register Locator 0, 1, 2, 3 Low</td>
<td>476</td>
</tr>
<tr>
<td>9-14</td>
<td>UCIe Link DVSEC - Register Locator 0, 1, 2, 3 High</td>
<td>477</td>
</tr>
<tr>
<td>9-15</td>
<td>UCIe Link DVSEC - Sideband Mailbox Index Low</td>
<td>477</td>
</tr>
<tr>
<td>9-16</td>
<td>UCIe Link DVSEC - Sideband Mailbox Index High</td>
<td>478</td>
</tr>
<tr>
<td>9-17</td>
<td>UCIe Link DVSEC - Sideband Mailbox Data Low</td>
<td>478</td>
</tr>
<tr>
<td>9-18</td>
<td>UCIe Link DVSEC - Sideband Mailbox Data High</td>
<td>478</td>
</tr>
<tr>
<td>9-19</td>
<td>UCIe Link DVSEC - Sideband Mailbox Control</td>
<td>479</td>
</tr>
<tr>
<td>9-20</td>
<td>UCIe Link DVSEC - Sideband Mailbox Status</td>
<td>479</td>
</tr>
<tr>
<td>9-21</td>
<td>UCIe Link DVSEC - Requester ID</td>
<td>479</td>
</tr>
<tr>
<td>9-22</td>
<td>UCIe Link DVSEC - Associated Port Numbers</td>
<td>480</td>
</tr>
<tr>
<td>9-23</td>
<td>UiSRB DVSEC - PCI Express Extended Capability Header</td>
<td>480</td>
</tr>
<tr>
<td>9-24</td>
<td>UiSRB DVSEC - Designated Vendor Specific Header 1, 2</td>
<td>481</td>
</tr>
<tr>
<td>9-25</td>
<td>UiSRB DVSEC - UiSRB Base Address</td>
<td>481</td>
</tr>
<tr>
<td>9-26</td>
<td>D2D/PHY Register Block - UCIe Register Block Header (Offset 0h)</td>
<td>482</td>
</tr>
<tr>
<td>9-27</td>
<td>Uncorrectable Error Status Register</td>
<td>482</td>
</tr>
<tr>
<td>9-28</td>
<td>Uncorrectable Error Mask Register</td>
<td>483</td>
</tr>
<tr>
<td>9-29</td>
<td>Uncorrectable Error Severity Register</td>
<td>484</td>
</tr>
<tr>
<td>9-30</td>
<td>Correctable Error Status Register</td>
<td>484</td>
</tr>
<tr>
<td>9-31</td>
<td>Correctable Error Mask Register</td>
<td>485</td>
</tr>
<tr>
<td>9-32</td>
<td>Header Log 1 Register</td>
<td>485</td>
</tr>
<tr>
<td>9-33</td>
<td>Header Log 2 Register</td>
<td>486</td>
</tr>
<tr>
<td>9-34</td>
<td>Error and Link Testing Control Register</td>
<td>488</td>
</tr>
<tr>
<td>9-35</td>
<td>Runtime Link Testing Parity Log 0 Register</td>
<td>489</td>
</tr>
<tr>
<td>9-36</td>
<td>Runtime Link Testing Parity Log 1 Register</td>
<td>489</td>
</tr>
<tr>
<td>9-37</td>
<td>Runtime Link Testing Parity Log 2 Register</td>
<td>489</td>
</tr>
<tr>
<td>9-38</td>
<td>Runtime Link Testing Parity Log 3 Register</td>
<td>489</td>
</tr>
<tr>
<td>9-39</td>
<td>Advertised Adapter Capability Log Register</td>
<td>490</td>
</tr>
<tr>
<td>9-40</td>
<td>Finalized Adapter Capability Log Register</td>
<td>490</td>
</tr>
<tr>
<td>9-41</td>
<td>Advertised CXL Capability Log Register</td>
<td>490</td>
</tr>
<tr>
<td>9-42</td>
<td>Finalized CXL Capability Log Register</td>
<td>490</td>
</tr>
<tr>
<td>9-43</td>
<td>Advertised Multi-Protocol Capability Log Register</td>
<td>490</td>
</tr>
</table>

<table>
<tr>
<th colspan="2"></th>
<th>Tables</th>
</tr>
<tr>
<td>9-44</td>
<td>Finalized Multi-Protocol Capability Log Register</td>
<td>491</td>
</tr>
<tr>
<td>9-45</td>
<td>Advertised CXL Capability Log Register for Stack 1</td>
<td>491</td>
</tr>
<tr>
<td>9-46</td>
<td>Finalized CXL Capability Log Register for Stack 1</td>
<td>491</td>
</tr>
<tr>
<td>9-47</td>
<td>Physical Layer Capability Register</td>
<td>492</td>
</tr>
<tr>
<td>9-48</td>
<td>Physical Layer Control Register</td>
<td>493</td>
</tr>
<tr>
<td>9-49</td>
<td>Physical Layer Status Register</td>
<td>495</td>
</tr>
<tr>
<td>9-50</td>
<td>Phy Init and Debug Register</td>
<td>496</td>
</tr>
<tr>
<td>9-51</td>
<td>Training Setup 1 Register</td>
<td>497</td>
</tr>
<tr>
<td>9-52</td>
<td>Training Setup 2 Register</td>
<td>497</td>
</tr>
<tr>
<td>9-53</td>
<td>Training Setup 3 Register</td>
<td>498</td>
</tr>
<tr>
<td>9-54</td>
<td>Training Setup 4 Register</td>
<td>498</td>
</tr>
<tr>
<td>9-55</td>
<td>Current Lane Map Module 0 Register</td>
<td>499</td>
</tr>
<tr>
<td>9-56</td>
<td>Current Lane Map Module 1 Register</td>
<td>499</td>
</tr>
<tr>
<td>9-57</td>
<td>Current Lane Map Module 2 Register</td>
<td>499</td>
</tr>
<tr>
<td>9-58</td>
<td>Current Lane Map Module 3 Register</td>
<td>499</td>
</tr>
<tr>
<td>9-59</td>
<td>Error Log 0 Register</td>
<td>500</td>
</tr>
<tr>
<td>9-60</td>
<td>Error Log 1 Register</td>
<td>501</td>
</tr>
<tr>
<td>9-61</td>
<td>Runtime Link Test Control</td>
<td>501</td>
</tr>
<tr>
<td>9-62</td>
<td>Runtime Link Test Status Register</td>
<td>503</td>
</tr>
<tr>
<td>9-63</td>
<td>Mainband Data Repair Register</td>
<td>503</td>
</tr>
<tr>
<td>9-64</td>
<td>Clock, Track, Valid and Sideband Repair Register</td>
<td>504</td>
</tr>
<tr>
<td>9-65</td>
<td>UHM DVSEC - Designated Vendor Specific Header 1, 2 (Offsets 04h and 08h)</td>
<td>506</td>
</tr>
<tr>
<td>9-66</td>
<td>UHM Status</td>
<td>506</td>
</tr>
<tr>
<td>9-67</td>
<td>EML_Lnx_Mody</td>
<td>506</td>
</tr>
<tr>
<td>9-68</td>
<td>EMR_Lnx_Mody</td>
<td>506</td>
</tr>
<tr>
<td>9-69</td>
<td>UCIe Register Block Header (Offset 0h)</td>
<td>507</td>
</tr>
<tr>
<td>9-70</td>
<td>D2D Adapter Test/Compliance Register Block Offset (Offset 10h)</td>
<td>508</td>
</tr>
<tr>
<td>9-71</td>
<td>PHY Test/Compliance Register Block Offset (Offset 14h)</td>
<td>508</td>
</tr>
<tr>
<td>9-72</td>
<td>Adapter Compliance Control (Offset 20h from D2DOFF)</td>
<td>509</td>
</tr>
<tr>
<td>9-73</td>
<td>Flit Tx Injection Control (Offset 28h from D2DOFF)</td>
<td>509</td>
</tr>
<tr>
<td>9-74</td>
<td>Adapter Test Status</td>
<td>511</td>
</tr>
<tr>
<td>9-75</td>
<td>Link State Injection Control Stack 0</td>
<td>512</td>
</tr>
<tr>
<td>9-76</td>
<td>Link State Injection Control Stack 1</td>
<td>512</td>
</tr>
<tr>
<td>9-77</td>
<td>Retry Injection Control</td>
<td>513</td>
</tr>
<tr>
<td>9-78</td>
<td>Physical Layer Compliance Control 1</td>
<td>514</td>
</tr>
<tr>
<td>9-79</td>
<td>Physical Layer Compliance Control 2</td>
<td>516</td>
</tr>
<tr>
<td>9-80</td>
<td>Physical Layer Compliance Status 1</td>
<td>517</td>
</tr>
<tr>
<td>9-81</td>
<td>Physical Layer Compliance Status 2</td>
<td>518</td>
</tr>
<tr>
<td>9-82</td>
<td>Physical Layer Compliance Status 3</td>
<td>518</td>
</tr>
<tr>
<td>9-83</td>
<td>UEDT Header</td>
<td>520</td>
</tr>
<tr>
<td>9-84</td>
<td>UCIe Link Structure (UCLS)</td>
<td>520</td>
</tr>
<tr>
<td>10-1</td>
<td>RDI signal list</td>
<td>522</td>
</tr>
<tr>
<td>10-2</td>
<td>RDI Config interface extensions for Management Transport</td>
<td>527</td>
</tr>
<tr>
<td>10-3</td>
<td>FDI signal list</td>
<td>540</td>
</tr>
<tr>
<td>$1 0 - 4$</td>
<td>Requests Considered in Each State by Lower Layer</td>
<td>565</td>
</tr>
<tr>
<td>$\begin{array}{} { 1 0 - 5 } \\ { 1 0 - 6 } \end{array}$</td>
<td>Mapping of Vendor-defined Bits that Use TXVLD/RXVLD Encodings</td>
<td>572</td>
</tr>
<tr>
<td></td>
<td>Example Configurations and Widths</td>
<td>573</td>
</tr>
<tr>
<td>$\begin{array}{} { A - 1 } \\ { A - 2 } \end{array}$</td>
<td>CXL Registers for UCIe devices</td>
<td>582</td>
</tr>
<tr>
<td></td>
<td>PCIe Registers for UCIe devices</td>
<td>583</td>
</tr>
<tr>
<td>B-1</td>
<td>AIB 2.0 Datapath mapping for Advanced Package</td>
<td>586</td>
</tr>
<tr>
<td>B-2</td>
<td>AIB 1.0 Datapath mapping for Advanced Package</td>
<td>586</td>
</tr>
</table>

## Terminology

<table>
<caption>Table 1. Terms and Definitions (Sheet 1 of 8)</caption>
<tr>
<th>Term</th>
<th>Definition</th>
</tr>
<tr>
<td>Ack</td>
<td>Acknowledge</td>
</tr>
<tr>
<td>ACPI</td>
<td>Advanced Configuration and Power Interface</td>
</tr>
<tr>
<td>Addr</td>
<td>Address</td>
</tr>
<tr>
<td>Advanced Package</td>
<td>This packaging technology is used for performance optimized applications and short reach interconnects.</td>
</tr>
<tr>
<td>AFE</td>
<td>Analog Front End</td>
</tr>
<tr>
<td>ALMP</td>
<td>ARB/MUX Link Management Packet (as defined in CXL Specification)</td>
</tr>
<tr>
<td>APMW</td>
<td>Advanced Package Module Width</td>
</tr>
<tr>
<td>ARB/MUX</td>
<td>Arbiter/Multiplexer (as defined in CXL Specification)</td>
</tr>
<tr>
<td>Asset</td>
<td>Any data or mechanism used to access data that should be protected from illicit access, use, availability, disclosure, alteration, destruction, or theft.</td>
</tr>
<tr>
<td>ATE</td>
<td>Automated Test Equipment</td>
</tr>
<tr>
<td>B2B</td>
<td>Back-to-Back</td>
</tr>
<tr>
<td>BAR</td>
<td>Base Address Register</td>
</tr>
<tr>
<td>BDF</td>
<td>Bus Device Function</td>
</tr>
<tr>
<td>BE</td>
<td>Byte Enable</td>
</tr>
<tr>
<td>BEI</td>
<td>BAR Equivalent Indicator</td>
</tr>
<tr>
<td>BER</td>
<td>Bit Error Ratio</td>
</tr>
<tr>
<td>BFM</td>
<td>Bus Functional Model</td>
</tr>
<tr>
<td>bubble</td>
<td>Gap in data transfer and/or signal transitions. Measured in number of clock cycles.</td>
</tr>
<tr>
<td>bundle</td>
<td>Tx group or Rx group for UCIe-3D interconnects that contains data, clock, power, and ground. A 3D Module consists of a Tx bundle and an Rx bundle.</td>
</tr>
<tr>
<td>C4 bump</td>
<td>Controller Collapse Chip Connect bump</td>
</tr>
<tr>
<td>$\mathrm { C A }$</td>
<td>Completer Abort</td>
</tr>
<tr>
<td>CB</td>
<td>$C i r c u l a r \quad B u f f e r$</td>
</tr>
<tr>
<td>CDM</td>
<td>Charged Device Model</td>
</tr>
<tr>
<td>chiplet</td>
<td>Integrated circuit die that contains a well-defined subset of functionality that is designed to be combined with other chiplets in a package.</td>
</tr>
<tr>
<td>clear cleared</td>
<td>If clear or reset is used and no value is provided for a bit, it is interpreted as 0b.</td>
</tr>
<tr>
<td>CLM</td>
<td>Current Lane Map</td>
</tr>
<tr>
<td>CMLS</td>
<td>Common Maximum Link Speed</td>
</tr>
<tr>
<td>CMPS</td>
<td>Configured Maximum Packet Size</td>
</tr>
<tr>
<td>CoWoS</td>
<td>Chip on Wafer on Substrate</td>
</tr>
<tr>
<td>CPU</td>
<td>Central Processing Unit</td>
</tr>
<tr>
<td>CRC</td>
<td>Cyclic Redundancy Check</td>
</tr>
<tr>
<td>CXL</td>
<td>Compute eXpress Link</td>
</tr>
<tr>
<td>$C X L \quad 6 8 B \quad F l i t \quad M o d e$</td>
<td>This term is used to reference 68B Flit Mode related Protocol features defined in CXL Specification.</td>
</tr>
<tr>
<td>CXL 256B Flit Mode</td>
<td>This term is used to reference 256B Flit Mode related Protocol features defined in CXL Specification.</td>
</tr>
<tr>
<td>D2C</td>
<td>Data-to-Clock</td>
</tr>
</table>

<table>
<caption>Table 1. Terms and Definitions (Sheet 2 of 8)</caption>
<tr>
<th>Term</th>
<th>Definition</th>
</tr>
<tr>
<td>D2D</td>
<td>Die-to-Die</td>
</tr>
<tr>
<td>DCC</td>
<td>Duty Cycle Correction</td>
</tr>
<tr>
<td>DDR</td>
<td>Double Data Rate Memory</td>
</tr>
<tr>
<td>DevID</td>
<td>Device ID</td>
</tr>
<tr>
<td>DFx</td>
<td>Design for Debug or Design for Test</td>
</tr>
<tr>
<td>DLLP</td>
<td>Data Link Layer Packet (as defined in PCIe Base Specification)</td>
</tr>
<tr>
<td>DLP</td>
<td>In Flit modes, the Data Link Layer Payload within a flit (as defined in PCIe Base Specification).</td>
</tr>
<tr>
<td>$D M H$</td>
<td>$D F x \quad M a n a g e m e n t \quad H u b .$ DFx entity that provides enumeration/global control/status of DFx</td>
</tr>
<tr>
<td>DMS</td>
<td>DFx Management Spoke. DFx entity that implements a specific test/debug functionality within a DMH.</td>
</tr>
<tr>
<td>DMS-ID</td>
<td>Static design time ID assigned to a DMS for ID-routed messages within a DMH. Interchangeably used with the term Spoke-ID.</td>
</tr>
<tr>
<td>$\begin{array}{} { \text { Domain Reset } } \\ { \text { \left(domain reset\right) } } \end{array}$</td>
<td>Used to refer to a hardware mechanism that sets or returns all UCIe registers and state machines associated with a given UCIe Link to their initialization values as specified in this document. It is required for both sides of the Link to have an overlapping time window such that they are both in domain reset concurrently.</td>
</tr>
<tr>
<td>DP</td>
<td>Downstream Port</td>
</tr>
<tr>
<td>DSP</td>
<td>Downstream Switch Port (as defined in CXL Specification)</td>
</tr>
<tr>
<td>DVFS</td>
<td>Dynamic Voltage Frequency Scaling</td>
</tr>
<tr>
<td>DVSEC</td>
<td>Designated Vendor-Specific Extended Capability (as defined in PCIe Base Specification)</td>
</tr>
<tr>
<td>DWORD</td>
<td>Double Word. Four bytes. When used as an addressable quantity, a Double Word is four bytes of data that are aligned on a four-byte boundary (i.e., the least significant two bits of the address are 00b).</td>
</tr>
<tr>
<td>E2E</td>
<td>$E n d \quad t o \quad e n d$</td>
</tr>
<tr>
<td>EM</td>
<td>Eye Margin</td>
</tr>
<tr>
<td>EMIB</td>
<td>Embedded Multi-die Interconnect Bridge</td>
</tr>
<tr>
<td>EML</td>
<td>Eye Margin Left</td>
</tr>
<tr>
<td>EMR</td>
<td>Eye Margin Right</td>
</tr>
<tr>
<td>EMV</td>
<td>Eye Margin Valid</td>
</tr>
<tr>
<td>Encapsulated MTP eMTP</td>
<td>Encapsulated Management Transport Packet. The resulting packet after Encapsulation.</td>
</tr>
<tr>
<td>Encapsulation</td>
<td>Process of splitting an MTP or Vendor defined messages (exchanged between Management Port Gateways on both ends of a link) into smaller pieces to meet any required payload length restrictions or for any other reasons like credit availability, adding a 2-DWORD header to each piece and if required, adding a 1-DWORD data padding at the end of an MTP to transmit the MTP over sideband or mainband UCIe link. In the case of an MTP, the resulting packet after Encapsulation is called the Encapsulated MTP.</td>
</tr>
<tr>
<td>Endpoint EP</td>
<td>As defined in PCIe Base Specification.</td>
</tr>
<tr>
<td>eRCD</td>
<td>Exclusive Restricted CXL Device (as defined in CXL Specification)</td>
</tr>
<tr>
<td>eRCH</td>
<td>Exclusive Restricted CXL Host (as defined in CXL Specification)</td>
</tr>
<tr>
<td>ESD</td>
<td>Electro-Static Discharge</td>
</tr>
<tr>
<td>F2B</td>
<td>Face-to-Back</td>
</tr>
<tr>
<td>F2F</td>
<td>Face-to-Face</td>
</tr>
<tr>
<td>FDI</td>
<td>Flit-Aware Die-to-Die Interface</td>
</tr>
<tr>
<td>FEC</td>
<td>Forward Error Correction</td>
</tr>
</table>

<table>
<caption>Table 1. Terms and Definitions (Sheet 3 of 8)</caption>
<tr>
<th>Term</th>
<th>Definition</th>
</tr>
<tr>
<td>$F E X T$</td>
<td>Far-End CrossTalk</td>
</tr>
<tr>
<td>FH</td>
<td>Flit Header</td>
</tr>
<tr>
<td>FIFO</td>
<td>First In, First Out</td>
</tr>
<tr>
<td>FIR</td>
<td>Finite Impulse Response</td>
</tr>
<tr>
<td>$\mathrm { F I T }$</td>
<td>Failure In Time. 1 FIT = 1 device failure in 109 hours.</td>
</tr>
<tr>
<td>$F l i t$</td>
<td>Link Layer unit of transfer (as defined in CXL Specification).</td>
</tr>
<tr>
<td>Flit_Marker $F M$</td>
<td>Flit Marker (as defined in PCIe Base Specification)</td>
</tr>
<tr>
<td>FW</td>
<td>Firmware</td>
</tr>
<tr>
<td>FW-CLK</td>
<td>Forwarded Clock over the UCIe Link for mainband data Lanes</td>
</tr>
<tr>
<td>HMLS</td>
<td>Highest Maximum Link Speed of next-lower configuration.</td>
</tr>
<tr>
<td>Hub</td>
<td>See DMH.</td>
</tr>
<tr>
<td>$H W$</td>
<td>Hardware</td>
</tr>
<tr>
<td>IL</td>
<td>Insertion Loss</td>
</tr>
<tr>
<td>I/O</td>
<td>$I n p u t / O u t p u t$</td>
</tr>
<tr>
<td>IP</td>
<td>Generic term used to refer to architecture blocks that are defined within the specification (e.g., D2D adapter, PHY, etc.).</td>
</tr>
<tr>
<td>IPA</td>
<td>Ignore Prohibited Access</td>
</tr>
<tr>
<td>ISI</td>
<td>Inter-Symbol Interference</td>
</tr>
<tr>
<td>I/Q</td>
<td>in-phase/quadrature</td>
</tr>
<tr>
<td>KPI</td>
<td>Key Performance Indicator</td>
</tr>
<tr>
<td>L2SPD</td>
<td>L2 Sideband Power Down</td>
</tr>
<tr>
<td>Lane</td>
<td>A pair of signals mapped to physical bumps, one for Transmission, and one for Reception. A xN UCIe Link is composed of N Lanes.</td>
</tr>
<tr>
<td>LCLK</td>
<td>Refers to the clock at which the Logical Physical Layer, Adapter and RDI/FDI are operating.</td>
</tr>
<tr>
<td>LCRC</td>
<td>Link CRC</td>
</tr>
<tr>
<td>LFSR</td>
<td>Linear Feedback Shift Register</td>
</tr>
<tr>
<td>Link UCIe Link</td>
<td>A Link or UCIe Link refers to the set of two UCIe components and their interconnecting Lanes which forms a dual-simplex communications path between the two components.</td>
</tr>
<tr>
<td>LSM</td>
<td>Adapter Link State Machine</td>
</tr>
<tr>
<td>$\mathrm { L T S M }$</td>
<td>Link Training State Machine</td>
</tr>
<tr>
<td>LTSSM</td>
<td>Link Training and Status State Machine (as defined in PCIe Base Specification)</td>
</tr>
<tr>
<td>LSB</td>
<td>Least Significant Bit</td>
</tr>
<tr>
<td>Mainband MB</td>
<td>Connection that constitutes the main data path of UCIe. Consists of a forwarded clock, a data valid pin, and N Lanes of data per module.</td>
</tr>
<tr>
<td>Management Bridge</td>
<td>Type of Management Entity that bridges a Management Network within an SiP to another network that may be internal or external to the SiP.</td>
</tr>
<tr>
<td>Management Director</td>
<td>Management Element that is responsible for discovering, configuring, and coordinating the overall management of the SiP and acts as the manageability Root of Trust (ROT).</td>
</tr>
<tr>
<td>Management Domain</td>
<td>One or more chiplets in an SiP that are interconnected by a Management Network and support UCIe Manageability.</td>
</tr>
<tr>
<td>Management Element</td>
<td>Type of Management Entity that can perform one or more management functions.</td>
</tr>
</table>

<table>
<caption>Table 1. Terms and Definitions (Sheet 4 of 8)</caption>
<tr>
<th>Term</th>
<th>Definition</th>
</tr>
<tr>
<td>Management Entity</td>
<td>Addressable entity on the Management Network that can send and/or receive UCIe Management Transport packets. A Management Element, a Management Port, and a Management Bridge are all a type of Management Entity.</td>
</tr>
<tr>
<td>Management Flit</td>
<td>A Flit that carries a Management Port Message (MPM).</td>
</tr>
<tr>
<td>Management Link Encapsulation Mechanism</td>
<td>Mechanism that defines how UCIe Management Transport packets are transferred across a point-to- point management link.</td>
</tr>
<tr>
<td>Management Network</td>
<td>Network within and between chiplets that is capable of transporting UCIe Management Transport packets.</td>
</tr>
<tr>
<td>Management Port</td>
<td>Management Entity that facilitates management communication between chiplets using a chiplet- to-chiplet management link.</td>
</tr>
<tr>
<td>Management Port Gateway (MPG)</td>
<td>Entity that provides the bridging functionality when transporting an MTP from/to a local SoC management fabric (which is an SoC-specific implementation) to/from a UCIe link.</td>
</tr>
<tr>
<td>Management Port Message (MPM)</td>
<td>Sideband or mainband message that relates to encapsulation.</td>
</tr>
<tr>
<td>Management Protocol</td>
<td>Protocol carried on top of the UCIe Management Transport.</td>
</tr>
<tr>
<td>Management Reset</td>
<td>Type of reset that causes all UCIe manageability and manageability structures in a chiplet to be reset to their default state.</td>
</tr>
<tr>
<td>MCLS</td>
<td>Number of active Modules Current Link Speed</td>
</tr>
<tr>
<td>MMIO</td>
<td>Memory mapped Input/Output</td>
</tr>
<tr>
<td>MMPL</td>
<td>Multi-module PHY Logic</td>
</tr>
<tr>
<td>Module</td>
<td>UCIe main data path on the physical bumps is organized as a group of Lanes called a Module. For $a \quad s i n g l e \quad M o d u l e .$ 16 Lanes constitute a single Module. For Advanced Package, $6 4 \quad L a n e s \quad c o n s t i t u t e$</td>
</tr>
<tr>
<td>MSB</td>
<td>Most Significant Bit</td>
</tr>
<tr>
<td>MTP</td>
<td>Management Transport Packet</td>
</tr>
<tr>
<td>Nak</td>
<td>Negatively acknowledge</td>
</tr>
<tr>
<td>NEXT</td>
<td>Near-End Cross Talk</td>
</tr>
<tr>
<td>NOP</td>
<td>No Operation</td>
</tr>
<tr>
<td>NVMe</td>
<td>Non-Volatile $M e m o r y \quad e x p r e s s$</td>
</tr>
<tr>
<td>One-Time Programmable</td>
<td>Any data storage mechanism that is capable of being programmed only once (e.g., fuse).</td>
</tr>
<tr>
<td>P2P</td>
<td>Peer to peer</td>
</tr>
<tr>
<td>Packet</td>
<td>A block of data transmitted across a network.</td>
</tr>
<tr>
<td>$P C I e \left( P C I \quad E x p r e s s \right)$</td>
<td>Peripheral Component Interconnect Express (defined in PCIe Base Specification)</td>
</tr>
<tr>
<td>PCIe Flit Mode</td>
<td>This term is used to reference Flit Mode related Protocol features defined in PCIe Base Specification.</td>
</tr>
<tr>
<td>PCIe non-Flit Mode</td>
<td>Specification. This term is used to reference non-Flit Mode related Protocol features defined in PCIe Base</td>
</tr>
<tr>
<td>PDOS</td>
<td>Permanent Denial of Service</td>
</tr>
<tr>
<td>PDS</td>
<td>Pause of Data Stream</td>
</tr>
<tr>
<td>PHY</td>
<td>Physical Layer (PHY and Physical Layer are used interchangeable throughout the Specification)</td>
</tr>
<tr>
<td>PI</td>
<td>Phase Interpolator</td>
</tr>
<tr>
<td>PLL</td>
<td>Phase-Locked Loop</td>
</tr>
<tr>
<td>PM</td>
<td>Power Management states, used to refer to behavior and/or rules related to Power Management states (covers both L1 and L2).</td>
</tr>
<tr>
<td>PMO</td>
<td>Sideband Performant Mode Operation</td>
</tr>
<tr>
<td>Power Management Director</td>
<td>A Management Element that may configure power management parameters.</td>
</tr>
</table>

<table>
<caption>Table 1. Terms and Definitions (Sheet 5 of 8)</caption>
<tr>
<th>Term</th>
<th>Definition</th>
</tr>
<tr>
<td>Power Management Element</td>
<td>A type of Management Entity that can perform one or more Power Management functions.</td>
</tr>
<tr>
<td>PSPT</td>
<td>Priority Sideband Packet Transfer</td>
</tr>
<tr>
<td>PSTP</td>
<td>Priority Sideband Traffic Packet</td>
</tr>
<tr>
<td>QWORD</td>
<td>Quad Word. Eight bytes. When used as an addressable quantity, a Quad Word is eight bytes of data that are aligned on an eight-byte boundary (i.e., the least significant three bits of the address are 000b).</td>
</tr>
<tr>
<td>RAC</td>
<td>Read Access Control</td>
</tr>
<tr>
<td>RCD</td>
<td>Restricted CXL Device (as defined in CXL Specification)</td>
</tr>
<tr>
<td>RCH</td>
<td>Restricted CXL Host (as defined in CXL Specification)</td>
</tr>
<tr>
<td>RCIEP</td>
<td>Root Complex Integrated Endpoint</td>
</tr>
<tr>
<td>RCKN_P RXCKN rxckn</td>
<td>Physical Lane for Clock Receiver Phase-2</td>
</tr>
<tr>
<td>RCKP_P RXCKP rxckp</td>
<td>Physical Lane for Clock Receiver Phase-1</td>
</tr>
<tr>
<td>RCRB</td>
<td>Root Complex Register Block</td>
</tr>
<tr>
<td>RDI</td>
<td>Raw Die-to-Die Interface</td>
</tr>
<tr>
<td>$R D _ { - } P \left[ N \right]$ $R D \_ P N$ $\begin{array}{} \mathrm { R X D A I A I N } \\ \mathrm { r e d a t a n } \end{array}$</td>
<td>Nth Physical Lane for Data Receiver</td>
</tr>
<tr>
<td>remote Link partner</td>
<td>This term is used throughout this specification to denote the logic associated with the far side of the UCIe Link; to denote actions or messages sent or received by the Link partner of a UCIe die.</td>
</tr>
<tr>
<td>Replay Retry</td>
<td>Retry and Replay are used interchangeably to refer to the Link level reliability mechanisms.</td>
</tr>
<tr>
<td>Reserved</td>
<td>The contents, states, or information are not defined at this time. Using any Reserved area (for example, packet header bit-fields, configuration register bits) is not permitted. Reserved register fields must be read only and must return 0 (all Os for multi-bit fields) when read. For packets transmitted and received over the UCIe Link (mainband or sideband), the Reserved bits must be cleared to Ob by the sender and ignored by the receiver. Reserved encodings for register and packet fields must not be used. Any implementation dependence on a Reserved field value or encoding will result in an implementation that is not UCIe-compliant. The functionality of such an implementation cannot be guaranteed in this or any future revision of this specification. For registers, UCIe uses the "RsvdP" or "RsvdZ" attributes for reserved fields, as well as Rsvd, and these follow the same definition as PCIe Base Specification for hardware as well as software.</td>
</tr>
<tr>
<td>reset</td>
<td>If reset or clear is used and no value is provided for a bit, it is interpreted as 0b.</td>
</tr>
<tr>
<td>RID</td>
<td>Revision ID</td>
</tr>
<tr>
<td>$R L$</td>
<td>Register Locator</td>
</tr>
<tr>
<td>Root Complex</td>
<td>As defined in PCIe Base Specification.</td>
</tr>
<tr>
<td>Root Port RP</td>
<td>As defined in PCIe Base Specification.</td>
</tr>
<tr>
<td>RoT</td>
<td>Root of Trust</td>
</tr>
<tr>
<td>RRDCK_P RXCKRD rxckRD</td>
<td>Physical Lane for redundant Clock/Track Receiver</td>
</tr>
</table>

<table>
<caption>Table 1. Terms and Definitions (Sheet 6 of 8)</caption>
<tr>
<th>Term</th>
<th>Definition</th>
</tr>
<tr>
<td>$R R D \_ P \left[ N \right]$ RRD_PN RXDATARD[N] rxdataRD[N]</td>
<td>Nth Physical Lane for redundant Data Receiver</td>
</tr>
<tr>
<td>RRDVLD_P RXVLDRD rxvldRD</td>
<td>Physical Lane for redundant Valid Receiver</td>
</tr>
<tr>
<td>RTRK_P RXTRK rxtrk</td>
<td>Physical Lane for Track Receiver</td>
</tr>
<tr>
<td>$\mathrm { R V L D }$ RXVLD rxvld</td>
<td>Physical Lane for Valid Receiver</td>
</tr>
<tr>
<td>Rx</td>
<td>Receiver</td>
</tr>
<tr>
<td>RXCKSB rxcksb</td>
<td>Physical Lane for sideband Clock Receiver</td>
</tr>
<tr>
<td>RXCKSBRD $r x c k s b R D$</td>
<td>Physical Lane for redundant sideband Clock Receiver</td>
</tr>
<tr>
<td>RXDATASB rxdatasb</td>
<td>Physical Lane for sideband Data Receiver</td>
</tr>
<tr>
<td>RXDATASBRD rxdatasbRD</td>
<td>Physical Lane for redundant sideband Data Receiver</td>
</tr>
<tr>
<td>SBFE</td>
<td>Sideband Feature Extensions</td>
</tr>
<tr>
<td>$\left\{ < \mathrm { S B M S G } > \right\}$</td>
<td>Sideband message requests or responses are referred to by their names enclosed in curly brackets. See Chapter 7.0 for the mapping of sideband message names to relevant encodings. An asterisk in the &lt;SBMSG&gt; name is used to denote a group of messages with the same prefix or suffix in their name.</td>
</tr>
<tr>
<td>SC</td>
<td>Successful Completion</td>
</tr>
<tr>
<td>SD</td>
<td>Security Director. Management Element that may configure security parameters.</td>
</tr>
<tr>
<td>Segmentation</td>
<td>Process of taking a large MTP, splitting it into smaller "segments" and sending those segments on multiple sideband links or mainband stacks.</td>
</tr>
<tr>
<td>SERDES</td>
<td>Serializer/Deserializer</td>
</tr>
<tr>
<td>serial packet</td>
<td>$A \quad 6 4 - b i t$ serial packet is defined on the sideband I/O interface to the remote chiplet as shown in</td>
</tr>
<tr>
<td>set</td>
<td>If set is used and no value is provided for a bit, it is interpreted as 1b.</td>
</tr>
<tr>
<td>SFES</td>
<td>Sideband Feature Extensions Supported</td>
</tr>
<tr>
<td>Sideband SB</td>
<td>Connection used for parameter exchanges, register accesses for debug/compliance and coordination with remote partner for Link training and management. Consists of a forwarded clock pin and a data pin in each direction. The clock is fixed at 800 MHz regardless of the main data path speed. The sideband logic for the UCIe Physical Layer must be on auxiliary power and an "always on" domain. Each module has its own set of sideband pins.</td>
</tr>
<tr>
<td>SiP</td>
<td>System in Package. Collection of chiplets packaged as a unit.</td>
</tr>
<tr>
<td>SM</td>
<td>State Machine</td>
</tr>
<tr>
<td>SO</td>
<td>Sideband-only</td>
</tr>
<tr>
<td>SoC</td>
<td>System on a Chip</td>
</tr>
<tr>
<td>Spoke</td>
<td>See DMS.</td>
</tr>
<tr>
<td>Standard Package</td>
<td>This packaging technology is used for low cost and long reach interconnects using traces on organic package/substrate</td>
</tr>
<tr>
<td>Strobe</td>
<td>Used interchangeably with clock for sideband clock</td>
</tr>
</table>

<table>
<caption>Table 1. Terms and Definitions (Sheet 7 of 8)</caption>
<tr>
<th>Term</th>
<th>Definition</th>
</tr>
<tr>
<td>SW</td>
<td>Software</td>
</tr>
<tr>
<td>TARR</td>
<td>Tx Adjustment during Runtime Recalibration</td>
</tr>
<tr>
<td>TC</td>
<td>Traffic Class</td>
</tr>
<tr>
<td>TCKN_P TXCKN txckn</td>
<td>Physical Lane for Clock Transmitter Phase-2</td>
</tr>
<tr>
<td>TCKP_P TXCKP txckp</td>
<td>Physical Lane for Clock Transmitter Phase-1</td>
</tr>
<tr>
<td>TCM</td>
<td>Tightly coupled mode</td>
</tr>
<tr>
<td>TDPI</td>
<td>Test, Debug, Pattern, and Infrastructure</td>
</tr>
<tr>
<td>$T D _ { - } P \left[ N \right]$ TD_PN TXDATA[N] txdataN</td>
<td>Nth Physical Lane for Data Transmitter</td>
</tr>
<tr>
<td>Throttle Threshold</td>
<td>Threshold associated with a specific Function ID (e.g., power, thermal, etc.) that triggers the throttle function when breached.</td>
</tr>
<tr>
<td>TLP</td>
<td>Transaction Layer Packet (as defined in PCIe Base Specification)</td>
</tr>
<tr>
<td>TRD_P[N] TRD_PN TXDATARD[N] txdataRD[N]</td>
<td>Nth Physical Lane for redundant Data Transmitter</td>
</tr>
<tr>
<td>TRDCK_P TXCKRD txckRD</td>
<td>Physical Lane for redundant Clock/Track Transmitter</td>
</tr>
<tr>
<td>TRDVLD_P TXVLDRD txvldRD</td>
<td>Physical Lane for redundant Valid Transmitter</td>
</tr>
<tr>
<td>Trx</td>
<td>Transceiver</td>
</tr>
<tr>
<td>TSV</td>
<td>Through-Silicon Via</td>
</tr>
<tr>
<td>TTRK_P TXTRK txtrk</td>
<td>Physical Lane for Track Transmitter</td>
</tr>
<tr>
<td>TVLD_P TXVLD txvld</td>
<td>Physical Lane for Valid Transmitter</td>
</tr>
<tr>
<td>Tx</td>
<td>Transmitter</td>
</tr>
<tr>
<td>TXCKSB txcksb</td>
<td>Physical Lane for sideband Clock Transmitter</td>
</tr>
<tr>
<td>TXCKSBRD txcksbRD</td>
<td>Physical Lane for redundant sideband Clock Transmitter</td>
</tr>
<tr>
<td>TXDATASB txdatasb</td>
<td>Physical Lane for sideband Data Transmitter</td>
</tr>
<tr>
<td>TXDATASBRD $\mathrm { t x d a t a s b R D }$</td>
<td>Physical Lane for redundant sideband Data Transmitter</td>
</tr>
<tr>
<td>TXEQ</td>
<td>Transmitter Equalization</td>
</tr>
<tr>
<td>UCIe</td>
<td>Universal Chiplet Interconnect express</td>
</tr>
</table>

<table>
<caption>Table 1. Terms and Definitions (Sheet 8 of 8)</caption>
<tr>
<th>Term</th>
<th>Definition</th>
</tr>
<tr>
<td>UCIe-3D</td>
<td>Universal Chiplet Interconnect express for 3D packaging</td>
</tr>
<tr>
<td>UCIe-A</td>
<td>Used to denote x64 Advanced Package module.</td>
</tr>
<tr>
<td>UCIe-A x32</td>
<td>Used to denote x32 Advanced Package module. See Chapter 5.0 for UCIe-A x32 Advanced Package bump matrices, and interoperability between x32 to x32 and x32 to x64 module configurations.</td>
</tr>
<tr>
<td>UCIe-S</td>
<td>Used to denote x16 Standard Package module.</td>
</tr>
<tr>
<td>UCIe chiplet</td>
<td>A chiplet that complies with the UCIe specification.</td>
</tr>
<tr>
<td>UCIe DFx Architecture UDA</td>
<td>DFx architecture specified for chiplets and SiPs that implement UCIe.</td>
</tr>
<tr>
<td>$U C I e \quad D F x \quad M e s s a g e$ UDM</td>
<td>Generic term for all UCIe Management Transport packets with Protocol ID set to 'Test and Debug Protocols'.</td>
</tr>
<tr>
<td>UCIe die</td>
<td>This term is used throughout this specification to denote the logic associated with the UCIe Link on any given chiplet with a UCIe Link connection. It is used as a common noun to denote actions or messages sent or received by an implementation of UCIe.</td>
</tr>
<tr>
<td>UCIe Flit Mode</td>
<td>Operating Mode in which CRC bytes are inserted and checked by the D2D Adapter. If applicable, Retry is also performed by the D2D Adapter.</td>
</tr>
<tr>
<td>UCIe Link</td>
<td>A UCIe connection between two chiplets. These chiplets are Link partners in the context of UCIe since they communicate with each other using a common UCIe Link.</td>
</tr>
<tr>
<td>$\begin{array}{} { \text { UCIe Mainband } } \\ { \text { Manaanement Port } } \end{array}$</td>
<td>Chiplet port that implements the Management Link Encapsulation Mechanism and can transfer UCIe Management Transport packets across a point-to-point UCIe mainband link.</td>
</tr>
<tr>
<td>UCIe Management Transport Protocol</td>
<td>Protocol used to transfer UCIe Management Transport packets between management entities.</td>
</tr>
<tr>
<td>UCIe Raw Format</td>
<td>Operating format in which all the bytes of a Flit are populated by the Protocol Layer.</td>
</tr>
<tr>
<td>UCIe Sideband Management Port</td>
<td>Chiplet port that implements the Management Link Encapsulation Mechanism and can transfer UCIe Management Transport packets across a point-to-point UCIe sideband link.</td>
</tr>
<tr>
<td>UCLS</td>
<td>UCIe Link Structure</td>
</tr>
<tr>
<td>UEDT</td>
<td>UCIe Early Discovery Table</td>
</tr>
<tr>
<td>UHM</td>
<td>UCIe Link Health Monitor</td>
</tr>
<tr>
<td>UIE</td>
<td>Uncorrectable Internal Error</td>
</tr>
<tr>
<td>UİRB</td>
<td>UCIe Register Block</td>
</tr>
<tr>
<td>UİSRB</td>
<td>UCIe Structure Register Block</td>
</tr>
<tr>
<td>UMAP</td>
<td>UCIe Memory Access Protocol</td>
</tr>
<tr>
<td>Unit Interval UI</td>
<td>Given a data stream of a repeating pattern of alternating 1 and 0 values, the Unit Interval is the value measured by averaging the time interval between voltage transitions, over a time interval sufficiently long to make all intentional frequency modulation of the source clock negligible.</td>
</tr>
<tr>
<td>UP</td>
<td>Upstream Port</td>
</tr>
<tr>
<td>UR</td>
<td>Unsupported Request</td>
</tr>
<tr>
<td>USP</td>
<td>Upstream Switch Port</td>
</tr>
<tr>
<td>VH</td>
<td>Virtual Hierarchy (as defined in CXL Specification)</td>
</tr>
<tr>
<td>vLSM</td>
<td>Virtual Link State Machine</td>
</tr>
<tr>
<td>Vref</td>
<td>Reference voltage for receivers</td>
</tr>
<tr>
<td>VTF</td>
<td>Voltage Transfer Function</td>
</tr>
<tr>
<td>WAC</td>
<td>Write Access Control</td>
</tr>
<tr>
<td>zero</td>
<td>Numerical value of 0 in a bit, field, or register, of appropriate width for that bit, field, or register.</td>
</tr>
</table>

<table>
<caption>Table 2. Unit of Measure Symbols</caption>
<tr>
<th>Symbol</th>
<th>Unit of Measure</th>
</tr>
<tr>
<td>$b$</td>
<td>bit</td>
</tr>
<tr>
<td>B</td>
<td>byte</td>
</tr>
<tr>
<td>$d B$</td>
<td>decibel</td>
</tr>
<tr>
<td>$f F$</td>
<td>femtofarad</td>
</tr>
<tr>
<td>GB/s</td>
<td>gigabytes per second</td>
</tr>
<tr>
<td>GHZ</td>
<td>gigahertz</td>
</tr>
<tr>
<td>GT/s</td>
<td>gigatransfers per second</td>
</tr>
<tr>
<td>KB/s</td>
<td>kilobytes per second</td>
</tr>
<tr>
<td>MB/s</td>
<td>megabytes per second</td>
</tr>
<tr>
<td>MHz</td>
<td>megahertz</td>
</tr>
<tr>
<td>mm</td>
<td>millimeter</td>
</tr>
<tr>
<td>ms</td>
<td>millisecond</td>
</tr>
<tr>
<td>$M T / s$</td>
<td>megatransfers per second</td>
</tr>
<tr>
<td>mUI</td>
<td>milli-Unit interval</td>
</tr>
<tr>
<td>mV</td>
<td>millivolt</td>
</tr>
<tr>
<td>$m V p p$</td>
<td>millivolt peak-to-peak</td>
</tr>
<tr>
<td>um</td>
<td>micrometer</td>
</tr>
<tr>
<td>us</td>
<td>microsecond</td>
</tr>
<tr>
<td>ns</td>
<td>nanosecond</td>
</tr>
<tr>
<td>$p J$</td>
<td>$\mathrm { p i c o j o u l e }$</td>
</tr>
<tr>
<td>pk</td>
<td>peak</td>
</tr>
<tr>
<td>ppm</td>
<td>parts per million</td>
</tr>
<tr>
<td>$p s$</td>
<td>picosecond</td>
</tr>
<tr>
<td>s</td>
<td>second</td>
</tr>
<tr>
<td>$\frac { T B } { V }$</td>
<td>terabytes per second</td>
</tr>
<tr>
<td>V</td>
<td>volt</td>
</tr>
</table>

## Reference Documents

<table>
<caption>Table 3. Reference Documentsª</caption>
<tr>
<th>Document</th>
<th>Document Location</th>
</tr>
<tr>
<td>PCI Express® Base Specification (PCIe Base Specification) Revision 6.3</td>
<td>www.pcisig.com</td>
</tr>
<tr>
<td>Compute Express Link Specification (CXL Specification) Revision 3.2</td>
<td>computeexpresslink.org</td>
</tr>
<tr>
<td>ACPI Specification (version 6.5 or later)</td>
<td>www.uefi.org</td>
</tr>
<tr>
<td>Industry Council on ESD Targets white papers</td>
<td>www.jedec.org, reference JEP196 www.esdindustrycouncil.org/ic/en, reference White Paper 2 Part II www.esda.org, reference White Paper 2 Part II</td>
</tr>
</table>

a. References to these documents throughout this specification relate to the versions/revisions listed here.

## Revision History

Table 4 lists the significant changes in different revisions.

<table>
<caption>Table 4. Revision History</caption>
<tr>
<th>Revision</th>
<th>Date</th>
<th>Description</th>
</tr>
<tr>
<td>3.0</td>
<td>August 5, 2025</td>
<td>· Support for 48 GT/s and 64 GT/s data rates . Runtime Recalibration enhancement · Extended reach sideband · Enhancements to enable protocols that require continuous transmission · Support for priority sideband packets · Support for Early Firmware Download · Support for Fast Throttle Emergency Shutdown · Incorporation of Errata and bug fixes over 2.0</td>
</tr>
<tr>
<td>2.0</td>
<td>$A u g u s t \quad 6 , 2 0 2 4$</td>
<td>· Chapter 6.0, UCIe-3D and related support for UCIe 3D · Chapter 8.0, System Architecture and related support for: - Section 8.1, "UCIe Manageability" - Section 8.2, "Management Transport Packet (MTP) Encapsulation" - Section 8.3, "UCIe Debug and Test Architecture (UDA)" · di/dt risk mitigation during clock gating · Incorporation of Errata and bug fixes over 1.1</td>
</tr>
<tr>
<td rowspan="2">1.1</td>
<td rowspan="2">$J u l y \quad 1 0 , 2 0 2 3$</td>
<td>· Streaming Flit Format Capabilities (Allows Streaming protocols to use Adapter Retry/CRC) · Enhanced Multi-Protocol Multiplexing (Allows dynamic multiplexing of different protocols on the same Adapter) · Support for x32 Advanced Package Modules . Support for UCIe Link Health Monitoring · Definition of Hardware capabilities to enable Compliance · di/dt risk mitigation during clock gating</td>
</tr>
<tr>
<td>· Incorporation of Errata and bug fixes over 1.0</td>
</tr>
<tr>
<td>1.0</td>
<td>February 17, 2022</td>
<td>Initial release.</td>
</tr>
</table>

## 1.0 Introduction

This chapter provides an overview of the Universal Chiplet Interconnect express (UCIe) architecture.
UCIe is an open, multi-protocol capable, on-package interconnect standard for connecting multiple
dies on the same package. The primary motivation is to enable a vibrant ecosystem supporting
disaggregated die architectures which can be interconnected using UCIe. UCIe supports multiple
protocols (PCIe, CXL, Streaming, and a raw format that can be used to map any protocol of choice as
long as both ends support it) on top of a common physical and Link layer. It encompasses the
elements needed for SoC construction such as the application layer, as well as the form-factors
relevant to the package (e.g., bump location, power delivery, thermal solution, etc.).

UCIe Manageability Architecture is an optional mechanism to manage a UCIe-based System-in-
Package (SiP) by provisioning for a common manageability architecture and hardware/software
infrastructure to be leveraged across implementations. UCIe DFx Architecture (UDA) leverages the
UCIe Manageability Architecture to provide a standardized test and debug infrastructure for a UCIe-
based SiP.

The specification is defined to ensure interoperability across a wide range of devices having different
performance characteristics. A well-defined debug and compliance mechanism is provided to ensure
interoperability. It is expected that the specification will evolve in a backward compatible manner.

While UCIe supports a wide range of usage models, some are provided here as an illustration of the
type of capability and innovation it can unleash in the compute industry. The initial protocols being
mapped to UCIe are PCIe, CXL, and Streaming. The mappings for all protocols are done using a Flit
Format, including the Raw Format. Both PCIe and CXL are widely used and these protocol mappings
will enable more on-package integration by replacing the PCIe SERDES PHY and the PCIe/CXL LogPHY
along with the Link level Retry with a UCIe Adapter and PHY to improve the power and performance
characteristics. UCIe provisions for Streaming protocols to also leverage the Link Level Retry of the
UCIe Adapter, and this can be used to provide reliable transport for protocols other than PCIe or CXL.
UCIe also supports a Raw Format that is protocol-agnostic to enable other protocols to be mapped;
while allowing usages such as integrating a standalone SERDES/transceiver tile (e.g., ethernet) on-
package. When using Raw Format, the Protocol Layer is responsible for reliable transport across the
UCIe Link.

Figure 1-1 demonstrates an SoC package composed of CPU Dies, accelerator Die(s) and I/O Tile
Die(s) connected through UCIe. The accelerator or I/O Tile can use CXL transactions over UCIe when
connected to a CPU - leveraging the I/O, coherency, and memory protocols of CXL. The I/O tile can
provide the external CXL, PCIe, and DDR pins of the package. The accelerator can also use PCIe
transactions over UCIe when connected to a CPU. The CPU to CPU connectivity on-package can also
use the UCIe interconnect, running coherency protocols.

<figure>
<figcaption>Figure 1-1. A Package Composed of CPU Dies, Accelerator Die(s), and I/O Tile Die Connected through UCIe</figcaption>

Mem

CPU

CPU

Mem

UCle

UCle

Mem

Accel-

$I / O$
Tile

$\frac { 3 } { 3 }$

erator

UCle

CXL/ PCle

DDR

</figure>

A UCIe Retimer may be used to extend the UCIe connectivity beyond the package using an Off-
Package Interconnect. Examples of Off-Package Interconnect include electrical cable or optical cable
or any other technology to connect packages at a Rack/Pod level as shown in Figure 1-2. The UCIe
specification requires the UCIe Retimer to implement the UCIe interface to the Die that it connects on
its local package and ensure that the Flits are delivered to the remote UCIe Die interface in the
separate package following UCIe protocol using the channel extension technology of its choice.

Figure 1-2 demonstrates a rack/pod-level disaggregation using CXL protocol. Figure 1-2a shows the
rack level view where multiple compute nodes (virtual hierarchy) from different compute chassis
connect to a CXL switch which connects to multiple CXL accelerators/Type-3 memory devices which
can be placed in one or more separate drawer. The logical view of this connectivity is shown in
Figure 1-2b, where each "host" $\left( H 1 , H 2 , \cdots \right)$ is a compute drawer. Each compute drawer connects to
the switch using an Off-Package Interconnect running CXL protocol through a UCIe Retimer, as shown
in Figure 1-2c. The switch also has co-package Retimers where the Retimer tiles connect to the main
switch die using UCIe and on the other side are the PCIe/CXL physical interconnects to connect to the
accelerators/memory devices, as shown in Figure 1-2c.

<figure>
<figcaption>Figure 1-2. UCIe enabling long-reach connectivity at Rack/Pod Level</figcaption>

Mem

(Off-Package Interconnect)

CPU

CPU

Mem

TORS
Memory/
Accelerator
000000000

H1

H2

HA

H#

UCle

Mem

UCle
CXL

Retimer

0X1

CXI

CXI

CPU

I/O
Tile

UCle

CXI

CXI

(Pooled Memory /
$\left. \mathrm { A c c e l e r a t o r D r a w e r } \right)$

CXL Switch

Compute
CPU

Standardized Fabric Manager

CXL/PČle

DDR
(Interconnects at drawer level)
(CPU Package)

x

CXL

Compute
CPU

CXL

CXL

CXL

CXL

D1

D2

D3

D4

D#

M

(Off-Package Interconnect to CXL Switch)

CPU

Compute
188

1

1

1

UCle
Retimer

UCle

UCle

HDC

HDD

Retimer

UCle (CX

Retimer

(Compute Drawer)

CXL at Rack level
connected using
any long-reach media
(Electrical Cable/Optical,
etc.) through UCle
Retimers on package

(Pooled Memory /Accelerator Drawer)

CXL Switch Die

(CXL/PCle Interconnects at
Pooled Memory/ Accelerator drawer)
(CXL Switch Package)
(2)

(a)

(b)

</figure>

UCIe permits three different packaging options: Standard Package (2D), and Advanced Package
(2.5D), and UCIe-3D. This covers the spectrum from lowest cost to best performance interconnects.

1\. Standard Package - This packaging technology is used for low cost and long reach (10 mm to
25 mm, when measured from a bump on one Die to the connecting bump of the remote Die)
interconnects using traces on organic package/substrate, while still providing significantly better
BER characteristics compared to off-package SERDES. Figure 1-3 shows an example application
using the Standard Package option. Table 1-1 shows a summary of the characteristics of the
Standard Package option with UCIe.

<figure>
<figcaption>Figure 1-3. Standard Package interface</figcaption>

Die-1

Die-0

Die-2

Package Substrate

</figure>

Table 1-1.
Characteristics of UCIe on Standard Package

<table>
<tr>
<th>Index</th>
<th>Value</th>
</tr>
<tr>
<td>Supported speeds (per Lane)</td>
<td>4 GT/s, 8 GT/s, 12 GT/s, 16 GT/s, 24 GT/s, 32 GT/s, 48 GT/s, 64 GT/s</td>
</tr>
<tr>
<td>Bump Pitch</td>
<td>100 um to 130 um</td>
</tr>
<tr>
<td>Channel reach (short reach)</td>
<td>10 mm</td>
</tr>
<tr>
<td>Channel reach (long reach)</td>
<td>25 mm</td>
</tr>
<tr>
<td rowspan="3">Raw Bit Error Rate (BER)ª</td>
<td>1E-27 ( &lt;= 8 GT/s)</td>
</tr>
<tr>
<td>$1 E - 1 5 \left( < = 4 8 \quad G T / s \quad a n d > = 1 2 \quad G T / s \right)$</td>
</tr>
<tr>
<td>1E-12 (&gt; 48 GT/s)</td>
</tr>
</table>

a. See Chapter 5.0 for details about BER characteristics.

2\. Advanced Package - This packaging technology is used for performance optimized
applications. Consequently, the channel reach is short (less than 2 mm, when measured from a
bump on one Die to the connecting bump of the remote Die) and the interconnect is expected to
be optimized for high bandwidth and low latency with best performance and power efficiency
characteristics. Figure 1-4, Figure 1-5, and Figure 1-6 show example applications using the
Advanced Package option.

Table 1-2 shows a summary of the main characteristics of the Advanced Package option.

<table>
<caption>Table 1-2. Characteristics of UCIe on Advanced Package</caption>
<tr>
<th>Index</th>
<th>Value</th>
</tr>
<tr>
<td>Supported speeds (per Lane)</td>
<td>4 GT/s, 8 GT/s, 12 GT/s, 16 GT/s, 24 GT/s, 32 GT/s, 48 GT/s, 64 GT/s</td>
</tr>
<tr>
<td>Bump pitch</td>
<td>25 um to 55 um</td>
</tr>
<tr>
<td>Channel reach</td>
<td>2 mm</td>
</tr>
<tr>
<td rowspan="3">Raw Bit Error Rate (BER)a</td>
<td>1E-27 $\left( < = 1 2 \quad G T / s \right)$</td>
</tr>
<tr>
<td>1E-15 ( &lt;= 48 GT/s and $\left. > = 1 6 \quad G T / s \right)$</td>
</tr>
<tr>
<td>1E-12 (&gt; 48 GT/s)</td>
</tr>
</table>

a. See Chapter 5.0 for details about BER characteristics.

<figure>
<figcaption>Figure 1-4. Advanced Package interface: Example 1</figcaption>

Die-1

Die-0

Die-2

Silicon Bridge
(e.g. EMIB)

Package Substrate

Silicon Bridge
(e.g. EMIB)

Figure 1-5.
Advanced Package interface: Example 2

Die-1

Die-0

Die-2

Interposer (e.g. CoWoS)

Package Substrate

Figure 1-6.
Advanced Package interface: Example 3

Die-1

Die-0

Die-2

Silicon Bridge

Fanout Organic Interposer (e.g., FOCoS-B)

Silicon Bridge

Package Substrate

</figure>

3\. UCIe-3D: This packaging technology uses a two-dimensional array of interconnect bumps for
data transmission between dies where one die is stacked on top of another. A menu of design
options are provided for vendors to develop standard building blocks.

Table 1-3 shows a summary of the main characteristics of UCIe-3D. Figure 1-7 shows an example
of UCIe-3D. See Chapter 6.0 for a detailed description of UCIe-3D.

<table>
<caption>Table 1-3. Characteristics of UCIe-3D</caption>
<tr>
<th>Index</th>
<th>Value</th>
</tr>
<tr>
<td>Supported speed (per Lane)</td>
<td>up to 4 GT/s</td>
</tr>
<tr>
<td>Bump pitch</td>
<td>&lt; 10 um (optimizedª) 10 to 25 um (functionalª)</td>
</tr>
<tr>
<td>Channel</td>
<td>3D vertical</td>
</tr>
<tr>
<td>Raw Bit Error Rate (BER)b</td>
<td>1e-27</td>
</tr>
</table>

a. Circuit Architecture is optimized for < 10 um bump pitches. 10 to 25 um are supported functionally.

b. See Chapter 6.0 for details about BER characteristics.

<figure>
<figcaption>Figure 1-7. Example of UCIe-3D</figcaption>

Face-to-Face Hybrid Bonding

TSVs

Package Substrate

C4 Bumps

</figure>

## 1.1 UCIe Components

UCIe is a layered protocol, with each layer performing a distinct set of functions. Figure 1-8 shows the
three main components of the UCIe stack and the functionality partitioning between the layers. It is
required for every component in the UCIe stack to be capable of supporting the advertised
functionality and bandwidth. Several timeouts and related errors are defined for different handshakes
and state transitions. All timeout values specified are minus 0% and plus 50% unless explicitly stated
otherwise. All timeout values must be set to the specified values after Domain Reset. All counter
values must be set to the specified values after Domain Reset.

<figure>
<figcaption>Figure 1-8. UCIe Layers and functionalities</figcaption>

Protocol Layer

Flit-aware D2D Interface (FDI)

ARB/MUX (when applicable)
CRC/Retry (when applicable)
Link State Management
Parameter Negotiation

Die-to-Die Adapter

Raw D2D Interface (RDI)

Link Training

Physical Layer

$L a n e \quad R e v e r s a l \left( w h e n \quad a p p l i c a b l e \right)$

Scrambling/De-scrambling
Sideband Initialization and Transfers
Analog Front End
Clock Forwarding

</figure>

### 1.1.1 Protocol Layer

While the Protocol Layer may be application specific, UCIe Specification provides examples of
transferring CXL or PCIe protocols over UCIe Links. The following protocols are supported in UCIe for
enabling different applications:

· PCIe from PCIe Base Specification.

· CXL from CXL Specification. Note that RCD/RCH/eRCD/eRCH are not supported.

· Streaming protocol: This offers generic modes for a user defined protocol to be transmitted using
UCIe.

· UCIe Management Transport protocolª: This is an end-to-end media independent protocol(s) for
management communication on the UCIe Management Network within the UCIe Manageability
Architecture.

For each protocol, different optimizations and associated Flit transfers are available for transfer over
UCIe. Chapter 2.0 and Chapter 3.0 cover the relevant details of different modes and Flit Formats.

a. UCIe Management Transport protocol can be encapsulated for transport over the UCIe sideband
or the UCIe mainband. Section 8.1 covers the details of this protocol. Section 8.2 covers the
details around encapsulation of this protocol over the UCIe sideband and the UCIe mainband.

### 1.1.2 Die-to-Die (D2D) Adapter

The D2D Adapter coordinates with the Protocol Layer and the Physical Layer to ensure successful data
transfer across the UCIe Link. It minimizes logic on the main data path as much as possible, thus
providing a low-latency, optimized data path for protocol Flits. When transporting CXL protocol, the
ARB/MUX functionality required for multiple simultaneous protocols is performed by the D2D Adapter.
For options where the Raw BER is more than 1e-27, a CRC and Retry scheme is provided in the UCIe
Specification for PCIe, CXL, or Streaming protocol, which is implemented in the D2D Adapter. See
Section 3.8 for Retry rules.

D2D Adapter is responsible for coordinating higher level Link state machine and bring up, protocol
options related parameter exchanges with remote Link partner, and when supported, power
management coordination with remote Link partner. Chapter 3.0 covers the relevant details for the
D2D Adapter.

### 1.1.3 Physical Layer

The Physical Layer has three sub-components as shown in Figure 1-9.

<figure>
<figcaption>Figure 1-9. Physical Layer components</figcaption>

Raw D2D Interface (RDI)

Link Training

Physical Layer

Lane Repair (when applicable)

Lane Reversal (when applicable)

Scrambling/De-scrambling

Sideband/
Global

Sideband Initialization and Transfers

$\mathrm { E l e c t r i c a l } / \mathrm { A F E } \left[ \mathrm { k } \mathrm { s l i c e s } \right]$

Analog Front End

Clock Forwarding

</figure>

The UCIe main data path on the physical bumps is organized as a group of Lanes called a Module. A
Module forms the atomic granularity for the structural design implementation of the UCIe AFE. The
number of Lanes per Module for Standard and Advanced Packages is specified in Chapter 4.0. A given
instance of Protocol Layer or D2D adapter can send data over multiple modules where bandwidth
scaling is required.

The physical Link of UCIe is composed of two types of connections:

## 1. Sideband:

This connection is used for parameter exchanges, register accesses for debug/compliance and
coordination with remote partner for Link training and management. It consists of a forwarded
clock pin and a data pin in each direction. The clock is fixed at 800 MHz regardless of the
mainband data rate. The sideband logic for the UCIe Physical Layer must be on auxiliary power
and an "always on" domain. Each module has its own set of sideband pins.

For the Advanced Package option, a redundant pair of clock and data pins in each direction is
provided for repair.

## 2. Mainband:

This connection constitutes the main data path of UCIe. It consists of a forwarded clock, a data
valid pin, a track pin, and N Lanes of data per module.

For the Advanced Package option, $N = 6 4$ (also referred to as x64) or $N = 3 2$ (also referred to as
x32) and overall four extra pins for Lane repair are provided in the bump map.

For the Standard Package option, $N = 1 6$ (also referred to as x16) or $N = 8$ (also referred to as x8)
and no extra pins for repair are provided.

The Logical Physical Layer coordinates the different functions and their relative sequencing for proper
Link bring up and management (e.g., sideband transfers, mainband training and repair, etc.).
Chapter 4.0 and Chapter 5.0 cover the details on Physical Layer operation.

### 1.1.4 Interfaces

UCIe defines the interfaces between the Physical Layer and the D2D Adapter (Raw D2D Interface),
and the D2D Adapter and the Protocol Layer (Flit-aware D2D Interface) in Chapter 10.0. A reference
list of signals is also provided to cover the interactions and rules of the Management Transport
protocol between the SoC and the UCIe Stack.

The motivation for this is two-fold:

. Allow vendors and SoC builders to easily mix and match different layers from different IP
providers at low integration cost and faster time to market. (For example, getting a Protocol Layer
to work with the D2D Adapter and Physical Layer from any different vendor that conforms to the
interface handshakes provided in the UCIe Specification.)

· Given that inter-op testing during post-silicon has greater overhead and cost associated with it, a
consistent understanding and development of Bus Functional Models (BFMs) can allow easier IP
development for this stack.

### 1.2 UCIe Configurations

This section describes the different configurations and permutations permitted for UCIe operation.

#### 1.2.1 Single Module Configuration

A single Module configuration is a x64 or x32 data interface in an Advanced Package, as shown in
Figure 1-10. A single module configuration is a x16 or a x8 data interface in a Standard Package, as
shown in Figure 1-11. A x8 Standard Package module is only permitted for a single module
configuration and is primarily provided for pre-bond test purposes. In multiple instantiations of a
single module configuration where each module has its own dedicated Adapter, they operate
independently (e.g., they could be transferring data at different data rates and widths).

<figure>
<figcaption>Figure 1-10. Single module configuration: Advanced Package</figcaption>

Die-to-Die Adapter

PHY Logic

Sideband

Electrical/AFE

x64
or
x32

Valid
Track

Sideband

FW-CLK

</figure>

<figure>
<figcaption>Figure 1-11. Single module configuration: Standard Package</figcaption>

Die-to-Die Adapter

PHY Logic

Sideband

Electrical/ AFE

1

x16
or

1

Valid
Track

Sideband

FW-CLK

×8

</figure>

#### 1.2.2 Multi-module Configurations

This specification allows for two and four module configurations. When operating with a common
Adapter, the modules in two-module and four-module configurations must operate at the same data
rate and width. Examples of two-module and four-module configurations are shown in Figure 1-12
through Figure 1-14.

<figure>
<figcaption>Figure 1-12. Two-module configuration for Standard Package</figcaption>

Die-to-Die Adapter

Multi-Module PHY Logic

PHY Logic

PHY Logic

Sideband

Electrical/ AFE

Sideband

Electrical/ AFE

I

1

I

1
Valid
Track

1

I

1

Sideband

FW-CLK

x16

Sideband

FW-CLK

x16

Valid
Track

</figure>

<figure>
<figcaption>Figure 1-13. Four-module configuration for Standard Package</figcaption>
</figure>

<table>
<tr>
<th colspan="15">Die-to-Die Adapter</th>
<th></th>
<th></th>
</tr>
<tr>
<td colspan="16">Multi-Module PHY Logic</td>
<td></td>
</tr>
<tr>
<th colspan="4">PHY Logic</th>
<th colspan="4">PHY Logic</th>
<th colspan="4">PHY Logic</th>
<th colspan="4">PHY Logic</th>
<th></th>
</tr>
<tr>
<th>Sideband</th>
<th colspan="3">Electrical/AFE</th>
<th>Sideband</th>
<th colspan="3">Electrical/ AFE</th>
<th>Sideband</th>
<th colspan="3">Electrical/ AFE</th>
<th>Sideband</th>
<th colspan="3">Electrical/ AFE</th>
<th></th>
</tr>
<tr>
<td>1 Sideband</td>
<td>FW-CLK</td>
<td>x16</td>
<td>Valid Track</td>
<td>1 Sideband</td>
<td>FW-CLK</td>
<td>x16</td>
<td>Valid Track</td>
<td>1 Sideband</td>
<td>FW-CLK</td>
<td>x16</td>
<td>Valid Track</td>
<td>Sideband</td>
<td>FW-CLK</td>
<td>x16</td>
<td>Valid Track</td>
<td></td>
</tr>
</table>

Figure 1-14. Example of a Two-module Configuration for Advanced Package

<table>
<tr>
<th colspan="8">Die-to-Die Adapter</th>
</tr>
<tr>
<th colspan="8">Multi-Module PHY Logic</th>
</tr>
<tr>
<th colspan="4">PHY Logic</th>
<th colspan="4">PHY Logic</th>
</tr>
<tr>
<td>Sideband</td>
<td colspan="3">Electrical/ AFE</td>
<td>Sideband</td>
<td></td>
<td colspan="2">$\mathrm { E l e c t r i c a l l } / \mathrm { A F E }$</td>
</tr>
<tr>
<td rowspan="2">Sideband</td>
<td rowspan="2">I I FW-CLK</td>
<td>x64 Or</td>
<td>I Valid Track</td>
<td rowspan="2">1 Sideband</td>
<td>1 FW-CLK I</td>
<td>×64 Or</td>
<td rowspan="2">Valid Track</td>
</tr>
<tr>
<td>x32</td>
<td></td>
<td></td>
<td>x32</td>
</tr>
</table>

<figure>
</figure>

#### 1.2.3 Sideband-only Configurations

A Standard Package UCIe sideband-only configuration is permitted for test or manageability
purposes. This can be a one, two, or four sideband-only ports as part of the same UCIe sideband-only
Link. Figure 1-15, Figure 1-16, and Figure 1-17 show examples of these configurations. See
Section 5.7.4 for more details.

<figure>
<figcaption>Figure 1-15. One-port Sideband-only Link</figcaption>

PHY Logic

Sideband

Sideband

</figure>

<figure>
<figcaption>Figure 1-16. Two-port Sideband-only Link</figcaption>

PHY Logic

Sideband

Sideband

Sideband

</figure>

<figure>
<figcaption>Figure 1-17. Four-port Sideband-only Link</figcaption>

PHY Logic

Sideband

Sideband

Sideband

Sideband

Sideband

</figure>

### 1.3 UCIe Retimers

As described previously, UCIe Retimers are used to enable different types of Off Package
Interconnects to extend the channel reach between two UCIe Dies on different packages. Each UCIe
Retimer has a local UCIe Link connection to a UCIe die on-package as well as an external connection
for longer reach. Figure 1-18 shows a high level block diagram demonstrating a system utilizing UCIe
Retimers to enable an Off Package Interconnect between UCIe Die 0 and UCIe Die 1. UCIe Retimer 0
and UCIe Die 0 are connected through UCIe Link 0 within Package 0. UCIe Retimer 1 and UCIe Die 1
are connected through UCIe Link 1 within Package 1. The terminology of "remote Retimer partner" is
used to reference the UCIe Retimer die connected to the far side of the Off Package Interconnect.

<figure>
<figcaption>Figure 1-18. Block Diagram for UCIe Retimer Connection</figcaption>

Package 0

Package 1

SB

Retimer
Receiver Buffer

SB

UCIe Link 0

Off Package
Interconnect

UCIe Link 1

UCIe Die 0

Retimer
Receiver Buffer

UCIe Retimer 0

UCIe Retimer 1

UCIe Die 1

</figure>

The responsibility of a UCIe Retimer include:

· Reliable Flit transfer across the Off Package Interconnect. Three options are available for
achieving this as described below:

\- The Retimer is permitted to use the FEC and CRC natively defined by the underlying
specification of the protocol it carries (e.g., PCIe or CXL) as long as the external interconnect
conforms to the underlying error model (e.g., BER and error correlation) of the specification
corresponding to the protocol it transports. The UCIe Links would be setup to utilize the Raw
Format to tunnel native bits of the protocol it transports (e.g., PCIe or CXL Flits). In this
scenario, the queue sizes (Protocol Layer buffers) must be adjusted on the UCIe Dies to meet
the underlying round trip latency.

\- The Retimer is permitted to provide the necessary FEC, CRC and Retry capabilities to handle
the BER of the Off Package Interconnect. In this case, the Flits undergo three independent
Links; each UCIe Retimer performs an independent ACK/NAK for Retry with the UCIe die
within its package and a separate independent ACK/NAK for Retry with the remote Retimer

partner. For this scenario, protocols are permitted to use any of the applicable Flit Formats for
transport over the UCIe Link.

\- The Retimer provides its own FEC by replacing the native PCIe or CXL defined FEC with its
own, or adding its FEC in addition to the native PCIe or CXL defined FEC, but takes advantage
of the built in CRC and Replay mechanisms of the underlying protocol. In this scenario, the
queue sizes (Protocol Layer buffers, Retry buffers) must be adjusted on the UCIe Dies to meet
the underlying round trip latency.

· Resolution of Link and Protocol Parameters with remote Retimer partner to ensure interoperability
between UCIe Dies end-to-end (E2E). For example, Retimers are permitted to force the same Link
width, speed, protocol (including any relevant protocol specific parameters) and Flit Formats on
both Package 0 and Package 1 in Figure 1-18. The specific mechanism of resolution including
message transfer for parameter exchanges across the Off Package Interconnect is
implementation specific for the Retimers and they must ensure a consistent operational mode
taking into account their own capabilities along with the UCIe Die capabilities on both Package 0
and Package 1. However, for robustness of the UCIe Links to avoid unnecessary timeouts in case
the external interconnect requires a longer time to Link up or resolution of parameters with
remote Retimer partner, UCIe Specification defines a "Stall" response to the relevant sideband
messages that can potentially get delayed. The Retimers must respond with the "Stall" response
within the rules of UCIe Specification to avoid such unnecessary timeouts while waiting for, or
negotiating with remote Retimer partner. It is the responsibility of the Retimer to ensure the UCIe
Link is not stalled indefinitely.

. Resolution of Link States for Adapter Link State Machine (LSM) or the RDI states with remote
Retimer partner to ensure correct E2E operation. See Chapter 3.0 for more details.

· Flow control and back-pressure:

\- Data transmitted from a UCIe Die to a UCIe Retimer is flow-controlled using credits. These
credits are on top of any underlying protocol credit mechanism (such as PH, PD credits in
PCIe). These UCIe D2D credits must be for flow control across the two UCIe Retimers and any
data transmitted to the UCIe Retimer must eventually be consumed by the remote UCIe die
without any other dependency. Every UCIe Retimer must implement a Receiver Buffer for Flits
that it receives from the UCIe die within its package. The Receiver buffer credits are
advertised to the UCIe die during initial parameter exchanges for the D2D Adapter, and the
UCIe die must not send any data to the UCIe Retimer if it does not have a credit for it. One
credit corresponds to 256B of data (including any FEC, CRC, etc.). Credit returns are
overloaded on the Valid framing (see Section 4.1.2). Credit counters at the UCIe Die are re-
assigned to their initial advertised value whenever RDI states transition away from Active.
UCIe Retimer must drain or dump (as applicable) the data in its receiver buffer before re-
entering Active state.

\- Data transmitted from a UCIe Retimer to a UCIe die is not flow-controlled at the D2D adapter
level. The UCIe Retimer may have its independent flow-control with the other UCIe Retimer if
needed, which is beyond the scope of this specification.

### 1.4 UCIe Key Performance Targets

Table 1-4 gives a summary of the performance targets for UCIe Advanced and Standard Package
configurations. Table 1-5 gives a summary of the performance targets for UCIe-3D.

<table>
<caption>Table 1-4. UCIe 2D and 2.5D Key Performance Targets</caption>
<tr>
<th>Metric</th>
<th>Link Speed/ Voltage</th>
<th>Advanced Package (x64)</th>
<th>Standard Package</th>
</tr>
<tr>
<td rowspan="8">Die Edge Bandwidth Densityª (GB/s per mm)</td>
<td>4 GT/s</td>
<td>165</td>
<td>28</td>
</tr>
<tr>
<td>$8 \quad G T / s$</td>
<td>329</td>
<td>56</td>
</tr>
<tr>
<td>12 GT/s</td>
<td>494</td>
<td>84</td>
</tr>
<tr>
<td>$1 6 \quad G T / s$</td>
<td>658</td>
<td>112</td>
</tr>
<tr>
<td>24 GT/s</td>
<td>988</td>
<td>168</td>
</tr>
<tr>
<td>32 GT/s</td>
<td>1317</td>
<td>224</td>
</tr>
<tr>
<td>48 GT/s</td>
<td>$1 9 7 5$</td>
<td>278b</td>
</tr>
<tr>
<td>64 GT/s</td>
<td>2634</td>
<td>370b</td>
</tr>
<tr>
<td rowspan="6">Energy Efficiencyc (pJ/bit)</td>
<td rowspan="3">$\begin{array}{} { 0 . 7 V } \\ { \text { \left(Supply voltage } } \end{array}$</td>
<td>$0 . 5 \left( < = 1 2 \quad G T / s \right)$</td>
<td>$0 . 5 \left( 4 \quad G T / s \right)$</td>
</tr>
<tr>
<td>$0 . 6 \left( > = 1 6 \quad G T / s \right)$</td>
<td>1.0 $\left( < = 1 6 \quad G T / s \right)$</td>
</tr>
<tr>
<td>-</td>
<td>$1 . 2 5 \left( > = 2 4 \quad G T / s \right)$</td>
</tr>
<tr>
<td rowspan="3">$\begin{array}{} { 0 . 5 V } \\ { \text { \left(Supply Voltage } } \end{array}$</td>
<td>$0 . 2 5 \left( < = 1 2 \quad G T / s \right)$</td>
<td>$0 . 5 \left( < = 1 6 \quad G T / s \right)$</td>
</tr>
<tr>
<td>$0 . 3 \left( > = 1 6 \quad G T / s \right.$ $\mathrm { a n d } < = 3 2$</td>
<td rowspan="2">$0 . 7 5 \left( > = 3 2 \quad G T / s \right)$</td>
</tr>
<tr>
<td>$0 . 5 \left( > = 4 8 \quad G T / s \right)$</td>
</tr>
<tr>
<td>$\text { Latency Target } ^ { 0 }$</td>
<td></td>
<td>$< = 2 n s$</td>
<td></td>
</tr>
</table>

a. Die edge bandwidth density is defined as total I/O bandwidth in GB per sec per mm silicon die edge, with 45-
um (Advanced Package) and 110-um (Standard Package) bump pitch. For a x32 Advanced Package module,
the Die Edge Bandwidth Density is 50% of the corresponding value for

b. Die edge bandwidth density for Standard Package at 48 GT/s and 64 $G T / s \quad i s \quad l e s s \quad t h a n \quad 2 x \quad o f \quad t h a t \quad a t \quad 2 4 \quad G T / s$
and 32 GT/s, respectively. This is because of increased die edge to improve
rates. Future revisions of the specification will look at addressing this.

c. Energy Efficiency (energy consumed per bit to traverse from FDI to bump and back to FDI) includes all the
Adapter and Physical Layer-related circuitry including, but not limited to, Tx, Rx, PLL, Clock Distribution, etc.
Channel reach and termination are discussed in Chapter 5.0.

d. Latency includes the latency of the Adapter and the Physical Layer (FDI to bump delay) on Tx and Rx. See
Chapter 5.0 for details of Physical Layer latency. Latency target is based on 16 GT/s. Latency at other data
rates may differ due to data rate-dependent aspects such as data accumulation and transfer time. Note that
the latency target does not include the accumulation of bits required for processing; either within or across
Flits.

<table>
<caption>Table 1-5. UCIe-3D Key Performance Targets</caption>
<tr>
<th>Metric</th>
<th>Link Speed/Voltage</th>
<th>UCIe-3D</th>
</tr>
<tr>
<td></td>
<td>4 GT/s</td>
<td>4000</td>
</tr>
<tr>
<td>$\begin{array}{} { \left. \text { \left(GB/s/mm } ^ { 2 } \right) } \\ { \text { Energy Efficiency^{b } } } \\ { \text { \left(pJ/bit\right) } } \end{array}$</td>
<td>0.65 V (Supply Voltage)</td>
<td>0.05</td>
</tr>
<tr>
<td>Latency Targetc</td>
<td></td>
<td>$< = 1 2 5 \quad p s$</td>
</tr>
</table>

a. Bandwidth Density is provided for a 9-um bump pitch.

b. Energy Efficiency (energy consumed per bit) includes all the Tx, Rx, PLL, Clock Distribution, etc.

c. Latency includes the latency on Tx and Rx.

## 1.5 Interoperability

Package designers need to ensure that Dies that are connected on a package can inter-operate. This
includes compatible package interconnect (e.g., Advanced vs. Standard), protocols, voltage levels,
etc. It is strongly recommended that a Die adopts Transmitter voltage of less than 0.85 V so that the
Die can inter-operate with a wide range of process nodes in the foreseeable future.

This specification comprehends interoperability across a wide range of bump pitch for Advanced
Packaging options. It is expected that over time, the smaller bump pitches will be predominantly
used. With smaller bump pitch, we expect designs will reduce the maximum advertised data rate
(even though they can go to 64 GT/s) to optimize for area and to address the power delivery and
thermal constraints of high bandwidth with reduced area. Table 1-6 summarizes these bump pitches
across four groups. Interoperability is guaranteed within each group as well as across groups, based
on the PHY dimension specified in Chapter 5.0. The performance targets provided in Table 1-4 are
with the 45 um bump pitch.

<table>
<caption>Table 1-6. Groups for Different Advanced Package Bump Pitches</caption>
<tr>
<th>Bump Pitch (um)</th>
<th>Minimum Data Rate (GT/s)</th>
<th>Expected Maximum Data Rate (GT/s)</th>
</tr>
<tr>
<td>Group 1: 25 - 30</td>
<td>4</td>
<td>24</td>
</tr>
<tr>
<td>Group 2: 31 - 37</td>
<td>4</td>
<td>32</td>
</tr>
<tr>
<td>Group 3: 38 - 44</td>
<td>4</td>
<td>48</td>
</tr>
<tr>
<td>Group 4: 45 - 55</td>
<td>4</td>
<td>64</td>
</tr>
</table>

Interoperability between Standard Package implementations of different die edge measurements
(e.g., a maximum data rate of 64 GT/s implementation connected to a maximum data rate of
32 GT/s implementation) will require a minimum die gap in the package to ensure that there is
sufficient space for the individual Lane connections to adjust for the die edge differences.

## 2.0 Protocol Layer

Universal Chiplet Interconnect express (UCIe) maps PCIe and CXL, as well as any Streaming protocol.
Throughout the UCIe Specification, Protocol-related features are kept separate from Flit Formats and
packetization. This is because UCIe provides different transport mechanisms that are not necessarily
tied to protocol features (e.g., PCIe non-Flit mode packets are transported using CXL.io 68B Flit
Format). Protocol features include the definitions of Transaction Layer and higher layers, as well as
Link Layer features not related to Flit packing/Retry (e.g., Flow Control negotiations etc.).

The following terminology is used throughout this specification to identify Protocol-level features:

· PCIe Flit mode: To reference Flit mode-related Protocol features defined in PCIe Base Specification

· PCIe non-Flit mode: To reference non-Flit mode-related Protocol features defined in PCIe Base
Specification

· CXL 68B Flit mode: To reference 68B Flit mode-related Protocol features defined in CXL
Specification

· CXL 256B Flit mode: To reference 256B Flit mode-related Protocol features defined in $C X L$
Specification

The following protocol mappings are supported over the UCIe mainband:

· PCIe Flit mode

· CXL 68B Flit mode, CXL 256B Flit Mode: If CXL is negotiated, each of CXL.io, CXL.cache, and
CXL.mem protocols are negotiated independently.

· Streaming protocol: This offers generic modes for a user defined protocol to be transmitted using
UCIe.

· Management Transport protocol: This allows transport of manageability packets.

Note:
RCD/RCH/eRCD/eRCH are not supported. PCIe non-Flit Mode is supported using CXL.io
68B Flit Format as the transport mechanism.

The Protocol Layer requirements for interoperability for PCIe and CXL are as follows:

· CXL 68B Flit Mode and PCIe Non-Flit Mode are not supported if the negotiated maximum data rate
(see Section 4.5.3.3.1 to see how the maximum data rate is negotiated) is greater than
32 GT/s.

. A Protocol Layer must support PCIe non-Flit mode if it is advertising the 68B Flit Mode parameter
from Table 3-1.

. If a Protocol Layer supports CXL 256B Flit Mode, it must support PCIe Flit Mode. If a Protocol
Layer supports CXL 256B Flit Mode and the negotiated maximum data rate is less than or equal to
32 GT/s, that Protocol Layer must also support 68B Flit Mode.

. A Protocol Layer advertising CXL is permitted to only support CXL 68B Flit Mode without
supporting CXL 256B Flit Mode or PCIe Flit Mode. If so, the UCIe Link must not negotiate a
maximum data rate greater than 32 GT/s with its remote Link partner.

# IMPLEMENTATION NOTE

$T a b l e \quad 2 - 1$ summarizes the mapping of the above rules from a specification version to a protocol
mode.

<table>
<caption>Table 2-1. Specification to Protocol Mode Requirements</caption>
<tr>
<th>Native Specification Supportedª</th>
<th>Negotiated Maximum Data Rate</th>
<th>PCIe Non-Flit Mode</th>
<th>CXL 68B Flit Mode</th>
<th>CXL 256B Flit Mode</th>
<th>PCIe Flit Mode</th>
</tr>
<tr>
<td rowspan="2">PCIe</td>
<td>&lt;= 32 GT/s</td>
<td>Mandatory</td>
<td>N/A</td>
<td>N/A</td>
<td>Optional</td>
</tr>
<tr>
<td>&gt; 32 GT/s</td>
<td>Not Supported</td>
<td>N/A</td>
<td>N/A</td>
<td>Mandatory</td>
</tr>
<tr>
<td rowspan="2">$\csc 2 . 0$</td>
<td>&lt;= 32 GT/s</td>
<td>Mandatory (for CXL.io)</td>
<td>Mandatory</td>
<td>N/A</td>
<td>N/A</td>
</tr>
<tr>
<td>&gt; 32 GT/s</td>
<td>Not Supported</td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td rowspan="2">CXL 3.0</td>
<td>&lt;= 32 GT/s</td>
<td>Mandatory (for CXL.io)</td>
<td>Mandatory</td>
<td>Mandatory</td>
<td>Mandatory (for CXL.io)</td>
</tr>
<tr>
<td>&gt; 32 GT/s</td>
<td>Not Supported</td>
<td></td>
<td>Mandatory</td>
<td>$\begin{array}{} { \text { Mandatory } } \\ { \text { \left(for cXL.io } } \end{array}$</td>
</tr>
</table>

a. The same table applies to derivative version numbers for the specifications.

The Die-to-Die (D2D) Adapter negotiates the protocol with the remote Link partner and
communicates it to the Protocol Layer(s). For each protocol, UCIe supports multiple modes of
operation (that must be negotiated with the remote Link partner depending on the advertised
capabilities, Physical Layer Status as well as usage models). These modes have different Flit Formats
and are defined to enable different trade-offs around efficiency, bandwidth and interoperability. The
spectrum of supported protocols, advertised modes and Flit Formats must be determined at SoC
integration time or during the Die-specific reset bring up flow. The Die-to-Die Adapter uses this
information to negotiate the operational mode as a part of Link Training and informs the Protocol
Layer over the Flit-aware Die-to-Die Interface (FDI). See Section 3.2 for parameter exchange rules in
the Adapter.

The subsequent sections provide an overview of the different modes from the Protocol Layer's
perspective, hence they cover the supported formats of operation as subsections per protocol. The
Protocol Layer is responsible for transmitting data over FDI in accordance with the negotiated mode
and Flit Format. The illustrations of the Flit Formats in this chapter show an example configuration of
a 64B data path in the Protocol Layer mapped to a 64-Lane module of Advanced Package
configuration on the Physical Link of UCIe. Certain Flit Formats have dedicated bit positions filled in by
the Adapter, and details associated with these are illustrated separately in Chapter 3.0. For other Link
widths, see the Byte to Lane mappings defined in Section 4.1.1. Figure 2-1 shows the legend for
color-coding convention used when showing bytes within a Flit in the Flit Format examples in the UCIe
Specification.

<table>
<caption>Figure 2-1. Color-coding Convention in Flit Format Byte Map Figures</caption>
<tr>
<th>Color Shading</th>
<th>Description</th>
</tr>
<tr>
<td></td>
<td>Some bits populated by the Protocol Layer, some bits populated by the Adapter.</td>
</tr>
<tr>
<td></td>
<td>All bits populated by Adapter.</td>
</tr>
<tr>
<td></td>
<td>All bits populated by the Protocol Layer.</td>
</tr>
</table>

## 2.1 PCIe

UCIe supports the Flit Mode defined in PCIe Base Specification. See PCIe Base Specification for the
protocol definition. UCIe supports the non-Flit Mode using the CXL.io 68B Flit Formats as the transport
mechanism. There are five UCIe operating formats supported for PCIe, and these are defined in the
subsections that follow.

### 2.1.1 Raw Format

This format is optional. All bytes are populated by the Protocol Layer. The intended usage is for UCIe
Retimers transporting PCIe protocol. An example usage of this format is where a CPU and an I/O
Device are in different Rack/chassis and connected through a UCIe Retimer using Off-Package
Interconnect as shown in Figure 1-2. Retry, CRC and FEC (if applicable) are taken care of by the
Protocol Layer when using Raw Format. It is strongly recommended for the UCIe Retimers to check
and count errors using either the parity bits of the 6B FEC or the Flit Mode 8B CRC defined in PCIe
Base Specification for this mode to help characterize the Off Package Interconnect (to characterize or
debug the Link that is the dominant source of errors). See Section 3.3.1 as well.

### 2.1.2 Standard 256B End Header Flit Format

This format is mandatory when PCIe Flit Mode protocol is supported. It is the standard Flit Format
defined in PCIe Base Specification for Flit Mode and the main motivation of supporting this Flit Format
is to enable interoperability with vendors that only support the standard PCIe Flit Formats. The
Protocol Layer must follow the Flit Formats for Flit transfer on FDI, driving 0 on the fields reserved for
Die-to-Die Adapter. The PM and Link Management DLLPs are not used over UCIe. The other DLLPs
(that are applicable for PCIe Flit Mode) and Flit Status definitions follow the same rules including
packing as defined in PCIe Base Specification. It is strongly recommended for implementations to
optimize out any 8b/10b, 128b/130b, and non-Flit Mode related CRC/Retry or framing logic from the
Protocol Layer in order to obtain area and power efficient designs for UCIe applications. Portions of
the DLP bytes must be driven by the Protocol Layer for Flit_Marker assignment; see Section 3.3.3 for
details of the Flit Format.

### 2.1.3 68B Flit Format

This mode is mandatory when PCIe protocol or CXL protocol is supported and the negotiated
maximum data rate is <= 32 GT/s. The transport mechanism for this is the same as CXL.io 68B Flit
Formats. See Section 2.3.2 for the CXL.io DLLP rules that apply for Non-Flit Mode for PCIe as well. It
is strongly recommended for implementations to optimize out any 8b/10b, 128b/130b and non-Flit
Mode related CRC/Retry logic from the Protocol Layer in order to obtain area and power efficient
designs for UCIe applications. To keep the framing rules consistent, Protocol Layer for PCIe non-Flit
mode must still drive the LCRC bytes with a fixed value of 0, and the Receiver must ignore these
bytes and never send any Ack or Nak DLLPs. Framing tokens are applied as defined for CXL.io 68B Flit
Mode operation in CXL Specification. It is recommended for the transmitter to drive the sequence
number, DLLP CRC, Frame CRC and Frame parity in STP to 0; the receiver must ignore these fields.
Given that UCIe Adapter provides reliable Flit transport, framing errors, if detected by the Protocol
Layer, are likely due to uncorrectable internal errors and it is permitted to treat them as such.

### 2.1.4 Standard 256B Start Header Flit Format

This is an optional format for PCIe Flit Mode, supported if Standard Start Header for PCIe protocol
Capability is supported. The Protocol Layer must follow the Flit Formats for Flit transfer on FDI, driving
0 on the fields reserved for Die-to-Die Adapter. The PM and Link Management DLLPs are not used over
UCIe. The other DLLPs (that are applicable for PCIe Flit Mode) and Flit Status definitions follow the
same rules including packing as defined in PCIe Base Specification. It is strongly recommended for

implementations to optimize out any 8b/10b, 128b/130b and non-Flit Mode related CRC/Retry or
framing logic from the Protocol Layer in order to obtain area and power efficient designs for UCIe
applications. Portions of the DLP bytes must be driven by the Protocol Layer for Flit_Marker
assignment; see Section 3.3.3 for details of the Flit Format.

### 2.1.5 Latency-Optimized 256B with Optional Bytes Flit Format

This is an optional format for PCIe Flit Mode, supported if Latency-Optimized Flit with Optional Bytes
for PCIe protocol capability is supported. It is the Latency-Optimized Flit with Optional Bytes Flit
Format for PCIe, as defined in Section 3.3.4. The Protocol Layer must follow the Flit Formats for Flit
transfer on FDI, driving 0 on the fields reserved for Die-to-Die Adapter. The PM and Link Management
DLLPs are not used over UCIe. The other DLLPs (that are applicable for PCIe Flit Mode) and Flit Status
definitions follow the same rules including packing as defined in PCIe Base Specification. It is strongly
recommended for implementations to optimize out any 8b/10b, 128b/130b and non-Flit Mode related
CRC/Retry or framing logic from the Protocol Layer in order to obtain area and power efficient designs
for UCIe applications. Portions of the DLP bytes must be driven by the Protocol Layer for Flit_Marker
assignment; see Section 3.3.4 for details of the Flit Format.

## 2.2 CXL 256B Flit Mode

See CXL Specification for details on the protocol layer messages and slot formats for "CXL 256B Flit
Mode". There are four possible operational formats for this protocol mode (there are two formats in
Section 2.2.3), defined in the subsections that follow. The light orange bytes are inserted by the
Adapter (see Figure 2-1). In cases where these are shown as part of the main data path (e.g., in the
Standard 256B Flit Format), the Protocol Layer must drive 0 on them on the Transmitter, and ignore
them on the Receiver.

### 2.2.1 Raw Format

This format is optional. All bytes are populated by the Protocol Layer. The intended usage is for UCIe
Retimers transporting CXL 256B Flit Mode protocol. An example usage of this format is where a CPU
and an I/O Device are in different Rack/chassis and connected through a UCIe Retimer using Off-
Package Interconnect. Retry, CRC and FEC are taken care of by the Protocol Layer. It is strongly
recommended for the UCIe Retimers to check and count errors using either the parity bits of the 6B
FEC or the Flit Mode 8B CRC or 6B CRC; depending on which Flit Format was enabled. This helps to
characterize and debug the Off-Package Interconnect which is the dominant source of errors. For
CXL.cachemem, Viral or poison containment (if applicable) must be handled within the Protocol Layer
for this format. See Section 3.3.1 as well.

### 2.2.2 Latency-Optimized 256B Flit Formats

The support for this format is strongly recommended for "CXL 256B Flit Mode" over UCIe. Two Flit
Formats are defined, which provide two independent operating points. These formats are derived
from the Latency-Optimized Flits defined in CXL Specification. The only difference for the second Flit
Format is that it gives higher Flit packing efficiency by providing Protocol Layer with extra bytes. For
CXL.io this results in extra 4B of TLP information, and for CXL.cachemem it results in an extra 14B H-
slot that can be packed in the Flit. This slot is ordered between Slots 7 and 8. It is included in both
Groups B and C, similar to Slot 7. See CXL Specification for reference of the packing rules. Support for
the first or second format is negotiated at the time of Link bring up. See Section 3.3.4 for the details
for the Flit Formats.

The Latency-Optimized formats enable the Protocol Layer to consume the Flit at 128B boundary,
reducing the accumulation latency significantly. When this format is negotiated, the Protocol Layer

must follow this Flit Format for Flit transfer on FDI, driving 0 on the fields reserved for Die-to-Die
Adapter.

The Ack, Nak, PM, and Link Management DLLPs are not used over UCIe for CXL.io for any of the 256B
Flit Modes. The other DLLPs and Flit_Marker definitions follow the same rules as defined in CXL
Specification. Portions of the DLP bytes must be driven by the Protocol Layer for Flit_Marker
assignment; see Section 3.3.3 for details on how DLP bytes are driven.

For CXL.cachemem for this mode, FDI provides an lp_corrupt_crc signal to help optimize for
latency while guaranteeing Viral containment. See Chapter 10.0 for details of interface rules for Viral
containment.

### 2.2.3 Standard 256B Start Header Flit Format

This format is mandatory when "CXL 256B Flit Mode" protocol is supported. It is the Standard 256B
Flit Format defined in CXL Specification for 256B Flit Mode and the main motivation of supporting this
Flit Format is to enable interoperability with vendors that only support the Standard 256B Flit
Formats. The Protocol Layer must follow the Flit Formats for Flit transfer on FDI, driving 0 on the
fields reserved for Die-to-Die Adapter. The Ack, Nak, PM, and Link Management DLLPs are not used
over UCIe for CXL.io. The other DLLPs and Flit Status definitions follow the same rules and packing as
defined in CXL Specification. Portions of the DLP bytes must be driven by the Protocol Layer for
Flit_Marker assignment; see Section 3.3.3 for details of the Flit Formats and on how DLP bytes are
driven.

For CXL.cachemem in this format, FDI provides an lp_corrupt_crc signal to help optimize for
latency while guaranteeing Viral containment. See Section 10.2 for details of interface rules for Viral
containment.

See Section 3.3.3 for details about this Flit Format.

## 2.3 CXL 68B Flit Mode

The CXL Specification provides details on the protocol layer messages and slot formats for CXL 68B
Flit Mode. There are two operational formats possible for this protocol, and these are defined in the
subsections that follow. The light orange bytes are inserted by the Adapter (see Figure 2-1). This
protocol is not supported if the negotiated maximum data rate is > 32 GT/s.

### 2.3.1 Raw Format

This format is optional. All bytes are populated by the Protocol Layer. The intended usage is for UCIe
Retimers transporting "CXL 68B Flit Mode" protocol. An example usage of this format is where a CPU
and an I/O Device are in different Rack/chassis and connected through a UCIe Retimer using an Off-
Package Interconnect. Retry and CRC are taken care of by the Protocol Layer. See Section 3.3.1 as
well.

### 2.3.2 68B Flit Format

This format is mandatory when CXL 68B Flit Mode protocol is negotiated and the negotiated maximum
data rate is <= 32 GT/s. When supported, this follows the corresponding 68B Flit Format defined in
CXL Specification and the main motivation of supporting this Flit Format is to enable interoperability
with vendors that only support the baseline CXL formats. The Protocol Layer presents 64B of the Flit
(excluding the Protocol ID and CRC) on FDI (shown in Figure 2-2), and the Die-to-Die Adapter inserts
a 2B Flit Header and 2B CRC and performs the byte shifting required to arrange the Flits in the format
shown in Figure 3-11.

The Ack, Nak, and PM DLLPs are not used for CXL.io in this mode. Credit updates and other remaining
DLLPs for CXL.io are transmitted in the Flits as defined in CXL Specification. For CXL.io, the
Transmitter must not implement Retry in the Protocol Layer (because Retry is handled in the
Adapter). To keep the framing rules consistent, Protocol Layer for CXL.io must still drive the LCRC
bytes with a fixed value of 0, and the Receiver must ignore these bytes and never send any Ack or
Nak DLLPs. Framing tokens are applied as defined for CXL.io 68B Flit Mode operation. It is
recommended for the transmitter to drive the sequence number, DLLP CRC, Frame CRC and Frame
parity in STP to 0. The receiver must ignore these fields. Given that UCIe Adapter provides reliable Flit
transport, framing errors, if detected by the Protocol Layer are likely due to uncorrectable internal
errors and it is permitted to treat them as such.

For CXL.cachemem, the "Ak" field defined by CXL Specification in the Flit is reserved, and the Retry
Flits are not used (because Retry is handled in the Adapter). Link Initialization begins with sending the
INIT.Param Flit without waiting for any received Flits. Viral containment (if applicable) must be
handled within the Protocol Layer for the 68B Flit Mode. CXL Specification introduced Error Isolation
as a way to reduce the blast radius of downstream component fatal errors compared to CXL Viral
Handling and provide a scalable way to handle device failures across a network of switches shared
between multiple Hosts. Specifically, Viral relies on a complete host reset to recover whereas Error
Isolation may recover by resetting the virtual hierarchy below the root port. Because CXL-defined
Retry Flits (which carry the viral notification for 68B Flits in CXL) are not used in 68B Flit mode in
UCIe, it is recommended for implementations to rely on error isolation at the CXL Root Port for fatal
errors on CXL.cachemem downstream components in 68B Flit mode (similar to Downstream Port
Containment for CXL.io).

Figure 2-2. 68B Flit Format on FDIª

+0

Byte 0

64B (from Protocol Layer)
$+ 6 3$

a. See Figure 2-1 for color mapping.

# 2.4 Streaming Protocol

This is the default protocol that must be advertised if none of the PCIe or CXL protocols are going to
be advertised and negotiated with the remote Link partner. If Streaming Flit Format capability is not
supported, then the operational formats that can be used are either Raw Format or vendor defined
extensions. Streaming Flit Format capability is supported if any of 68B Flit Format for Streaming
Protocol, Standard 256B End Header Flit Format for Streaming Protocol, Standard 256B Start Header
Flit Format for Streaming Protocol, Latency-Optimized 256B Flit Format without Optional Bytes for
Streaming Protocol or Latency-Optimized 256B Flit Format with Optional Bytes for Streaming Protocol
bits are set in the UCIe Link Capability register.

## 2.4.1 Raw Format

This is mandatory for Streaming protocol support in Adapter implementations. Protocol Layer
interoperability is vendor defined. All bytes are populated by the Protocol Layer. See Section 3.3.1 as
well.

## 2.4.2 68B Flit Format

This format is only applicable if Streaming Flit Format capability is supported. When the negotiated
maximum data rate is <= 32 GT/s, it is an optional format that permits implementations to utilize the
68B Flit Format from the Adapter for Streaming protocols. This format is not supported when the
negotiated maximum data rate $i s > 3 2 \quad G T / s .$ See Section 3.3.2 for details of the Flit Format.

The Protocol Layer presents 64B per Flit on FDI, and the Die-to-Die Adapter inserts a 2B Flit Header
and 2B CRC and performs the byte shifting required to arrange the Flits in the format shown in
Figure 3-11. On the receive data path, the Adapter strips out the Flit Header and CRC bytes to only
present the 64B per Flit to the Protocol Layer on FDI.

## 2.4.3 Standard 256B Flit Formats

This format is only applicable if Streaming Flit Format capability is supported. Implementations are
permitted to utilize the Standard 256B Start Header Flit Format or Standard 256B End Header Flit
Format from the Adapter for Streaming protocols. See Section 3.3.3 for details of the Flit Format and
to see which of the reserved fields in the Flit Header are driven by the Protocol Layer. The Protocol
Layer presents 256B per Flit on FDI, driving 0b on the bits reserved for the Adapter. The Adapter fills
in the applicable Flit Header and CRC bytes. On the Rx datapath, the Adapter forwards the Flit
received from the Link as it is, and the Protocol Layer must ignore the bits reserved for the Adapter
(for example the CRC bits).

## 2.4.4 Latency-Optimized 256B Flit Formats

This format is applicable only when Streaming Flit Format capability is supported. Implementations
are permitted to utilize the Latency-Optimized 256B with Optional Bytes Flit Format or Latency-
Optimized 256B without Optional Bytes Flit Format for Streaming protocols. See Section 3.3.4 for
details of the Flit Format and to see which of the reserved fields in the Flit Header are driven by the
Protocol Layer. The Protocol Layer presents 256B per Flit on FDI, driving 0b on the bits reserved for
the Adapter. The Adapter fills in the applicable Flit Header and CRC bytes. On the Rx datapath, the
Adapter forwards the Flit received from the Link as is, and the Protocol Layer must ignore the bits
reserved for the Adapter (e.g., the CRC bits).

## 2.5 Management Transport Protocol

This protocol is used to carry management network packets over the mainband. The format for these
packets is shown in Section 8.2.2.2. The 68B Flit Format is not permitted for this protocol. Raw format
and any of the 256B Flit Formats are permitted for this protocol. When using the 256B Flit Formats,
the Protocol Layer presents 256B per Flit on the FDI, driving 0 on the bits that are reserved for the
Adapter. The Adapter fills in the applicable Flit Header and CRC bytes. On the Rx data path, the
Adapter forwards the Flit received from the Link as is, and the Management Port Gateway must ignore
the bits reserved for the Adapter (e.g., the CRC bits).

See Section 8.2.5.2.3 for details of mapping the Management Transport Packets (MTPs) over
Management Flits.

### 3.0 Die-to-Die Adapter

The Die-to-Die Adapter is responsible for:

· Reliable data transfer (performing CRC computation and Retry, or parity computation when
applicable)

· Arbitration and Muxing (in case of multiple Protocol Layers)

· Link State Management

· Protocol and Parameter negotiation with the remote Link partner.

Figure 3-1 shows a high level description of the functionality of the Adapter.

<figure>
<figcaption>Figure 3-1. Functionalities in the Die-to-Die Adapter</figcaption>

Protocol Layer

Flit aware
D2D interface

(FDI)

ARB/MUX (when applicable)
CRC/Retry (when applicable)
Link State Management
Parameter Negotiation

Die-to-Die Adapter

Raw D2D interface (RDI)

Physical Layer

Sideband/
Global

Electrical/AFE [k slices]

</figure>

The Adapter interfaces to the Protocol Layer using one or more instances of the Flit-aware Die-to-Die
interface (FDI), and it interfaces to the Physical Layer using the raw Die-to-Die interface (RDI). See
Chapter 10.0 for interface details and operation.

The D2D Adapter must follow the same rules as the Protocol Layer for protocol interoperability
requirements. Figure 3-2 shows example configurations for the Protocol Layer and the Adapter, where
the Protocol identifiers (e.g., PCIe) only signify the protocol, and not the Flit Formats. To provide cost

and efficiency trade-offs, UCIe allows configurations in which two protocol stacks are multiplexed onto
the same physical Link.

#### 3.1 Stack Multiplexing

If the Multi_Protocol_Enable parameter is negotiated, two stacks multiplexed on the same physical
Link is supported when each protocol stack needs half the bandwidth that the Physical Layer provides.
Both stacks must be of the same protocol with the same protocol capabilities. When
Multi_Protocol_Enable and Management Transport protocol are negotiated for mainband and the
Protocol Layer implements the Management Port Gateway multiplexer (MPG mux), the MPG mux must
be present on both stacks and the same protocols must be present in both stacks. For example, in
Figure 8-35 the Multi_Protocol_Enable parameter can be negotiated for config b if both stacks in this
configuration have PCIe or both stacks have Streaming. Similarly, the Multi_Protocol_Enable
parameter can be negotiated for config d in Figure 8-35 if both CXL stacks are identical.

When Multi_Protocol_Enable is supported and negotiated, the Adapter must guarantee that it will not
send consecutive flits from the same protocol stack on the Link. This applies in all cases including
when Flits are sourced from FDI, from Retry Buffer, and when the data stream is paused and
restarted. Adapter is permitted to insert NOP Flits to guarantee this (these Flits bypass the Tx Retry
buffer, and are not forwarded to the Protocol Layer on the receiver). When Flits are transmitted from
the Retry Buffer, it is required to insert NOP Flits as needed to avoid sending consecutive Flits from
the same Protocol stack. When Management Transport protocol is negotiated for mainband with
Multi_Protocol_Enable, the Management Flit carries the same stack identifier as the Protocol Layer it
is multiplexed with. From the Adapter perspective, for the purposes of throttling and interleaving, it is
treated the same as flits received from the corresponding Protocol Layer. Note that there is no fixed
pattern of Flits alternating from different Protocol Layers. For example, a Flit from Protocol Stack 0
followed by a NOP Flit, followed by a Flit from Protocol Stack 0 is a valid transmit pattern. A NOP Flit
is defined as a Flit where the protocol identifier in the Flit Header corresponds to the D2D Adapter,
and the body of the Flit is filled with all 0 data (the NOP Flit is defined for all Flit Formats supported by
the Adapter, for all cases when it is operating in Raw Format). It is permitted for NOP flits to bypass
the Retry buffer, as long as the Adapter guarantees that it is not sending consecutive Flits for any of
the Protocol Layers. On the receiving side, the Adapter must not forward these NOP flits to the
Protocol Layer. The receiving Protocol Layer must be capable of receiving consecutive chunks of the
same Flit at the maximum Link speed, but it will not receive consecutive Flits. In addition to the
transfer rate, both protocol stacks must operate with the same protocol and Flit Formats.
Multi_Protocol_Enable and Raw Format are mutually exclusive. Each stack is given a single bit stack
identifier that is carried along with the Flit header for de-multiplexing of Flits on the Receiver. The
Stack Mux shown maintains independent Link state machines for each protocol stack. Link State
transition-related sideband messages have unique message codes to identify which stack's Link State
Management is affected by that message.

## IMPLEMENTATION NOTE

The primary motivation for enabling the Multi_Protocol_Enable parameter is to allow
implementations to take advantage of the higher bandwidth provided by the UCIe
Link for lower-bandwidth individual Protocol Layers, without the need to make a lot of
changes to the UCIe Link. For example, two Protocol Layers that support the
maximum bandwidth for CXL 68B Flit Mode (i.e., the equivalent of 32 GT/s CXL
SERDES bandwidth) can be multiplexed over a UCIe Link that supports their
aggregate bandwidth.

If the Enhanced Multi_Protocol_Enable parameter is negotiated, dynamic multiplexing between two
stacks of the same or different protocols on the same physical Link is supported. When Enhanced

Multi_Protocol_Enable and Management Transport protocol are negotiated, each stack can have
different protocols with or without MPG mux. For example, in Figure 8-35, the Enhanced
Multi_Protocol_Enable parameter must be negotiated for configs e, f, and h. The parameter is also
negotiated for configs b and d if the two stacks have different protocol pairs. Both protocol stacks and
the Adapter must support a common Flit Format for this feature to be enabled. "Enhanced
Multi_Protocol_Enable" and Raw Format are mutually exclusive. The Adapter must advertise the
maximum percentage of bandwidth that the receiver for each Protocol Layer can accept. The Adapter
transmitter must support 100% (no throttling) and throttling one or both Protocol Layer(s) to 50% of
maximum bandwidth. When 50% of the maximum bandwidth is advertised for a stack by an Adapter,
the remote Link partner must guarantee that it will not send consecutive Flits for the same stack on
the Link. This applies in all cases including when Flits are sourced from FDI, from Retry Buffer, and
when the data stream is paused and restarted. Adapter is permitted to insert NOP Flits to guarantee
this (these Flits bypass the Tx Retry buffer, and are not forwarded to the Protocol Layer on the
receiver). When Flits are transmitted from the Retry Buffer, it is required to insert NOP Flits as needed
to avoid exceeding the negotiated maximum bandwidth. The receiving Protocol Layer must be capable
of sinking Flits at the advertised maximum bandwidth percentage; in addition, Protocol Layer must be
able to receive consecutive chunks of the same Flit at the maximum advertised Link speed. When this
capability is supported, the Adapter must be capable of allowing each Protocol Layer to independently
utilize 100% of the Link bandwidth. Furthermore, the arbitration is per Flit, and the Adapter must
support round robin arbitration between the Protocol Layers if both of them are permitted to use
100% of the Link bandwidth. Additional implementation specific arbitration schemes are permitted as
long as they are per Flit and do not violate the maximum bandwidth percentage advertised by the
remote Adapter for a given stack. The Flit header has a single bit stack identifier to identify the
destination stack for the flit. The Stack Mux maintains independent Link state machines for each
protocol stack. Link State transition-related sideband messages have unique message codes to
identify which stack's Link State Management is affected by that message.

<figure>
<figcaption>Figure 3-2. Example Configurations</figcaption>

Protocol Layer
(PCe orStreaming )

Protocol Layer
$\left( \mathrm { C } \mathrm { M } . \mathrm { i } \mathrm { o } \right)$

Protocol Layer
$\left( \mathrm { C } \mathrm { X } . \mathrm { c a c h e } \mathrm { m e } \mathrm { m } \right)$

FDI

FDI

Die-to-Die Adapter

$A r b / M u x$
Die-to-Die Adapter

RDI

RDI

(a) Single Protocol

(b) Single CXL Stack

Pro tocol Layer
$1 0 \times 1 0$

Pro toco l Layer
(CXL.cachemem)

Pro toco l Layer
(CXL.io)

Pro toco l Layer
(CXL.cachemem)

FDI

$A r b / M u x$

Arb/Mux

Sta ck Mux

Die-to-Die Adapter

RDI

(c) Two CXL stacks multiplexed inside the adapter

Protocol
Layer A

Protocol
Layer B

FDI

Stack Mux
Die-to-Die Adapter

$R D I$

(d) Two Stacks Multiplexed with Enhanced Multi_Protocol_Enable Negotiated

</figure>

# 3.2 Link Initialization

Link Initialization consists of four stages before protocol Flit transfer can begin on mainband.
Figure 3-3 shows the high-level steps involved in the Link initialization flow for UCIe. Stage 0 is
die-specific and happens independently for each die; the corresponding boxes in Figure 3-3 are of
different sizes to denote that different die can take different amount of time to finish Stage 0. Stage 1
involves sideband initialization. Stage 2 involves mainband training and repair. Details of Stage 1 and
Stage 2 are provided in Chapter 4.0. Stage 3 involves parameter exchanges between Adapters to
negotiate the protocol and Flit Formats and is covered in Section 3.2.1.

<figure>
<figcaption>Figure 3-3. Stages of UCIe Link Initialization</figcaption>

Protocol Layer
Die 0

D2D Adapter
Die 0

Physical Layer
Die 0

D2D
CHANNEL

Physical Layer
Die 1

D2D Adapter Protocol Layer
Die 1
Die 1

Reset flow for Die 0
(independent of Die 1)
Stage 0

Reset flow for Die 1
(independent of Die 0)
Stage 0

Sideband initialization
Stage 1

Training parameter exchanges on sideband
Mainband (Lane Repair and) Training
Stage 2

Protocol parameter exchanges on sideband
Stage 3

Stage 3 Complete; Flit transfer can start

Time Progression

</figure>

## 3.2.1 Stage 3 of Link Initialization: Adapter Initialization

Stage 2 is complete when the RDI state machine moves to Active State. The initialization flow on RDI
to transition the state from Reset to Active is described in Section 10.1.6. Once Stage 2 is complete,
the Adapter must follow a sequence of steps in order to determine Local Capabilities, complete
Parameter Exchanges, and bring FDI state machine to Active.

## 3.2.1.1 Part 1: Determine Local Capabilities

The Adapter must determine the results of Physical Layer training and if Retry is needed for the given
Link speed and configuration. See Section 3.8 for the rules on when Retry must be enabled for Link
operation. If the Adapter is capable of supporting Retry, it must advertise this capability to the remote

Link partner during Parameter Exchanges. For UCIe Retimers, the Adapter must also determine the
credits to be advertised for the Retimer Receiver Buffer. Each credit corresponds to 256B of Mainband
data storage.

## 3.2.1.2 Part 2: Parameter Exchange with Remote Link Partner

The following list of capabilities must be negotiated between Link partners. The capabilities (if
enabled) are transmitted to the remote Link partner using a sideband message. In the section below,
"advertised" means that the corresponding bit is 1b in the {AdvCap.Adapter} sideband message.

<table>
<caption>Table 3-1. Capabilities that Must Be Negotiated between Link Partners (Sheet 1 of 3)</caption>
<tr>
<th>Capability</th>
<th>Description and Requirements</th>
</tr>
<tr>
<td>"Raw Format"</td>
<td>This parameter is advertised if the corresponding bit in the UCIe Link Control register is 1b. Software/ Firmware enables this based on system usage scenario. If the PCIe or CXL protocols are not supported, and Streaming protocol is to be negotiated without any vendor-specific extensions and without Streaming Flit Format capability support, "Raw Format" must be 1b and advertised. If Streaming Flit Format capability or Enhanced Multi-Protocol capability is supported, then this must be advertised as 1b only if Raw Format is the intended format of operation. Software/firmware-based control on setting the corresponding UCIe Link Control is permitted to enable this.</td>
</tr>
<tr>
<td>"68B Flit Mode"</td>
<td>This is a protocol parameter. This must be advertised if the Adapter and Protocol Layer support CXL 68B Flit mode (mandatory for CXL if the negotiated maximum data rate is &lt;= 32 GT/s) or PCIe Non- Flit mode (mandatory for PCIe if the negotiated maximum data rate is &lt;= 32 GT/s). If PCIe Non-Flit mode is the final negotiated protocol, it will use the CXL.io 68B Flit mode formats as defined in CXL Specification. This is an advertised Protocol for Stack 0 if "Enhanced Multi_Protocol_Enable" is supported and enabled. This protocol is not supported and this parameter must be 0 if the negotiated maximum data rate is &gt; 32 GT/s. Note that the negotiation of the maximum data rate occurs during MBINIT.PARAM, which is during Stage 2 of Link Initialization, before any of the Adapter capabilities are determined in Stage 3. The Adapter can use the pl_max_speedmode signal on the RDI to determine the negotiated maximum data rate.</td>
</tr>
<tr>
<td>$C X L \quad 2 5 6 B \quad F l i t \quad M o d e$</td>
<td>This is a protocol parameter. This must be advertised if the Adapter and Protocol Layer support CXL 256B Flit mode. This is an advertised Protocol for Stack 0 if Enhanced Multi-Protocol capability is supported and enabled.</td>
</tr>
<tr>
<td>"PCIe Flit Mode"</td>
<td>This is a protocol parameter. This must be advertised if the Adapter and Protocol Layer support PCIe $F l i t \quad m o d e .$ This is an advertised Protocol for Stack 0 if Enhanced Multi-Protocol capability is supported</td>
</tr>
<tr>
<td>"Streaming"</td>
<td>This is a protocol parameter. This must be advertised if the Adapter and Protocol Layer support Streaming protocol in Raw Format or Streaming Flit Format capability is supported and the corresponding capabilities are enabled. This is an advertised Protocol for Stack 0 if Enhanced Multi- Protocol capability is supported and enabled. PCIe or CXL protocol must not be advertised if Streaming is advertised for a given Protocol Layer.</td>
</tr>
<tr>
<td>"Retry"</td>
<td>This must be advertised if the Adapter supports Retry. With the exception of the Link operating in Raw Format, the Link cannot be operational if the Adapter has determined Retry is needed, but "Retry" is not advertised or negotiated. See also Section 3.8.</td>
</tr>
<tr>
<td>"Multi_Protocol_Enable"</td>
<td>This must only be advertised if the Adapter is connected to multiple FDI instances corresponding to (or SoC firmware in Stage 0 of $\left. L i n k \quad I n i t i a l i z a t i o n \right) h a s \quad d e t e r m i n e d \quad t h a t \quad t h e \quad U C I e \quad L i n k \quad m u s t \quad b e \quad o p e r a t e d \quad i n \quad t h i s \quad m o d e . B o t h$</td>
</tr>
<tr>
<td>"Stack0_Enable"</td>
<td>This must be advertised if the Protocol Layer corresponding to Stack 0 exists and is enabled for operation with support for the advertised protocols.</td>
</tr>
<tr>
<td>"Stack1_Enable"</td>
<td>This must be advertised if the Protocol Layer corresponding to Stack 1 exists and is enabled for operation with support for the advertised protocols.</td>
</tr>
<tr>
<td>"CXL_LatOpt_Fmt5"</td>
<td>This must be advertised if the Adapter and Protocol Layer support Format 5 defined in Section 3.3.4. The Protocol Layer does not take advantage of the spare bytes in this Flit Format. This must not be advertised if CXL protocol and CXL 256B Flit mode are not supported or enabled.</td>
</tr>
<tr>
<td>"CXL_LatOpt_Fmt6"</td>
<td>This must be advertised if the Adapter and Protocol Layer support Format 6 defined in Section 3.3.4. The Protocol Layer takes advantage of the spare bytes in this Flit Format. This must not be advertised if CXL protocol and CXL 256B Flit mode are not supported or enabled.</td>
</tr>
</table>

<table>
<caption>Table 3-1. Capabilities that Must Be Negotiated between Link Partners (Sheet 2 of 3)</caption>
<tr>
<th>Capability</th>
<th>Description and Requirements</th>
</tr>
<tr>
<td>"Retimer"</td>
<td>This must be advertised if the Adapter of a UCIe Retimer is performing Parameter Exchanges with a</td>
</tr>
<tr>
<td>"Retimer_Credits"</td>
<td>$T h i s \quad i s \quad a \quad 9 - b i t \quad v a l u e \quad a d v e r t i s i n g \quad t h e \quad t o t a l \quad c r e d i t s \quad a v a i l a b l e \quad f o r \quad R e t i m e r s \quad R e c e i v e r \quad B u f f e r . E a c h \quad c r e d i t$</td>
</tr>
<tr>
<td>"DP"</td>
<td>This is set by Downstream Ports to inform the remote Link partner that it is a Downstream Port. It is useful for Retimers to identify whether they are connected to a Downstream Port UCIe die. It is currently only applicable for PCIe and CXL protocols; however, Streaming protocols are not precluded from utilizing this bit. If Enhanced Multi-Protocol capability is supported, this bit is applicable if either of the Protocol Layers is PCIe or CXL. This bit must be set to Ob if "Retimer" is set to 1b.</td>
</tr>
<tr>
<td>"UP"</td>
<td>This is set by Upstream Ports to inform the remote Link partner that it is an Upstream Port. It is useful for Retimers to identify whether they are connected to an Upstream Port UCIe die. It is currently only applicable for PCIe and CXL protocols; however, Streaming protocols are not precluded from utilizing this bit. If Enhanced Multi-Protocol capability is supported, this bit is applicable if either of the Protocol Layers is PCIe or CXL. This bit must be set to Ob if "Retimer" is set to 1b.</td>
</tr>
<tr>
<td>"68B Flit Format"</td>
<td>This must be advertised if the negotiated maximum data rate is &lt;= 32 GT/s and any of the following are true: · Enhanced Multi-Protocol capability is supported and enabled, AND the 68B Flit Format is supported and enabled . The 68B Flit Format for Streaming Protocol capability is supported and enabled Otherwise, it must be set to 0b. Note that the negotiation of the maximum data rate occurs during MBINIT.PARAM, which is during Stage 2 of Link Initialization, before any of the Adapter capabilities are determined in Stage 3. The Adapter can use the pl_max_speedmode signal on the RDI to determine the negotiated maximum data rate.</td>
</tr>
<tr>
<td>"Standard 256B End Header Flit Format"</td>
<td>This must be advertised if any of the following are true: · Enhanced Multi-Protocol capability is supported and enabled, AND the Standard 256B End Header Flit Format is supported and enabled · The Standard 256B End Header Flit Format for Streaming Protocol capability is supported and enabled Otherwise, it must be set to 0b.</td>
</tr>
<tr>
<td>"Standard 256B Start Header Flit Format"</td>
<td>This must be advertised if any of the following are true: · PCIe Flit mode is advertised and Standard Start Header for PCIe protocol capability is supported and enabled · Enhanced Multi-Protocol capability is supported and enabled, AND the Standard 256B Start Header Flit Format is supported and enabled · The Standard 256B Start Header Flit Format for Streaming Protocol capability is supported and enabled Otherwise, it must be set to 0b.</td>
</tr>
<tr>
<td>"Latency-Optimized $\begin{array}{} { 2 5 6 B \text { without Optiona } } \\ { \text { Bytes Fit Format^{\prime\prime } } } \end{array}$</td>
<td>This must be advertised if any of the following are true: . Enhanced Multi-Protocol capability is supported and enabled, AND the Latency-Optimized 256B without Optional Bytes Flit Format is supported and enabled · The Latency-Optimized 256B without Optional Bytes Flit Format for Streaming Protocol capability is supported and enabled Otherwise, it must be set to 0b.</td>
</tr>
<tr>
<td>"Latency-Optimized 256B with Optional Bytes Flit Format"</td>
<td>This must be advertised if any of the following are true: · PCIe Flit mode is advertised and Latency-Optimized Flit with Optional Bytes for PCIe protocol capability is supported and enabled · Enhanced Multi-Protocol capability is supported and enabled, AND the Latency-Optimized 256B with Optional Bytes Flit Format is supported and enabled · The Latency-Optimized 256B with Optional Bytes Flit Format for Streaming Protocol capability is supported and enabled Otherwise, it must be set to 0b.</td>
</tr>
<tr>
<td>"Enhanced Multi_Protocol_Enable"</td>
<td>This must only be advertised if the Adapter is connected to multiple FDI instances corresponding to two sets of Protocol Layers. The two sets of Protocol Layers are permitted to be different protocols, but must support at least one common Flit Format. This must only be advertised if the Enhanced Multi-Protocol capability is supported and enabled; otherwise, it must be set to 0b. Both "Stack0_Enable" and "Stack1_Enable" must be 1b if this bit is advertised.</td>
</tr>
</table>

<table>
<caption>Table 3-1. Capabilities that Must Be Negotiated between Link Partners (Sheet 3 of 3)</caption>
<tr>
<th>Capability</th>
<th>Description and Requirements</th>
</tr>
<tr>
<td>"Stack 0 Maximum Bandwidth_Limit"</td>
<td>This must be advertised if Enhanced Multi_Protocol_Enable is advertised and the Stack 0 protocol Receiver is limited to 50% of the maximum bandwidth; otherwise, it must be set to 0b.</td>
</tr>
<tr>
<td>$S t a c k \quad 1 \quad M a x i m u m$</td>
<td>This must be advertised if Enhanced Multi_Protocol_Enable is advertised and the Stack 1 protocol Receiver is limited to 50% of the maximum bandwidth; otherwise, it must be set to 0b.</td>
</tr>
<tr>
<td>"Management Transport Protocol"</td>
<td>This bit must be set to 1 if the Protocol Layer and Adapter both support Management Transport protocol (either as the only protocol or multiplexed with one of CXL.io, PCIe, or Streaming). The mechanism by which this bit is set to 1 is implementation-specific.</td>
</tr>
</table>

Once local capabilities are established, the Adapter sends the {AdvCap.Adapter} sideband message
advertising its capabilities to the remote Link partner.

If PCIe or CXL protocol support is going to be advertised, the Upstream Port (UP) Adapter must wait
for the first {AdvCap.Adapter} message from the Downstream Port (DP) Adapter, review the
capabilities advertised by DP and then send its own sideband message of advertised capabilities. UP is
permitted to change its advertised capabilities based on DP capabilities. Once the DP receives the
capability advertisement message from the UP, the DP responds with the Finalized Configuration using
{FinCap.Adapter} sideband message to the UP as shown in Figure 3-4. See Section 7.1.2.3 to see the
message format for the relevant sideband messages.

Final determination for Protocol parameters:

· If "68B Flit Mode" is advertised by both Link partners, it is set to 1 in the {FinCap.Adapter}
message

· If "CXL 256B Flit Mode" is advertised by both Link partners, it is set to 1 in the {FinCap.Adapter}
message

· If "PCIe Flit Mode" is advertised by both Link partners, "PCIe Flit Mode" bit is set to 1 in the
{FinCap.Adapter} message

· If Streaming protocol is negotiated, no {FinCap.Adapter} messages are exchanged for that stack.

If "68B Flit Mode" or "CXL 256B Flit Mode" is set in the {FinCap.Adapter} message, there must be
another handshake of Parameter Exchanges using the {AdvCap.CXL} and the {FinCap.CXL}
messages to determine the details associated with this mode. If the negotiated maximum data rate is

negotiated data rates, CXL 68B Flit Mode protocol is mandatory for CXL and PCIe Non-Flit Mode
protocol is mandatory for PCIe. If the negotiated maximum data rate is > 32 GT/s, the 68B Flit
Formats are not supported and the "68B Flit Mode" parameter must be cleared to 0. This additional
handshake is shown in Figure 3-4. The combination of {FinCap.CXL} and {FinCap.Adapter}
determine the Protocol and Flit Format. See Section 7.1.2.3 for the message format of the relevant
sideband messages. See Section 3.4 for how Protocol and Flit Formats are determined.

Final determination for other parameters if CXL or PCIe protocol is negotiated:

· If "Raw Format" is advertised by both Link partners, "Raw Format" is set to 1 in the
{FinCap.Adapter} message.

· If both Link partners advertised "Retry" and "Raw Format" is not negotiated, Adapter Retry is
enabled and "Retry" is set to 1 in the {FinCap.Adapter} message.

. If both Link partners advertised "Enhanced Multi_Protocol_Enable", both Stack 0 and Stack 1 are
enabled by the adapter, and all three parameters ("Enhanced Multi_Protocol_Enable",
"Stack0_Enable" and "Stack1_Enable") are each set to 1 in the {FinCap.Adapter} message (if a
{FinCap.Adapter} message is required to be sent).

. If both Link partners advertised "Multi_Protocol_Enable" and "Enhanced Multi_Protocol_Enable" is
not negotiated, both Stack 0 and Stack 1 are enabled by the Adapter, and all three parameters
("Multi_Protocol_Enable", "Stack0_Enable", and "Stack1_Enable") are each set to 1 in the
{FinCap.Adapter} message.

. If neither "Enhanced Multi_Protocol_Enable" nor "Multi_Protocol_Enable" is negotiated, then the
lowest common denominator is used to determine whether Stack 0 or Stack 1 is enabled, and the
corresponding bit is set to 1 in the {FinCap.Adapter} message. If both Stack enables are
advertised, then Stack 0 is selected for operational mode and only Stack0_Enable is set to 1 in
the {FinCap.Adapter} message.

· If CXL_LatOpt_Fmt5 is advertised by both Link partners, then it is set to 1 in the
{FinCap.Adapter} message.

· If CXL_LatOpt_Fmt6 is advertised by both Link partners, then it is set to 1 in the
{FinCap.Adapter} message.

<figure>
<figcaption>Figure 3-4. Parameter Exchange for CXL or PCIe (i.e., "68B Flit Mode" or "CXL 256B Flit Mode" is 1 in {FinCap.Adapter} )</figcaption>

DP Adapter
Die 0

DP Physical layer CHANNEL UP Physical layer
Die 0
Die 1

UP Adapter
Die 1

SB MSG {AdvCap.Adapter}

SB MSG {AdvCap.Adapter}

$S B \quad M S G F i n C a p . A d a p t e r$

SB MSG {AdvCap.CXL}

$S B \quad M S G A d v C a p . C X L$

SB MSG {FinCap.CXL}

</figure>

If Streaming protocol is negotiated, there is no notion of DP and UP for parameter exchanges and
each side independently advertises its capabilities. Additional Vendor Defined sideband messages are
permitted to be exchanged to negotiate vendor-specific extensions. See Table 7-8 and Table 7-10 for
additional descriptions of Vendor Defined sideband messages. Similarly, if Management Transport
protocol is negotiated on a stack without "Streaming protocol," "CXL 256B Flit mode," or "PCIe Flit
mode," there is no notion of DP and UP for parameter exchanges and each side independently
advertises its capabilities.

The Finalized Configuration is implicitly determined based on the intersection of capabilities
advertised by each side:

· Flit Formats are chosen based on the Truth Table resolution provided in Table 3-10

· If both Link partners advertised Retry, and "Raw Format" is not negotiated, then Adapter Retry is
enabled

. If "Multi_Protocol_Enable" is negotiated, both Stack 0 and Stack 1 are enabled by the adapter

. If neither "Multi_Protocol_Enable" nor "Enhanced Multi_Protocol_Enable" is advertised by at least
one of the Link partners, then the lowest common denominator is used to determine whether
Stack 0 or Stack 1 is enabled (i.e., if both Stack enables are advertised, then Stack 0 is selected
for operational mode)

{FinCap .* } messages are not sent for Streaming protocol. Adapter must determine vendor specific
requirements in an implementation specific manner.

If "Enhanced Multi_Protocol_Enable" is negotiated, the {AdvCap.Adapter} and if applicable, the
{FinCap.Adapter} messages determine the negotiated Flit Format of operation as well as the protocol
for Stack 0. The Adapter uses {MultiProtAdvCap.Adapter} and if applicable, the
{MultiProtFinCap.Adapter} sideband messages to negotiate the Stack 1 protocol. For Stack 1, if PCIe
or CXL protocol support is going to be advertised, the UP Adapter must wait for the first message
from the DP Adapter, review the capabilities advertised by DP and then send its own sideband
message of advertised capabilities. UP is permitted to change its advertised capabilities based on DP
capabilities. In the section below, "advertised" means that the corresponding bit is 1b in the
{MultiProtAdvCap.Adapter} sideband message.

· "68B Flit Mode": If the negotiated maximum data rate is $< = 3 2$ GT/s, this must be advertised
when the Adapter and Protocol Layer support CXL 68B Flit Mode or PCIe Non-Flit Mode on Stack
1.

. "CXL 256B Flit Mode": This must be advertised if the Adapter and Protocol Layer support CXL
256B Flit Mode on Stack 1.

. "PCIe Flit Mode": This must be advertised if the Adapter and Protocol Layer support PCIe Flit Mode
on Stack 1.

. "Streaming": This must be advertised if the Adapter and Protocol Layer support Streaming Flit
Mode on Stack 1.

. "Management Transport Protocol": This must be advertised if the Protocol Layer supports
Management Transport protocol on Stack 1.

If "68B Flit Mode" or "CXL 256B Flit Mode" is set in the {MultiProtFinCap.Adapter} message, there
must be another handshake of Parameter Exchanges using the {AdvCap.CXL} and the {FinCap.CXL}
messages to determine the details associated with this mode. The non-Stall { *. CXL} messages are
sent with a MsgInfo encoding of 0001h indicating that these messages are for Stack 1 negotiation.

Figure 3-5 to Figure 3-9 represent examples of different scenarios where Stack 0 and Stack 1 are of
different protocols.

Figure 3-5.
Both Stacks are CXL or PCIe

<table>
<tr>
<th colspan="4">DP Adapter DP Physical layer CHANNEL UP Physical layer Die 0 Die 0 Die 1 $S B \quad M S G$ {AdvCap.Adapter}</th>
<th>UP Adapter $D i e \quad 1$</th>
</tr>
<tr>
<th colspan="2"></th>
<th>$S B \quad M S G$ {AdvCap.Adapter} SB MSG {FinCap.Adapter} SB MSG {AdvCap.CXL}: MsgInfo=0000h $C A N S G \left\{ A d v C _ { d P } ^ { 1 } , C X L \right\} : M s g l n f o = 0 0 0 0$ SB MSG {Fin Cap.CXL}: MsgInfo=0000h- SB MSG {MultiProtAdvCap.Adapter} SB MSG {MultiProtAdvCap.Adapter}</th>
<th></th>
<th></th>
</tr>
<tr>
<td></td>
<td></td>
<td>SB MSG {MultiProtFinCap.Adapter} SB MSG {AdvCap.CXL}: MsgInfo=0001h- SB MSG {AdvCap.CXL}: $\mathrm { M s g l n f o } = 0 0 0 1$ SB MSG {FinCap.CXL}: MsgInfo=0001h-</td>
<td></td>
<td></td>
</tr>
</table>

<figure>
<figcaption>Figure 3-6. Stack 0 is PCIe, Stack 1 is Streaming</figcaption>
</figure>

<figure>

$\begin{array}{} { \text { Adapte } } \\ { \text { Die } 0 } \end{array}$

Physical layer
$D i e \quad 0$
DP

Physical layer
$D i e \quad 1$
UP

Adapter
Die 1
UP

CHANNEL

DP

SB MSG {AdvCap.Adapter}

SB MSG {AdvCap.Adapter}

SB MSG {Fin Cap.Adapter}

SB MSG {AdvCap.CXL}: MsgInfo=0000h-

SB MSG {AdvCap.CXL}: MsgInfo=0000h

SB MSG {Fin Cap.CXL}: $M s g I n f o = 0 0 0 0 h -$

SB MSG {MultiProtAdvCap.Adapter}

SB MSG {MultiProtAdvCap.Adapter}

</figure>

<figure>
<figcaption>Figure 3-7. Stack 0 is Streaming, Stack 1 is PCIe</figcaption>

$\begin{array}{} { \text { Adapte } } \\ { \text { Die } 0 } \end{array}$

Physical layer
$D i e \quad 0$
DP

Physical layer
Die 1
$U P$

Adapter
Die 1
UP

CHANNEL

$\mathrm { D P }$

SB MSG {AdvCap.Adapter}

SB MSG {AdvCap.Adapter}

SB MSG {MultiProtAdvCap.Adapter}

SB MSG {Multi ProtAdvCap.Adapter}

SB MSG {MultiProtFinCap.Adapter}

SB MSG {AdvCap.CXL}: MsgInfo=0001h

SB MSG {AdvCap.CXL}: MsgInfo=0001h-

SB MSG {Fin Cap. CXL}: MsgInfo=0001h-

</figure>

<figure>
<figcaption>Figure 3-8. Both Stacks are Streaming</figcaption>

Adapter
Die 0

Physical layer
$D i e \quad 0$

CHANNEL

Physical layer
Die 1

Adapter
$D i e \quad 1$

SB MSG {AdvCap.Adant~}
SB MSG {AdvCap.Adapter}

SB MSG {Multi ProtAdvCap.Adapter}
SB MSG {Multi ProtAdvCap.Adapter}

</figure>

<figure>
<figcaption>Figure 3-9. Stack 0 is Streaming, Stack 1 is CXL</figcaption>

Adapter
$D i e \quad 0$
DP

Physical layer
$D i e \quad 0$
DP

Physical layer
Die 1
UP

Adapter
Die 1
UP

CHANNEL

SB MSG {AdvCap.Adapter}
SB MSG {AdvCap.Adapter}

SB MSG {Multi ProtAdvCap.Adapter}

SB MSG {Multi ProtAdvCap.Adapter}

SB MSG {MultiProtFinCap.Adapter}

SB MSG {AdvCap.CXL}: MsgInfo=0001h-

SB MSG {AdvCap.CXL}: MsgInfo=0001h

SB MSG {FinCap.CXL}: MsgInfo=0001h-

</figure>

The Adapter must implement a timeout of 8 ms $\left( - 0 / + 5 0 \right)$ for successful Parameter Exchange
completion. For the purposes of measuring a timeout for Parameter Exchange completion, all steps in
Part 1 and Part 2 of Stage 3 of Link Initialization are included. The timer only increments while RDI is
in Active state. The timer must reset if the Adapter receives an {AdvCap .\*. Stall}, {FinCap .\*. Stall},
{MultiProtAdvCap .\*. Stall}, or {MultiProtFinCap .\*. Stall} message from the remote Link partner. The
8-ms timeouts for Parameter Exchanges or Link State Machine transitions are treated as UIE and the
Adapter must take the RDI to LinkError state. UCIe Retimers must ensure that they resolve the
capability advertisement with remote Retimer partner (and merge with their own capabilities) before
responding/initiating parameter exchanges with the UCIe die within its package. While resolution is in
progress, they must send the corresponding stall message once every 4 ms to ensure that a timeout
does not occur on the UCIe die within its package.

## 3.2.1.3 Part 3: FDI bring up

Once Parameter Exchanges have successfully completed, the Adapter reflects the result to the
Protocol Layers on FDI, and moves on to carry out the FDI bring up flow as defined in Section 10.2.8.
Once FDI is in Active state, it concludes Stage 3 of Link Initialization and protocol Flit transfer can
begin. When multiple stacks are enabled on the same Adapter, each stack may finish the FDI bring up
flow (see Section 10.2.8) at different times.

The data width on FDI is a function of the frequency of operation of the UCIe stack as well as the total
bandwidth being transferred across the UCIe physical Link (which in turn depends on the number of
Lanes and the speed at which the Lanes are operating). The data width on RDI is fixed to at least one
byte per physical Lane per module that is controlled by the Adapter. The illustrations of the formats in
this chapter are showing an example configuration of RDI mapped to a 64 Lane module of Advanced
Package configuration on the Physical Layer of UCIe.

# 3.3 Operation Formats

In subsequent sections, when referring to CRC computation, a byte mapping of the Flit to CRC
message (CRC message is the 128B input to CRC computation logic) is provided. See Section 3.7 for
more details.

## 3.3.1 Raw Format for All Protocols

Raw Format can only be used for scenarios in which Retry support from the Adapter is not required. If
Raw Format is negotiated for CXL or PCIe protocols, the Adapter transfers data from Protocol Layer to
Physical Layer without any modification. Figure 3-10 shows an example of this for a 64B data path on
FDI and RDI. This is identified as Format 1 during parameter negotiation.

Figure 3-10. Format 1: Raw Formata

+0

$\infty$

Byte 0

64B (from Protocol Layer)

a. See Figure 2-1 for color mapping.

## 3.3.2 68B Flit Format

This Flit Format is identified as Format 2 on UCIe. If the negotiated maximum data rate is
$< = 3 2 \quad G T / s :$

· Support for this is mandatory when CXL 68B Flit Mode protocol or PCIe Non-Flit Mode protocol is
supported

. 68B Flit Format support is optional for Streaming protocols

If the negotiated maximum data rate is > 32 GT/s, 68B Flit Format is not supported.

The Protocol Layer sends 64B of protocol information. The Adapter adds a two byte prefix of Flit
Header and a two byte suffix of CRC. Table 3-3 gives the Flit Header format for Format 2 when Retry
from the Adapter is required. If Retry from the Adapter is not required, then the Flit Header format is
as provided in Table 3-2.

Even if Retry is not required, the Adapter still computes and drives CRC bytes - the Receiver is
strongly recommended to treat a CRC error as an Uncorrectable Internal Error in this situation. For
CRC computation, Flit Byte 0 (i.e., Flit Header Byte 0) is assigned to CRC message Byte 0, Flit Byte 1
(i.e., Flit Header Byte 1) is assigned to CRC message Byte 1 and so on until Flit Byte 65 is assigned to
CRC message Byte 65.

Retry is performed over this 68B Flit.

<table>
<caption>Table 3-2. Flit Header for Format 2 without Retry</caption>
<tr>
<th rowspan="2">Byte</th>
<th rowspan="2">Bit</th>
<th colspan="2">Description</th>
</tr>
<tr>
<th>PCIe or CXL</th>
<th>Streaming Protocol</th>
</tr>
<tr>
<td rowspan="4">Byte 0</td>
<td>[7:6]</td>
<td>Protocol Identifier: 2'b00: D2D Adapter NOP Flit or PDS Flit Header 2'b01: CXL.io Flit 2'b10: CXL.cachemem Flit 2'b11: ARB/MUX Flit (Reserved encoding for PCIe)</td>
<td>Protocol Identifier: 2'b00: D2D Adapter NOP Flit 2'b01: Protocol Layer Flit Remaining encodings are Reserved.</td>
</tr>
<tr>
<td>[5]</td>
<td>Stack Identifier: 1'b0: Stack 0 1'b1: Stack 1</td>
<td></td>
</tr>
<tr>
<td>[4]</td>
<td>1'b0: Regular Flit Header 1'b1: Pause of Data Stream (PDS) Flit Header</td>
<td></td>
</tr>
<tr>
<td>[3:0]</td>
<td>Reserved</td>
<td></td>
</tr>
<tr>
<td rowspan="2">Byte 1ª</td>
<td>[7]</td>
<td>1'b0: Regular Flit Header 1'b1: Pause of Data Stream (PDS) Flit Header</td>
<td></td>
</tr>
<tr>
<td>[6:0]</td>
<td>Reserved</td>
<td></td>
</tr>
</table>

a. For a Test Flit, bits [7:6] of Byte 1 are 01b. See Section 11.2 for more details.

<table>
<caption>Table 3-3. Flit Header for Format 2 with Retry</caption>
<tr>
<th rowspan="2">Byte</th>
<th rowspan="2">Bit</th>
<th colspan="2">Description</th>
</tr>
<tr>
<th>PCIe or CXL</th>
<th>Streaming Protocol</th>
</tr>
<tr>
<td rowspan="4">Byte 0</td>
<td>[7:6]</td>
<td>Protocol Identifier: 2'b00: D2D Adapter NOP Flit or PDS Flit Header 2'b01: CXL.io Flit 2'b10: CXL.cachemem Flit 2'b11: ARB/MUX Flit (Reserved encoding for PCIe)</td>
<td>Protocol Identifier: 2'b00: D2D Adapter NOP Flit 2'b01: Protocol Layer Flit Remaining encodings are Reserved.</td>
</tr>
<tr>
<td>[5]</td>
<td>Stack Identifier: 1'b0: Stack 0 1'b1: Stack 1</td>
<td></td>
</tr>
<tr>
<td>[4]</td>
<td>1'b0: Regular Flit Header 1'b1: Pause of Data Stream (PDS) Flit Header</td>
<td></td>
</tr>
<tr>
<td>[3:0]</td>
<td>The upper four bits of Sequence number "S" (i.e., S[7:4])</td>
<td></td>
</tr>
<tr>
<td rowspan="3">$1 ^ { a }$</td>
<td>[7:6]</td>
<td>2'b00: Regular Flit Header 2'b11: Pause of Data Stream (PDS) Flit Header Other encodings are reserved</td>
<td></td>
</tr>
<tr>
<td>$\left[ 5 : 4 \right]$</td>
<td>Ack or Nak information 2'b00: Explicit Sequence number "S" of Flit if not PDS, "NEXT_TX_FLIT_SEQ_NUM - 1". (See PCIe Base Specification NEXT_TX_FLIT_SEQ_NUM and the subtraction operation 2'b01: Ack. The Sequence number "S" carries the Ack'ed 2'b10: Nak. The Sequence number "S" carries 255 if N=1, Nak'ed sequence number. 2'b11: Reserved</td>
<td>otherwise the bitwise inverted value of for the definition of for sequence numbers) sequence number. otherwise it carries N-1, where N is the</td>
</tr>
<tr>
<td>[3:0]</td>
<td colspan="2">The lower four bits of Sequence number "S" (i.e., S[3:0]) Sequence number 0 is reserved and if present, it implies no Ack or Nak is sent.</td>
</tr>
</table>

a. For a Test Flit, bits [7:6] of Byte 1 are 01b. See Section 11.2 for more details.

## 3.3.2.1 68B Flit Format Alignment and Padding Rules

Because of the four bytes added by D2D Adapter, the alignment of the Flit does not always match the
number of Lanes of the physical Link. The bytes added by D2D Adapter require the Adapter to shift
the data arriving over FDI by four bytes for consecutive Flits transmitted over RDI. Data is always
transferred in multiples of 256B (note that Retimer credits have a 256B data granularity). A
mechanism to Pause the Data Stream is provided as a way to save power when the Link is idle. Before
pausing the data stream, the data stream is terminated with a Pause of Data Stream (PDS) Flit
Header followed by 0b padding to the next 64B count multiple boundary and at least two subsequent
64B chunks of all 0 value data. If the transfer is not at a 256B count multiple boundary, additional 64B
chunks of all 0 value data are required to bring the transferred bytes to a 256B count multiple. The
subsequent transfers of all 0 data mentioned above give the Receiver at least two 64B chunks to reset
the receiving byte shifter. The PDS Flit Header and the 0 padding bytes following it must not be
forwarded to the Protocol Layer. The PDS token is a variable-size Flit that carries a 2B special Flit
Header (referred to as the PDS Flit Header), and 0 bytes padded as described above. The Transmitter
of PDS drives the following on the Flit header:

1\. Bit [4] of Byte 0 as 1

2\. Bit [7] of Byte 1 as 1

3\. Bit [6] of Byte 1 as 1

4\. Bits [5:4] of Byte 1 as 00b and the sequence number[7:0] is matching the expected value for a
PDS Flit Header in this position as defined in Table 3-3.

The Adapter may optionally insert continuous NOPs instead of terminating the data stream with a PDS
when no other flits are available to transmit ("no flits available to transmit" includes any payload flits,
test flits, or flits transmitted to follow the replay rules, as well as any pending ACKs/NAKs, etc.).
There is a trade-off between the longer idle latency for a new flit to be transmitted after a PDS vs. the
power consumption of continuously transmitting NOP flits. It is the responsibility of the transmitting
Adapter to make the determination between transmitting NOP flits vs. inserting a PDS in an
implementation-specific manner. Note that the transmitting Adapter does not de-assert lp_irdy and
lp_valid on the RDI in the middle of a data stream (i.e., until the PDS Flit Header and
corresponding padding of Os has completed transferring across the RDI). If Runtime Link Testing
Parity is enabled (see Section 3.9), any parity bytes that are scheduled for transmission must be sent
immediately and without any gap after the preceding data, including any completed PDS, to ensure
that the parity bytes can be correctly identified by the receiver.

If Retry is enabled, the Receiver must interpret this Flit header as PDS if any two of the above four
conditions are true. If Retry is disabled, the Receiver must interpret this Flit header as a PDS if
conditions (1) and (2) are true.

A PDS must be inserted when Retry is triggered or RDI state goes through Retrain. The transmitter
must insert PDS Flit Header and corresponding padding of 0s as it would for an actual PDS and start
the replayed Flit from fresh alignment (i.e., flit begins from a 256B-aligned boundary). Note that for
Retry, this should occur before the Transmitter begins replaying the Flits from the Retry buffer; and
for Retrain entry, this should occur before asserting lp_stallack to the Physical Layer.

For Retry and Retrain scenarios, the Receiver must also look for the expected sequence number in
Byte 0 and Byte 1 of the received data bus with a corresponding valid Flit (i.e., CRC passes). Note that
for a Retrain scenario, a PDS might not be received at the receiver before the RDI state changes to
Retrain, and the Adapter must discard any partially received 68B Flits after state change.

When resuming the data stream after a PDS token (i.e., a PDS Flit Header and the corresponding
padding of 0s), the first Flit is always 256B aligned; any valid Flit transfer after a PDS token will
resume the data stream. If Retry is disabled, the first Flit that is transmitted to resume the data
stream must be a payload Flit or a test Flit (because NOPs can be all 0 Flit, the receiver could not

distinguish this NOP from a paused data stream). After a PDS Flit Header has been transmitted, the
corresponding padding of 0b to satisfy the PDS token padding requirements must be finished before
resuming the data stream with new Flits. If Runtime Link Testing Parity is enabled (see Section 3.9),
any parity bytes transmitted do not indicate that a data stream is resumed; only a valid Flit resumes
a data stream.

If Retry is enabled, it is permitted to map a PDS error (such as an invalid length or nonzero data
bytes) to trigger Link Retrain. If Retry is disabled, it is permitted to map a PDS error to LinkError.

### IMPLEMENTATION NOTE

#### Bit Errors and Aliasing

When Retry is disabled, the BER of the Link is 1E-27 or lower. In these cases, any bit
error is an uncorrectable error for the Link. As a best practice, it is strongly
recommended for receiver implementations to have an uncorrectable internal error
condition for scenarios in which neither a valid Flit Header nor a valid PDS Flit Header
is detected.

When Retry is enabled, the BER is 1E-15 or lower, which results in the probability of
two or more bit errors within the Flit Header is very low. However, implementations
must consider the following two scenarios:

. PDS Flit Header aliasing to a regular Flit Header: Checking for two out of the
four conditions guarantees that at least three bit errors must occur within the two
bytes of the PDS Flit Header for it to alias to a regular Flit Header. Even for three
bit errors, there will be a CRC which will result in a retry and will be handled
seamlessly through the retry rules.

· Regular Flit Header aliasing to a PDS Flit Header: It is possible for two bit
errors to cause a Regular Flit Header to alias to a PDS Flit Header. This will likely
result in a CRC error for future Flits. However, to reduce the probability of a data
corruption that escapes CRC even further, it is strongly recommended that if a
PDS Flit Header was detected without all four conditions being satisfied (i.e., two
out of four or three out of four were satisfied), the receiver checks for an explicit
sequence number Flit with the expected sequence number in Byte 0 and Byte 1 of
the first received data transfer and that it is a valid Flit (i.e., CRC passes) after
the PDS (including the PDS token and the corresponding padding) have
completed; and triggers a Retry if it does not pass the check. Note that this is the
same check a Receiver performs after a Retry or Retrain.

Figure 3-11 shows the 68B Flit Format. Figure 3-12 and Figure 3-13 provide examples of PDS
insertion.

Figure 3-11. Format 2: 68B Flit Formata

+0

+1

+2

+3

+4

+5

+6

+7

+8
+9

+10

$\infty$

Byte 0

F1H B0b

F1H B1b

62B of Flit 1 (from Protocol Layer)

Byte 64

F1 B62C

F1 B63c

C1 B0d

C1 B1d

F2H B0b

F2H B1b

58B of Flit 2 (from Protocol Layer)

Byte 128

6B of Flit 2
(from Protocol Layer)

C2 B0d

C2 B1ª

F3H B0b

F3H B1b

54B of Flit 3 (Next Flit)

a. See Figure 2-1 for color mapping.

b. Flit 1 Header Byte 0, Flit 1 Header Byte 1, Flit 2 Header Byte 0, Flit 2 Header Byte 1, Flit 3 Header Byte 0, and Flit 3 Header Byte
1 respectively.

c. Flit 1 Byte 62 and Byte 63, respectively (from Protocol Layer).

d. Flit 1 CRC Byte 0, Flit 1 CRC Byte 1, Flit 2 CRC Byte 0, and Flit 2 CRC Byte 1, respectively.

<figure>
<figcaption>Figure 3-12. Format 2: 68B Flit Format PDS Example 1ª</figcaption>

+0

+1

+2

+3

+4

+5

+6

$\infty$

Byte 0

FH B0b

FH B1b

62B (from Protocol Layer)

2B

CRC BOC

CRC B1C

PDS B0d

Byte 64

(from

Protocol
Layer)

PDS B1ª

58B all 0 data

Byte 128

64B all 0 data

Byte 192

64B all 0 data

</figure>

a. See Figure 2-1 for color mapping.

b. Flit Header Byte 0 and Byte 1, respectively.

c. CRC Byte 0 and Byte 1, respectively.

d. PDS Flit Header Byte 0 and Byte 1, respectively.

<figure>
<figcaption>Figure 3-13. Format 2: 68B Flit Format PDS Example 2 - Extra Os Padded to Make the Data Transfer a Multiple of 256Bª</figcaption>

Byte 0

Byte 64

Byte 128

Byte 192

Byte 256

Byte 320

Byte 384

Byte 448

</figure>

<table>
<tr>
<th>+0</th>
<th>+1</th>
<th>+2</th>
<th>+3</th>
<th>+4</th>
<th>+5</th>
<th>+6</th>
<th>+7</th>
<th>+8</th>
<th>+9 +10</th>
<th></th>
<th>$+ 6 3$</th>
</tr>
<tr>
<td>F1H B0b</td>
<td>F1H B1b</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>62B of Flit 1 (from Protocol Layer)</td>
<td></td>
</tr>
<tr>
<td>F1 B62℃</td>
<td>F1 B63C</td>
<td>C1 B0d</td>
<td>C1 B1ª</td>
<td>F2H B0b</td>
<td>F2H B1b</td>
<td></td>
<td></td>
<td colspan="2"></td>
<td colspan="2">58B of Flit 2 (from Protocol Layer)</td>
</tr>
<tr>
<td>F2 B58e</td>
<td>F2 B59e</td>
<td>F2 B60e</td>
<td>F2 B61e</td>
<td>F2 B62e</td>
<td>F2 B63e</td>
<td>C2 B0d</td>
<td>C2 B1d</td>
<td>PDS B0f</td>
<td>PDS B1f</td>
<td colspan="2">54B all 0 data</td>
</tr>
<tr>
<td colspan="2"></td>
<td colspan="4"></td>
<td></td>
<td colspan="3"></td>
<td colspan="2">64B all 0 data</td>
</tr>
<tr>
<td colspan="7"></td>
<td colspan="3"></td>
<td colspan="2">64B all 0 data</td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td colspan="3"></td>
<td></td>
<td></td>
<td></td>
<td colspan="2">64B all 0 data</td>
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
<td>64B all 0 data</td>
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
<td>64B all 0 data</td>
<td></td>
</tr>
</table>

a. See Figure 2-1 for color mapping.

b. Flit 1 Header Byte 0, Flit 1 Header Byte 1, Flit 2 Header Byte 0, and Flit 2 Header Byte 1, respectively.

c. Flit 1 Byte 62 and Byte 63, respectively (from Protocol Layer).

d. Flit 1 CRC Byte 0, Flit 1 CRC Byte 1, Flit 2 CRC Byte 0, and Flit 2 CRC Byte 1, respectively.

e. Flit 2 Bytes 58 through Byte 63, respectively (from Protocol Layer).

f. PDS Flit Header Byte 0 and Byte, respectively.

## 3.3.3 Standard 256B Flit Formats

These are the Standard Flit Formats defined in PCIe Base Specification for PCIe Flit Mode and CXL
Specification for CXL 256B Flit Mode. These are identified as "Standard 256B End Header Flit Format"
(or Format 3) and "Standard 256B Start Header Flit Format" (or Format 4), respectively. Support for

this is mandatory when PCIe Flit Mode or CXL 256B Flit Mode protocols are negotiated. Standard 256B
Flit Formats (Start Header or End Header) support is optional with Streaming protocols.

The Protocol Layer sends data in 256B Flits, but it drives 0 on the bytes reserved for the Adapter
(shown in light orange in Figure 3-14 through Figure 3-19). The 6B of DLP defined in PCIe Base
Specification exist in Format 3 and Format 4 as well for PCIe and CXL.io protocols. However, since
DLLPs are required to bypass the Tx Retry buffer in PCIe and CXL.io protocols, the DLP bytes end up
being unique since they are partially filled by the Protocol Layer and partially by the Adapter. DLP0
and DLP1 are replaced with the Flit Header for UCIe and are driven by UCIe Adapter. However, if the
Flit carries a Flit Marker, the Protocol Layer must populate bit 4 of Flit Header Byte 0 to 1b, as well as
the relevant information in the Flit_Marker bits (these are driven as defined in PCIe Base
Specification). Protocol Layer must also populate the Protocol Identifier bits in the Flit Header for the
Flits it generates.

For Streaming protocols, Figure 3-17 shows the applicable Flit Format. Protocol Layer only populates
bits [7:6] of Byte 0 of the Flit Header, and it must never set 00b for bits [7:6].

Standard 256B Start Header Flit Format is optional for PCIe Flit Mode protocol. Figure 3-18 shows the
Flit Format example.

FDI provides a separate interface for DLLP transfer from the Protocol Layer to the Adapter and vice-
versa. The Adapter is responsible for inserting DLLP into DLP Bytes 2:5 if a Flit Marker is not present.
The credit update information is transferred as regular Update_FC DLLPs over FDI from the Protocol
Layer to the Adapter. The Adapter is also responsible for formatting these updates as
Optimized_Update_FC format when possible and driving them on the relevant DLP bytes. The Adapter
is also responsible for adhering to all the DLLP rules defined for Flit Mode in PCIe Base Specification.
On the receive path, the Adapter is responsible for extracting the DLLPs or Optimized_Update_FC
from the Flit and driving it on the dedicated DLLP interface provided on FDI.

Two sets of CRC are computed (CRC0 and CRC1). The same 2B over 128B CRC computation as
previous formats is used.

For PCIe, CXL, and Streaming:

· For Format 3, CRCO is computed using Flit Bytes 0 to 127 assigned to the corresponding bytes of
the CRC message input. CRC1 is computed using Flit Bytes 128 to 241 as the message input with
Flit Byte 128 assigned to CRC message Byte 0, Flit Byte 129 assigned to CRC message Byte 1 and
so on until Flit Byte 241 is assigned to CRC message Byte 113 (including the Flit Header bits
inserted by the Adapter, which for PCIe and CXL.io, includes the DLP bytes inserted by the
Adapter).

· For Format 4, CRCO is computed using Flit Bytes 0 to 127 assigned to the corresponding bytes of
the CRC message input (including the Flit Header bits inserted by the Adapter). CRC1 is computed
using Flit Bytes 128 to 241 as the message input with Flit Byte 128 assigned to CRC message
Byte 0, Flit Byte 129 assigned to CRC message Byte 1 and so on until Flit Byte 241 is assigned to
CRC message Byte 113 (for PCIe and CXL.io, this includes the DLP bytes inserted by the Adapter).

If Retry is not required, the Adapter still computes and drives CRC bytes - the Receiver is strongly
recommended to treat a CRC error as an Uncorrectable Internal Error (UIE) in this situation.

The Flit Header byte formats are shown in Table 3-5 when Retry is required; otherwise, it is as shown
in Table 3-4.

The Protocol Layer must drive bits [7:6] in Byte 1 of Flit Header to 00b for CXL/PCIe/Streaming
protocol Flits and to 10b for Management Flits (when successfully negotiated).

For Management Flits, Bytes 238 to 241 are driven from the Protocol Layer with Management
Transport Credit Return DWORD (CRD) Bytes 0 to 3 (see Section 8.2.5.2.2 for CRD format). Bytes

232 to 235 in Format 3 and Bytes 234 to 237 in Format 4 are driven from the Protocol Layer with 0s
for Management Flits. See Figure 3-16 and Figure 3-19 for details of Format 3 and Format 4 for
Management Flits, respectively.

If PCIe/CXL.io is negotiated along with Management Transport protocol on the same stack:

· If bits [7:6] of Byte 1 are 10b, the Adapter passes through Bytes 238 to 241 from the Protocol
Layer to the Link

· If bits [7:6] of Byte 1 are 00b, Bytes 238 to 241 are treated per PCIe/CXL.io DLP rules for this flit
format

<figure>
<figcaption>Figure 3-14. Format 3: Standard 256B End Header Flit Format for PCIeª</figcaption>

+0

+43

+44

+45

+46

+49

+50

+59

+60

$+ 6 3$

Byte 0

Flit Chunk 0 64B (from Protocol Layer)

Byte 64

Flit Chunk 1 64B (from Protocol Layer)

Byte 128

Flit Chunk 2 64B (from Protocol Layer)

Byte 192

44B of Flit Chunk 3 (from Protocol Layer)

FH B0b

FH B1b

DLP B2C

DLP B3c

DLP B4c

DLP B5c

10B
Reserved

C0 B0d

C0 B1d

$\overrightarrow { \mathrm { U } }$ B0d

C1 B1d

</figure>

a. See Figure 2-1 for color mapping.

b. Flit Header Byte 0 and Byte 1, respectively.

c. DLP Byte 2, Byte 3, Byte 4, and Byte 5, respectively.

d. CRC0 Byte 0, CRC0 Byte 1, CRC1 Byte 0, and CRC1 Byte 1, respectively.

Figure 3-15. Format 3: Standard 256B End Header Flit Format for Streaming Protocola

<figure>

+0

+43

+44

+45

+46

+49

+50

+59

+60

$+ 6 3$

Byte 0

Flit Chunk 0 64B (from Protocol Layer)

Byte 64

Flit Chunk 1 64B (from Protocol Layer)

Byte 128

Flit Chunk 2 64B (from Protocol Layer)

Byte 192

44B of Flit Chunk 3 (from Protocol Layer)

FH B0b

FH B1b

4B
(from Protocol
Layer)

10B
Reserved

CO BOC

C0 B1c

C1 B0c

C1 B1c

</figure>

a. See Figure 2-1 for color mapping.

b. Flit Header Byte 0 and Byte 1, respectively.

c. CRC0 Byte 0, CRC0 Byte 1, CRC1 Byte 0, and CRC1 Byte 1, respectively.

<figure>
<figcaption>Figure 3-16. Format 3: Standard 256B End Header Flit Format for Management Transport Protocolª</figcaption>

+0

+39

+40

+43

+44

+45

+46

+49

+50

$\frac { n } { t }$

+60

$\infty$

Byte 0

Flit Chunk 0 64B (from Protocol Layer)

Byte 64

Flit Chunk 1 64B (from Protocol Layer)

Byte 128

Flit Chunk 2 64B (from Protocol Layer)

Byte 192

40B of Flit Chunk 3 (from Protocol Layer)

4B
Rsvd

FH B0b

FH B1b

4B CRD
(from Protocol
Layer)

10B
Reserved

CO BOC

C0 B1c

C1 B0c

C1 B1c

</figure>

a. See Figure 2-1 for color mapping.

b. Flit Header Byte 0 and Byte 1, respectively.

c. CRCO Byte 0, CRC0 Byte 1, CRC1 Byte 0, and CRC1 Byte 1, respectively.

<figure>
<figcaption>Figure 3-17. Format 4: Standard 256B Start Header Flit Format for CXL.cachemem or Streaming Protocolª</figcaption>

+0

+1

+2

+49

+50

$\frac { m } { t }$

+60

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

50B of Flit Chunk 3 (from Protocol Layer)

10B
Reserved

CO BOC

C0 B1c

C1 B0c

C1 B1c

</figure>

a. See Figure 2-1 for color mapping.

b. Flit Header Byte 0 and Byte 1, respectively.

c. CRCO Byte 0, CRC0 Byte 1, CRC1 Byte 0, and CRC1 Byte 1, respectively.

Figure 3-18. Format 4: Standard 256B Start Header Flit Format for CXL.io or PCIeª

+0

+1

+2

+45

+46

+49

+50

+59

+60

$\infty$

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

$\overrightarrow { \mathrm { U } }$ B0d

C1 B1d

a. See Figure 2-1 for color mapping.

b. Flit Header Byte 0 and Byte 1, respectively.

c. DLP Byte 2, Byte 3, Byte 4, and Byte 5, respectively.

d. CRC0 Byte 0, CRC0 Byte 1, CRC1 Byte 0, and CRC1 Byte 1, respectively.

<figure>
<figcaption>Figure 3-19. Format 4: Standard 256B Start Header Flit Format for Management Transport Protocolª</figcaption>

+0

+1

+2

+41

+42

+45

+46

+49

+50

$\frac { 9 } { 7 }$

+60

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

42B of Flit Chunk 3 (from Protocol Layer)

4B
Rsvd

4B CRD
(from Protocol
Layer)

10B
Reserved

CO BOC

C0 B1c

C1 B0c

C1 B1c

</figure>

a. See Figure 2-1 for color mapping.

b. Flit Header Byte 0 and Byte 1, respectively.

c. CRCO Byte 0, CRC0 Byte 1, CRC1 Byte 0, and CRC1 Byte 1, respectively.

<table>
<caption>Table 3-4. Flit Header for Format 3, Format 4, Format 5, and Format 6 without Retry</caption>
<tr>
<th rowspan="2">Byte</th>
<th rowspan="2">Bit</th>
<th colspan="4">Description</th>
</tr>
<tr>
<th>CXL 256B Flit Mode</th>
<th>PCIe Flit Mode</th>
<th>Streaming Protocol</th>
<th>Management Transport Protocol</th>
</tr>
<tr>
<td rowspan="6">0</td>
<td rowspan="2">[7:6]</td>
<td rowspan="2">Protocol Identifier: 00b: D2D Adapter/CXL.io NOP Flit 01b: CXL.io Flit $\begin{array}{} { 1 0 b : \text { CXL. Cachememem Fli } } \\ { 1 1 b : \text { ARB/MUX Flit } } \end{array}$</td>
<td rowspan="2">Protocol Identifier: 00b: D2D Adapter/PCIe NOP Flit 01b: PCIe Flit All other encodings are reserved.</td>
<td>Protocol Identifier: 00b: D2D Adapter NOP Flit Remaining encodings are</td>
<td>Protocol Identifier: 00b: D2D Adapter NOP Flit 01b: Management Flit</td>
</tr>
<tr>
<td>permitted to be used by Protocol Layer in a vendor defined manner. Protocol $\begin{array}{} { \text { Layer must never set this } } \\ { \text { to 00b for Flits sent across } } \end{array}$ FDI.</td>
<td>All other encodings are reserved.</td>
</tr>
<tr>
<td rowspan="2">[5]</td>
<td rowspan="2">Stack Identifier: 0: Stack 0 1: Stack 1</td>
<td></td>
<td rowspan="2"></td>
<td rowspan="2"></td>
</tr>
<tr>
<td></td>
</tr>
<tr>
<td>[4]</td>
<td colspan="2">Reserved for CXL.cachemem For CXL.io or PCIe Flit Mode: 0: DLLP Payload in DLP 2 .. 5 1: Optimized_Update_FC or Flit_Marker in DLP2 .. 5</td>
<td>Reserved</td>
<td></td>
</tr>
<tr>
<td>[3:0]</td>
<td>Reserved</td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td rowspan="2">1</td>
<td>[7:6]</td>
<td colspan="3">Flit Type: 00b: CXL/PCIe/Streaming Flit/D2D Adapter NOP Flit $\left( \mathrm { s e e } S _ { t } \right.$ Section 11.2 for details) 10b: Management Flit 11b: Reserved</td>
<td></td>
</tr>
<tr>
<td>[5:0]</td>
<td>Reserved</td>
<td></td>
<td></td>
<td></td>
</tr>
</table>

<table>
<caption>Table 3-5. Flit Header for Format 3, Format 4, Format 5, and Format 6 with Retry</caption>
<tr>
<th rowspan="2">Byte</th>
<th rowspan="2">Bit</th>
<th colspan="4">Description</th>
</tr>
<tr>
<th>CXL 256B Flit Mode</th>
<th>PCIe Flit Mode</th>
<th>Streaming Protocol</th>
<th>Management Transport Protocol</th>
</tr>
<tr>
<td rowspan="4">0</td>
<td>[7:6]</td>
<td>Protocol Identifier: 00b: D2D Adapter/CXL.io NOP Flit 01b: CXL.io Flit $\begin{array}{} { 1 0 b : \text { CXL. Cachememem Fli } } \\ { 1 1 b : \text { ARB/MUX Flit } } \end{array}$</td>
<td>Protocol Identifier: 00b: D2D Adapter/PCIe NOP Flit 01b: PCIe Flit All other encodings are reserved</td>
<td>Protocol Identifier: 00b: D2D Adapter NOP Flit Remaining encodings are permitted to be used by Protocol Layer in a vendor defined manner. Protocol Layer must never set this to 00b for Flits sent across FDI.</td>
<td>Protocol Identifier: 00b: D2D Adapter NOP Flit 01b: Management Flit All other encodings are reserved.</td>
</tr>
<tr>
<td>[5]</td>
<td>Stack Identifier: 0: Stack 0 1: Stack 1</td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td>[4]</td>
<td colspan="2">Reserved for CXL.cachemem For CXL.io or PCIe Flit Mode: 0: DLLP Payload in DLP 2 .. 5 1: Optimized_Update_FC or Flit_Marker in DLP2 .. 5</td>
<td>Reserved</td>
<td></td>
</tr>
<tr>
<td>[3:0]</td>
<td colspan="3">$\bar { T h \epsilon }$ upper four bits of Sequence number "S" (i.e., S[7:4])</td>
<td></td>
</tr>
<tr>
<td rowspan="3">1</td>
<td>[7:6]</td>
<td colspan="3">Flit Type: 00b: CXL/PCIe/Streaming Flit/D2D Adapter NOP Flit 01b: Test Flit (see Section 11.2 for details) $\begin{array}{} { 1 0 b : \text { Management Fil } } \\ { 1 1 h : \text { Reserved } } \end{array}$</td>
<td></td>
</tr>
<tr>
<td>[5:4]</td>
<td colspan="3">Ack or Nak Information: 00b: Explicit Sequence number "S" of the current Flit is present. 01b: Ack. The sequence number "S" carries the Ack'ed sequence number. 10b: Nak. The sequence number "S" carries 255 if N=1; otherwise, it carries N-1; where number. 11b: Reserved</td>
<td>N is the Nak'ed sequence</td>
</tr>
<tr>
<td>[3:0]</td>
<td colspan="4">The lower four bits of Sequence number "S" (i.e., S[3:0]). Sequence number 0 is reserved and if present, it implies no Ack or Nak is sent.</td>
</tr>
</table>

## 3.3.4 Latency-Optimized 256B Flit Formats

Two Latency-Optimized 256B Flit Formats are defined: Format 5 and Format 6. It is strongly
recommended that UCIe implementations support Format 6 for CXL 256B Flit Mode protocol to get
the best latency benefits.

Both formats look the same from the Adapter perspective, the only difference is whether the Protocol
Layer is filling in the optional bytes of protocol information . The Latency-Optimized 256B without
Optional bytes Flit Format (or Format 5) is when the Protocol Layer is not filling in the optional bytes,
whereas the Latency-Optimized 256B with Optional bytes Flit Format (or Format 6) is when the
Protocol Layer is filling in the optional bytes.

Latency-Optimized 256B Flit Formats (with Optional bytes or without Optional bytes) support is
optional with Streaming protocols. Protocol Layer only populates bits [7:6] of the Flit Header, and it
must never set 00b for bits [7:6].

Latency-Optimized Flit with Optional Bytes Flit Format is optional for PCIe Flit Mode protocol.
Figure 3-23 shows the Flit Format example.

Two sets of CRC are computed. CRC0 is computed using Flit Bytes 0 to 125 assigned to the
corresponding bytes of the CRC message input (including the Flit Header bits and if applicable, the
DLP bits inserted by the Adapter). CRC1 is computed using Flit Bytes 128 to 253 as the message input
with Flit Byte 128 assigned to CRC message Byte 0, Flit Byte 129 assigned to CRC message Byte 1
and so on until Flit Byte 253 assigned to CRC message Byte 125. If Retry is not required, the Adapter
still computes and drives CRC bytes - the Receiver is strongly recommended to treat a CRC error as
UIE in this situation.

For Management Flits (when successfully negotiated), the Protocol Layer must drive bits [7:6] in Byte
1 of Flit Header to 00b for Protocol Flit and to 10b.

For Management Flits using Format 5, Bytes 240 to 243 are driven from the Protocol Layer with
Management Transport Credit Return DWORD (CRD) Bytes 0 to 3 (see Section 8.2.5.2.2 for CRD
format). See Figure 3-22 for details.

If CXL.io is negotiated along with Management Transport protocol on the same stack for Format 5:

· If bits [7:6] of Byte 1 are 10b, the Adapter drives 0 on Bytes 122 to 125 and 244 to 253

· If bits [7:6] of Byte 1 are 00b, then Bytes 122 to 125 are treated per the CXL.io DLP rules of this
flit format and Bytes 250 to 253 are treated per the CXL.io FM rules of this flit format

For Management Flits using Format 6, Bytes 250 to 253 are driven from the Protocol Layer with
Management Transport Credit Return DWORD (CRD) Bytes 0 to 3 (see Section 8.2.5.2.2 for CRD
format). Similarly, Bytes 244 to 249 are driven from the Protocol Layer as 0. See Figure 3-26 for
details.

If PCIe/CXL.io is negotiated along with Management Transport protocol on the same stack for Format
6:

· If bits [7:6] of Byte 1 are 10b, the Adapter passes through Bytes 122 to 125 and 248 to 253

· If bits [7:6] of Byte 1 are 00b, then Bytes 122 to 125 are treated per the PCIe/CXL.io DLP rules of
this flit format, Bytes 250 to 253 are treated per the PCIe/CXL.io FM rules of this flit format, and
the Adapter drives 0 on Bytes 248 and 249

<figure>
<figcaption>Figure 3-20. Format 5: Latency-Optimized 256B without Optional Bytes Flit Format for CXL.ioª</figcaption>

+0

+1

+2

+51

+52

+57

+58

+61

+62

+63

Byte 0

FH B0b

FH B1b

62B of Flit Chunk 0 (from Protocol Layer)

58B of Flit Chunk 1 (from Protocol Layer)

DLP B2C

DLP B3c

DLP B5c

Byte 64

DLP B4c

C0 B0d

C0 B1d

Byte 128

Flit Chunk 2 64B (from Protocol Layer)

Byte 192

52B of Flit Chunk 3 (from Protocol Layer)

6B
Reserved

FM B0e

FM B1e

FM B2e

FM B3e

$\overrightarrow { \mathrm { U } }$ B0d

C1 B1d

</figure>

a. See Figure 2-1 for color mapping.

b. Flit Header Byte 0 and Byte 1, respectively.

c. DLP Byte 2, Byte 3, Byte 4, and Byte 5, respectively.

d. CRCO Byte 0, CRC0 Byte 1, CRC1 Byte 0, and CRC1 Byte 1, respectively.

e. Flit_Marker or Optimized_Update_FC Byte 0, Byte 1, Byte 2, and Byte 3, respectively.

<figure>
<figcaption>Figure 3-21. Format 5: Latency-Optimized 256B without Optional Bytes Flit Format for CXL.cachemem and Streaming Protocolª</figcaption>

+0

+1

+2

$+ 5 2$

+57

+58

$\frac { 6 } { + }$

+62

$+ 6 3$

Byte 0

FH B0b

FH B1b

62B of Flit Chunk 0 (from Protocol Layer)

Byte 64

58B of Flit Chunk 1 (from Protocol Layer)

4B
Reserved

CO BOC

CO $\frac { - } { m }$

Byte 128

Flit Chunk 2 64B (from Protocol Layer)

Byte 192

52B of Flit Chunk 3 (from Protocol Layer)

10B
Reserved

C1 B0c

C1 B1c

</figure>

a. See Figure 2-1 for color mapping.

b. Flit Header Byte 0 and Byte 1, respectively.

c. CRCO Byte 0, CRC0 Byte 1, CRC1 Byte 0, and CRC1 Byte 1, respectively.

<figure>
<figcaption>Figure 3-22. Format 5: Latency-Optimized 256B without Optional Bytes Flit Format for Management Transport Protocolª</figcaption>

+0

+1

+2

+47

+48

+51

+52

$+ 5 7$

+58

+61

+62

+63

Byte 0

FH B0b

FH B1b

62B of Flit Chunk 0 (from Protocol Layer)

Byte 64

58B of Flit Chunk 1 (from Protocol Layer)

4B
Reserved

CO BOC

C0 B1c

Byte 128

Flit Chunk 2 64B (from Protocol Layer)

$B y t e \quad 1 9 2$

48B of Flit Chunk 3 (from Protocol Layer)

4B CRD
(from Protocol
Layer)

10B
Reserved

$\bigtriangledown$ B0c

$\overrightarrow { \cup }$ B1c

</figure>

a. See Figure 2-1 for color mapping.

b. Flit Header Byte 0 and Byte 1, respectively.

c. CRC0 Byte 0, CRC0 Byte 1, CRC1 Byte 0, and CRC1 Byte 1, respectively.

<figure>
<figcaption>Figure 3-23. Format 6: Latency-Optimized 256B with Optional Bytes Flit Format for CXL.io or PCIeª</figcaption>

+0
+1

${ } ^ { N } _ { + }$

+55
+56

+57

+58

+61

+62

+63

Byte 0

FH B0b

FH B1b

62B of Flit Chunk 0 (from Protocol Layer)

DLP B2C

DLP B3c

DLP B4c

DLP B5c

Byte 64

58B of Flit Chunk 1 (from Protocol Layer)

C0 B0d

C0 B1d

$B y t e \quad 1 2 8$

Flit Chunk 2 64B (from Protocol Layer)

Byte 192

56B of Flit Chunk 3 (from Protocol Layer)

2B
Rsvd

FM B0e

FM B1e

FM B2e

FM B3e

C1 B0d

C1 B1d

</figure>

a. See Figure 2-1 for color mapping.

b. Flit Header Byte 0 and Byte 1, respectively.

c. DLP Byte 2, Byte 3, Byte 4, and Byte 5, respectively.

d. CRC0 Byte 0, CRC0 Byte 1, CRC1 Byte 0, and CRC1 Byte 1, respectively.

e. Flit_Marker Byte 0, Byte 1, Byte 2, and Byte 3, respectively.

<table>
<tr>
<th>Byte 192</th>
<th>Byte 128</th>
<th>$\frac { 5 } { 8 }$</th>
<th>Byte 0</th>
<th></th>
<th></th>
</tr>
<tr>
<th rowspan="8">52B of Flit Chunk 3</th>
<th rowspan="9"></th>
<th rowspan="6">58B</th>
<th>FH B0b</th>
<th>+0</th>
<th>Figure 3-24.</th>
</tr>
<tr>
<td>FH B1b</td>
<td>+1</td>
<td></td>
</tr>
<tr>
<th rowspan="5"></th>
<th rowspan="3">+2</th>
<th>Format 6: for CXL.cachememª</th>
</tr>
<tr>
<td></td>
</tr>
<tr>
<td></td>
</tr>
<tr>
<td></td>
<td>Latency-Optimized</td>
</tr>
<tr>
<td>of</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td rowspan="4"></td>
<td></td>
<td></td>
</tr>
<tr>
<td rowspan="3">(from</td>
<td>Flit</td>
<td rowspan="2"></td>
<td></td>
</tr>
<tr>
<td rowspan="7">Flit Chunk</td>
<td rowspan="2">Chunk</td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
</tr>
<tr>
<td rowspan="5">Protocol</td>
<td rowspan="2"></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td>62B</td>
<td></td>
<td></td>
</tr>
<tr>
<td>1</td>
<td></td>
<td></td>
<td>256B</td>
</tr>
<tr>
<td></td>
<td>of</td>
<td></td>
<td></td>
</tr>
<tr>
<td>(from</td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td>2</td>
<td></td>
<td>Flit</td>
<td></td>
<td></td>
</tr>
<tr>
<td rowspan="13">Layer)</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td>64B</td>
<td></td>
<td></td>
<td></td>
<td>with</td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td rowspan="22">(from Protocol Layer)</td>
<td></td>
<td>Chunk</td>
<td></td>
<td></td>
</tr>
<tr>
<td rowspan="3">Protocol</td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td rowspan="2">0</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td rowspan="11">Layer)</td>
<td rowspan="2">(from</td>
<td rowspan="2"></td>
<td>Optional</td>
</tr>
<tr>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td rowspan="2">Protocol</td>
<td rowspan="2">+51</td>
<td></td>
</tr>
<tr>
<td></td>
</tr>
<tr>
<td>H B4c</td>
<td rowspan="11">Layer)</td>
<td>+52</td>
<td>Bytes</td>
</tr>
<tr>
<td>H B5c</td>
<td></td>
<td>Flit</td>
</tr>
<tr>
<td>H B6c</td>
<td rowspan="2"></td>
<td></td>
</tr>
<tr>
<td>H B7c</td>
<td></td>
</tr>
<tr>
<td>H B8c</td>
<td rowspan="2">+57</td>
<td>Format</td>
</tr>
<tr>
<td>H B9c</td>
<td></td>
</tr>
<tr>
<td>H B10c</td>
<td>$H B O ^ { C }$</td>
<td rowspan="2">+58</td>
<td></td>
</tr>
<tr>
<td>H B11c</td>
<td>H B1c</td>
<td></td>
</tr>
<tr>
<td>H B12c</td>
<td>H B2c</td>
<td></td>
<td></td>
</tr>
<tr>
<td>H B13c</td>
<td>H B3c</td>
<td>+61</td>
<td></td>
</tr>
<tr>
<td>C1 B0d</td>
<td>C0 B0d</td>
<td>+62</td>
<td></td>
</tr>
<tr>
<td>C1 B1d</td>
<td>C0 B1d</td>
<td></td>
<td>+63</td>
<td></td>
</tr>
</table>

a. See Figure 2-1 for color mapping.

b. Flit Header Byte 0 and Byte 1, respectively.

c. H-slot Byte 0 through Byte 13, respectively (from Protocol Layer).

d. CRC0 Byte 0, CRC0 Byte 1, CRC1 Byte 0, and CRC1 Byte 1, respectively.

<table>
<tr>
<th>Byte 192</th>
<th>$B y t e$ 128</th>
<th>Byte 64</th>
<th>$\frac { 5 } { 8 }$</th>
<th></th>
<th></th>
<th>Figure</th>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td>FH B0b</td>
<td>+0</td>
<td></td>
<td>3-25.</td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td>FH B1b</td>
<td>$+ 1$</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td rowspan="2"></td>
<td></td>
<td>+2</td>
<td>for</td>
<td></td>
</tr>
<tr>
<td></td>
<td rowspan="2"></td>
<td></td>
<td></td>
<td>Streaming</td>
<td>Format 6:</td>
</tr>
<tr>
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
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>Protocolª</td>
<td>Latency-Optimized</td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td>62B</td>
<td rowspan="2"></td>
<td rowspan="2">62B</td>
<td></td>
<td rowspan="2"></td>
<td></td>
<td></td>
</tr>
<tr>
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
</tr>
<tr>
<td>of</td>
<td>Flit</td>
<td>of</td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>Flit</td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td>Flit</td>
<td></td>
<td></td>
<td>62B</td>
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
</tr>
<tr>
<td></td>
<td rowspan="2">Chunk</td>
<td></td>
<td>of</td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td>Chunk</td>
<td>Chunk</td>
<td></td>
<td></td>
<td></td>
<td>256B</td>
</tr>
<tr>
<td></td>
<td>2</td>
<td></td>
<td>Flit</td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td>3</td>
<td>64B</td>
<td>1</td>
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
<td>with</td>
</tr>
<tr>
<td>(from</td>
<td>(from</td>
<td>(from</td>
<td>Chunk</td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td>0</td>
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
</tr>
<tr>
<td>Protocol</td>
<td>Protocol</td>
<td>Protocol</td>
<td>(from</td>
<td></td>
<td></td>
<td>Optional</td>
</tr>
<tr>
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
</tr>
<tr>
<td>Layer)</td>
<td></td>
<td>Layer)</td>
<td>Protocol</td>
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
</tr>
<tr>
<td></td>
<td>Layer)</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>Bytes</td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>Flit</td>
</tr>
<tr>
<td></td>
<td rowspan="2"></td>
<td rowspan="2"></td>
<td>Layer)</td>
<td></td>
<td></td>
<td rowspan="2">Format</td>
</tr>
<tr>
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
<td>$+ 6 1$</td>
<td></td>
<td></td>
</tr>
<tr>
<td>C1 B0c</td>
<td></td>
<td>$C 0 B 0 ^ { \circ }$</td>
<td></td>
<td>+62</td>
<td></td>
<td></td>
</tr>
<tr>
<td>C1 B1c</td>
<td></td>
<td>C0 B1c</td>
<td></td>
<td>+63</td>
<td></td>
<td></td>
</tr>
</table>

a. See Figure 2-1 for color mapping.

b. Flit Header Byte 0 and Byte 1, respectively.

c. CRC0 Byte 0, CRC0 Byte 1, CRC1 Byte 0, and CRC1 Byte 1, respectively.

<table>
<tr>
<th>c. CRC0 b. Flit Header</th>
<th>a. See Figure</th>
<th>Byte 192</th>
<th>$\frac { 5 } { 8 }$ 128</th>
<th>Byte 64</th>
<th>$B y t e \quad 0$</th>
<th></th>
<th></th>
<th>Figure</th>
</tr>
<tr>
<td colspan="2">Byte</td>
<td></td>
<td></td>
<td rowspan="2"></td>
<td>FH B0b</td>
<td>40</td>
<td></td>
<td>3-26.</td>
</tr>
<tr>
<td>0, Byte</td>
<td>2-1</td>
<td></td>
<td></td>
<td>FH B1b</td>
<td>71</td>
<td></td>
<td></td>
</tr>
<tr>
<td>CRC0 Byte 0 and</td>
<td>for color</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>4</td>
<td>for</td>
<td>Format</td>
</tr>
<tr>
<td>1, Byte</td>
<td>mapping.</td>
<td>52B</td>
<td rowspan="2"></td>
<td></td>
<td></td>
<td></td>
<td>Management</td>
<td>6:</td>
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
<td>CRC1 1,</td>
<td></td>
<td>of</td>
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
</tr>
<tr>
<td></td>
<td></td>
<td>Flit</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td>Byte</td>
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
</tr>
<tr>
<td>0, respectively.</td>
<td></td>
<td>Chunk</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>Transport</td>
<td>Latency-Optimized</td>
</tr>
<tr>
<td></td>
<td></td>
<td>3</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td>and</td>
<td></td>
<td></td>
<td></td>
<td>62B</td>
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
</tr>
<tr>
<td>CRC1</td>
<td></td>
<td>(from</td>
<td>Flit</td>
<td>of</td>
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
<td>Flit</td>
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
<td>62B</td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td>Byte</td>
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
<td>1,</td>
<td></td>
<td>Protocol</td>
<td>Chunk</td>
<td>Chunk</td>
<td>of</td>
<td></td>
<td>Protocolª</td>
<td>256B</td>
</tr>
<tr>
<td></td>
<td></td>
<td>Layer)</td>
<td>2</td>
<td>1</td>
<td>Flit</td>
<td></td>
<td></td>
<td>with</td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td>64B</td>
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
</tr>
<tr>
<td>respectively.</td>
<td></td>
<td></td>
<td>(from</td>
<td>(from</td>
<td>Chunk 0</td>
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
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td>Protocol</td>
<td>Protocol</td>
<td>(from</td>
<td></td>
<td></td>
<td>Optional</td>
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
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>Protocol</td>
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
<td>+51</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td rowspan="4"></td>
<td></td>
<td></td>
<td>Layer)</td>
<td></td>
<td>+52</td>
<td></td>
<td>Bytes</td>
</tr>
<tr>
<td></td>
<td></td>
<td rowspan="3">Layer)</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td rowspan="2"></td>
<td rowspan="2">Rsvd 6B</td>
<td rowspan="2"></td>
<td rowspan="2">Layer)</td>
<td></td>
<td></td>
<td>Flit</td>
</tr>
<tr>
<td></td>
<td></td>
<td>Format</td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>+57</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td rowspan="2"></td>
<td>(from Protocol 4B CRD Layer)</td>
<td></td>
<td></td>
<td></td>
<td>+58</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>+61</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>C1 B0c</td>
<td></td>
<td>CO BOC</td>
<td></td>
<td>+62</td>
<td></td>
<td></td>
</tr>
<tr>
<td></td>
<td></td>
<td>$B 1 ^ { c }$</td>
<td></td>
<td>C0 B1c</td>
<td></td>
<td>$+ 6 3$</td>
<td></td>
<td></td>
</tr>
</table>

The Flit Header byte formats are the same as Table 3-5 when Retry is required; otherwise, they are
the same as Table 3-4. The DLP rules are also the same as defined in Section 3.3.3 for CXL protocol,
except that Flit_Marker/Optimized_Update_FC has dedicated space in the Flit (i.e., bit [4] of Byte 0
corresponds to the Flit_Marker bytes, and not the DLP bytes). If Optimized_Update_FC is sent, the
DLP Bytes 2:5 shown in Figure 3-20 must be reserved. If bit [4] of Byte 0 in the Flit Header is 0b,
then the Flit_Marker bytes are reserved.

## 3.3.5 Flit Format-related Implementation Requirements for Protocol Layer and Adapter

Table 3-6 lists the different Flit Formats supported in UCIe.

<table>
<caption>Table 3-6. Summary of Flit Formats</caption>
<tr>
<th>Format Number</th>
<th>Name</th>
<th>Notes</th>
<th>For Details, See Also</th>
</tr>
<tr>
<td>$F o r m a t$ 1</td>
<td>Raw</td>
<td>Protocol Layer populates all the bytes on FDI. Adapter passes to RDI without modifications or additions.</td>
<td>· Section 3.3.1 · Figure 3-10</td>
</tr>
<tr>
<td>$F o r m a t \quad 2$</td>
<td>68B Flit</td>
<td>Protocol Layer transmits 64B per Flit on FDI. Adapter inserts two bytes of Flit header and two bytes of CRC and performs the required barrel shifting of bytes before transmitting on RDI. On the RX, Adapter strips out the Flit header and CRC only sending the 64B per Flit to the Protocol Layer on FDI.</td>
<td>· Section 3.3.2 · Figure 3-11 · Figure 3-12</td>
</tr>
<tr>
<td>Format 3</td>
<td>$S t a n d a r d \quad 2 5 6 B \quad E n d$ Header Flit</td>
<td>Protocol Layer transmits 256B of Flit on FDI, while driving 0b on the bits reserved for the Adapter. Adapter fills in the relevant Flit header and CRC information before transmitting on RDI. On the Rx, Adapter forwards the Flit received modifying any bits applicable Layer must ignore any bits $\begin{array}{} { \text { Jle to the Protocol Layer and Layer without } } \\ { \text { not applicable for it. Flit Header is located } } \end{array}$ on Byte 236 and Byte 237</td>
<td>· Section 3.3.3 · Figure 3-14 · Figure 3-15</td>
</tr>
<tr>
<td>Format 4</td>
<td>$S t a n d a r d \quad 2 5 6 B$ Start Header Flit</td>
<td>Protocol Layer transmits 256B of Flit on FDI, while driving 0b on the bits reserved for the Adapter. Adapter fills in the relevant Flit header and CRC information before transmitting on RDI. On the Rx, Adapter forwards the Flit received from the Link to the Protocol Layer without $\begin{array}{} { \text { Layer must ignore any bits nota applicable for iti } . \text { and the protocol } } \\ { \text { on Byte 0 and Byte 1 of the Flit } } \end{array}$</td>
<td>· Section 3.3.3 · Figure 3-17 · Figure 3-18</td>
</tr>
<tr>
<td>Format 5</td>
<td>Latency-Optimized 256B without Optional Bytes Flit</td>
<td>Protocol Layer transmits 256B of Flit on FDI, while driving 0b on the bits reserved for the Adapter. Adapter fills in the relevant Flit header and CRC information before transmitting on RDI. On the Rx, Adapter forwards the Flit received from the Link to the Protocol Layer without $L a y e r \quad m u s t \quad i g n o r e \quad a n y \quad b i t s \quad n o t \quad a p p l i c a b l e \quad f o r \quad i t . C R C \quad b y t e s \quad s e n t \quad w i t h$ in not used by the Protocol Layer.</td>
<td>· Section 3.3.4 · Figure 3-20 · Figure 3-21</td>
</tr>
<tr>
<td>Format 6</td>
<td>Latency-Optimized 256B with Optional Bytes Flit</td>
<td>Protocol Layer transmits 256B of Flit on FDI, while driving 0b on the bits reserved for the Adapter. Adapter fills in the and CRC information before transmitting on RDI. $R x _ { \prime }$ forwards the Flit received from the Link to the Protocol Layer without modifying any bits applicable to the Protocol Layer, and the Protocol Layer must ignore any bits not applicable for it. CRC bytes sent $w i t h$ each 128B of the Flit, and optional bytes are used by the Protocol Layer.</td>
<td>· Section 3.3.4 · $F i g u r e \quad 3 - 2 3$ · Figure 3-24 · Figure 3-25</td>
</tr>
</table>

Table 3-7 gives the implementation requirements and Protocol Mapping for the different Flit Formats.
For PCIe and CXL protocols, the implementation requirements must be followed by the Protocol Layer
as well as the Adapter implementations. For Streaming protocols, the implementation requirements
are for the Adapter only; Protocol Layer interoperability and implementation requirements are vendor
specific.

<table>
<caption>Table 3-7. Protocol Mapping and Implementation Requirements</caption>
<tr>
<th>Format Number</th>
<th>Flit Format Name</th>
<th>PCIe $\begin{array}{} { \text { Non-ril } } \\ { \text { Mode } } \end{array}$</th>
<th>PCIe Flit Mode</th>
<th>$C X L \quad 6 8 B$</th>
<th>CXL 256B Flit Mode</th>
<th>Streaming Protocol</th>
<th>Management Transport Protocol</th>
</tr>
<tr>
<td>1</td>
<td>Raw</td>
<td>Optional</td>
<td>Optional</td>
<td>Optional</td>
<td>Optional</td>
<td>Mandatory</td>
<td>Optional</td>
</tr>
<tr>
<td rowspan="2">2</td>
<td>68B $\left( < = 3 2 G T / s \right) ^ { a }$</td>
<td>$\mathrm { M a n d a t o r y }$</td>
<td>$N / A$</td>
<td>$\mathrm { M a n d a t o r y }$</td>
<td>$N / A$</td>
<td>$\mathrm { O p t i o n a l } ^ { \mathrm { b } }$</td>
<td>$N / A$</td>
</tr>
<tr>
<td>68B $\left( > 3 2 G T / s \right) ^ { a }$</td>
<td>Not Supported</td>
<td></td>
<td colspan="4"></td>
</tr>
<tr>
<td>3</td>
<td>$S t a n d a r d \quad 2 5 6 B$</td>
<td>$N / A$</td>
<td>Mandatory</td>
<td>$N / A$</td>
<td>$N / A$</td>
<td>$\mathrm { O p t i o n a l } ^ { \mathrm { b } }$</td>
<td>Optional</td>
</tr>
<tr>
<td>4</td>
<td>$S t a n d a r d \quad 2 5 6 B$ $\mathrm { S t a r t } \mathrm { H e a d e r }$</td>
<td>$N / A$</td>
<td>$\mathrm { O p t i o n a l } ^ { \mathrm { C } }$</td>
<td>$N / A$</td>
<td>$\mathrm { M a n d a t o r y }$</td>
<td>$\mathrm { O p t i o n a l } ^ { \mathrm { b } }$</td>
<td>$\mathrm { O p t i o n a l }$</td>
</tr>
<tr>
<td>5</td>
<td>Latency- $\mathrm { O p t i m i z e d }$ 256B without Optional Bytes</td>
<td>$N / A$</td>
<td>$N / A$</td>
<td>$N / A$</td>
<td>Optional</td>
<td>$\mathrm { O p t i o n a l } ^ { b }$</td>
<td>Optional</td>
</tr>
<tr>
<td>6</td>
<td>Latency- $\mathrm { O p t i m i z e d }$ 256B with Optional Bytes</td>
<td>$N / A$</td>
<td>Strongly Recommendedd</td>
<td>$N / A$</td>
<td>$\mathrm { s t r o n g l y }$</td>
<td>Strongly Recommendedb</td>
<td>Optional</td>
</tr>
</table>

a. Refers to the negotiated maximum data rate.

b. If Streaming Flit Format capability is supported, else it is N/A.

c. If Standard Start Header for PCIe protocol capability is supported, else it is N/A.

d. If Latency-Optimized Flit with Optional Bytes for PCIe protocol capability is supported, else it is N/A.
If Enhanced Multi-Protocol capability is supported where at least one of the stacks supports PCIe, this format and the
corresponding capability are strongly recommended.

# 3.4 Decision Table for Flit Format and Protocol

Table 3-8 shows the Truth Table for determining Protocol. Once the protocol and Flit Format have been
negotiated during initial Link bring up, they cannot be changed until the UCIe Physical Layer
transitions to Reset state.

If a valid Protocol and Flit Format are not negotiated, then the Adapter takes the Link down and
reports the error if applicable.

<table>
<caption>Table 3-8. Truth Table for Determining Protocolª</caption>
<tr>
<th colspan="5">{FinCap.Adapter} bits or {MultiProtFinCap.Adapter} bitsb</th>
<th colspan="2">{FinCap.CXL} bits</th>
<th rowspan="2">Protocol</th>
</tr>
<tr>
<th>68B Flit Mode</th>
<th>CXL 256B Flit Mode</th>
<th>PCIe Flit Mode</th>
<th>Streaming Protocol</th>
<th>Management Transport Protocol</th>
<th>PCIe</th>
<th>CXL.io</th>
</tr>
<tr>
<td>1º</td>
<td>0</td>
<td>0</td>
<td>$X$ ☒</td>
<td>☒ x</td>
<td>0</td>
<td>1</td>
<td>CXLd without Management Transport protocol</td>
</tr>
<tr>
<td>a. 1e b. $0 ^ { \text { e } }$</td>
<td>1</td>
<td>1</td>
<td>$X$ ☒</td>
<td>0</td>
<td>0</td>
<td>$1 ^ { f }$</td>
<td>$\mathrm { C X L } ^ { \mathrm { d } } \mathrm { w i t h o u t } \mathrm { M a n a a c m e n t }$ Transport protocol</td>
</tr>
<tr>
<td>a. 1e b. $0 ^ { \text { e } }$</td>
<td>1</td>
<td>1</td>
<td>$X$ ☒</td>
<td>1</td>
<td>0</td>
<td>$1 ^ { f }$</td>
<td>CXLd with Management Transport protocol</td>
</tr>
<tr>
<td>$1 ^ { c }$</td>
<td>0</td>
<td>0</td>
<td>$X$ ☒</td>
<td>$X$ ☒</td>
<td>1</td>
<td>0</td>
<td>$\begin{array}{} { \text { PCIe9 without Management } } \\ { \text { Transoort orotocol } } \end{array}$</td>
</tr>
<tr>
<td>a. 1e b. $0 ^ { \mathrm { e } }$</td>
<td>0</td>
<td>1</td>
<td>$X$ ☒</td>
<td>0</td>
<td>$1 ^ { h }$</td>
<td>0</td>
<td>PCIe without Management Transport protocol</td>
</tr>
<tr>
<td>a. 1e b. $0 ^ { \mathrm { e } }$</td>
<td>0</td>
<td>1</td>
<td>$X$ ☒</td>
<td>1</td>
<td>$1 ^ { h }$</td>
<td>0</td>
<td>$P C I e \quad w i t h \quad M a n a g e m e n t$</td>
</tr>
<tr>
<td>N/A</td>
<td>N/A</td>
<td>N/A</td>
<td>$N / A$</td>
<td>N/A</td>
<td>N/A</td>
<td>N/A</td>
<td>$\begin{array}{} { \text { Streamingi with or without } } \\ { \text { Management Transport } } \end{array}$ protocol</td>
</tr>
<tr>
<td>N/A</td>
<td>$N / A$</td>
<td>N/A</td>
<td>$N / A$</td>
<td>$N / A$</td>
<td>N/A</td>
<td>$N / A$</td>
<td>Management Transport protocol]</td>
</tr>
</table>

a. x indicates don't care in this Table.

b. If Enhanced_Multi-Protocol capability is negotiated then {MultiProt \*. Adapter} messages are used to determine the protocol for
Stack 1. Stack 0 protocol is determined using the {FinCap .\* } messages.

c. 68B Flit Mode must only be advertised if the negotiated maximum data rate is <= 32 GT/s.

d. For CXL protocol, the specific combination of Single Protocol vs Type 1 vs. Type 2 vs. Type 3 is determined using the CXL.cache
and CXL.mem capable/enable bits in addition to the CXL.io capable/enable bit in {FinCap.CXL}. The rules for that follow CXL
Specification. When CXL is the protocol, if CXL 256B Flit mode is 1, then the protocol follows CXL 256B Flit mode rules; otherwise,
the protocol follows CXL 68B Flit mode rules.

e. 68B Flit Mode must only be advertised if the negotiated maximum data rate is <= 32 GT/s. The value of 1 will be sent if the
negotiated maximum data rate is <= 32 GT/s. The value of 0 will be sent if the negotiated maximum data is > 32 GT/s.

f. CXL.io capable/enable must be 1 if CXL 256B Flit mode is negotiated.

g. For PCIe protocol, if PCIe Flit mode is 1, then the protocol follows PCIe Flit mode rules; otherwise, the protocol follows PCIe Non-
Flit mode rules.

h. PCIe capable/enable must be 1 if PCIe Flit mode is 1 but CXL 256B Flit mode is 0.

i. No sent for Streaming protocol negotiation, Streaming is the negotiated protocol if PCIe or CXL are not
$\begin{array}{} { \text { \left\{FinCap.*\right\} messayng } } \\ { \text { vertised, but Streaming } } \end{array}$ protocol is advertised. If Management Transport protocol was also advertised along with Streaming
protocol, then Transport protocol is enabled along with Streaming protocol.

j. No {FinCap .* } message is sent for Management Transport protocol negotiation, Management Transport is the negotiated
protocol if PCIe or CXL or Streaming are not advertised, but Management Transport protocol is advertised.

## IMPLEMENTATION NOTE

If the negotiated maximum data rate is <= 32 GT/s, the "68B Flit Mode" parameter is
advertised as set to 1 for both the CXL and PCIe protocols in {AdvCap.Adapter}
sideband messages. As seen in Table 3-8, this parameter is set to 1 in
{FinCap.Adapter} sideband messages whenever the CXL OR PCIe protocols are
negotiated and the negotiated maximum data rate is <= 32 GT/s; otherwise, this
parameter is cleared to 0.

The "CXL.io" and "PCIe" bits in the {AdvCap.CXL} sideband message disambiguate
between CXL support vs. PCIe support. It is permitted to set both to 1 in
{AdvCap.CXL} sideband messages. However, as seen in Table 3-8, only one of these
must be set in the {FinCap.CXL} sideband message to reflect the final negotiated
protocol for the corresponding stack. For example:

· If the DP and UP both support CXL and PCIe protocols, then both "CXL.io" and
"PCIe" will be set to 1 in the {AdvCap.CXL} sideband message

. If the DP decides to operate in CXL, the DP will set "CXL.io" to 1 and clear "PCIe"
to 0 in the {FinCap.CXL} sideband message, in which case the remaining CXL-
related bits in the {FinCap.CXL} sideband message are also applicable and are
assigned as per the negotiation

Table 3-9 (Truth Table 1) shows the truth table for deciding the Flit format in which to operate if PCIe
or CXL protocols are negotiated (with or without Management Transport protocol), and none of the
following are negotiated:

· Enhanced Multi_Protocol_Enable

· Standard 256B Start Header for PCIe protocol capability

· Latency-Optimized Flit with Optional Bytes for PCIe protocol capability

Table 3-10 (Truth Table 2) provides the Truth Table for determining the Flit Format for Streaming
protocols if Streaming Flit Format capability is negotiated or if Management Transport protocol is
negotiated without CXL or PCIe or Streaming protocols on the same stack. Note that for Streaming
protocol negotiation or for Management Transport protocol negotiation without CXL or PCIe protocol
multiplexed on the same stack, there are no {FinCap .* } messages exchanged. Each side of the UCIe
Link advertises its own capabilities in the {AdvCap.Adapter} message it sends. The bits in Table 3-10
represent the logical AND of the corresponding bits in the sent and received {AdvCap.Adapter}
messages. Truth Table 2 must be followed for determining the Flit Format if both sides of the Link
have any of the following capabilities are supported and enabled for both sides of the Link:

· Enhanced Multi-Protocol Capability

· Standard Start Header Flit for PCIe protocol capability

· Latency-Optimized Flit with Optional Bytes for PCIe protocol capability

For situations where {FinCap.Adapter} messages are sent, the bits in the truth table represent the
bits set in the {FinCap.Adapter} message.

It is permitted for the Adapter OR the Protocol Layer to take the Link down to LinkError if the desired
Flit Format is not negotiated or the negotiated Flit format and protocol combination is illegal (e.g., 68B
Flit Format 2 and Management Transport protocol combination).

<table>
<caption>Table 3-9. Truth Table 1</caption>
<tr>
<th colspan="6">{FinCap.Adapter} bitsª</th>
<th rowspan="2">Flit Format</th>
</tr>
<tr>
<th>Raw Format</th>
<th>68B Flit Mode</th>
<th>CXL 256B Flit Mode</th>
<th>PCIe Flit Mode</th>
<th>CXL_LatOpt Fmt5</th>
<th>CXL_LatOpt Fmt6</th>
</tr>
<tr>
<td>1</td>
<td>X ☒</td>
<td>$X$ ☒</td>
<td>$X$ ☒</td>
<td>$X$ ☒</td>
<td>$X$ ☒</td>
<td>Format 1: Raw Format</td>
</tr>
<tr>
<td>0</td>
<td>$x$ ☒</td>
<td>1</td>
<td>$x$ ☒</td>
<td>0</td>
<td>0</td>
<td>$\begin{array}{} { \text { Format } 4 : \text { Standard } 2 5 6 B \text { Start } } \\ { \text { Header Flit Format for } C X L } \end{array}$</td>
</tr>
<tr>
<td>0</td>
<td>X ☒</td>
<td>1</td>
<td>$X$ ☒</td>
<td>$X$ ☒</td>
<td>1</td>
<td>$\begin{array}{} { \text { Format } 6 : \text { Latency-Optimized } 2 5 6 E } \\ { \text { with Optional Bytes Flit Format for } } \end{array}$</td>
</tr>
<tr>
<td>0</td>
<td>$X$ ☒</td>
<td>1</td>
<td>$X$ ☒</td>
<td>1</td>
<td>0</td>
<td>$\begin{array}{} { \text { Format } 5 : \text { Latency- Optimuzed 250E } } \\ { \text { without Optional Bytes Flit Format } } \end{array}$ for CXL</td>
</tr>
<tr>
<td>0</td>
<td>X ☒</td>
<td>0</td>
<td>1</td>
<td>$X$ ☒</td>
<td>$X$ ☒</td>
<td>$F o r m a t \quad 3 : S t a n d a r d \quad 2 5 6 B \quad E n d$</td>
</tr>
<tr>
<td>0</td>
<td>1</td>
<td>0</td>
<td>0</td>
<td>$X$ ☒</td>
<td>$X$ ☒</td>
<td>$F o r m a t \quad 2 : 6 8 B \quad F l i t \quad F o r m a t$</td>
</tr>
</table>

a. x indicates don't care.
☒

<table>
<caption>Table 3-10. Truth Table 2</caption>
<tr>
<th colspan="6">Logical AND of Corresponding Bits in the Sent and Received {AdvCap.Adapter} Message OR the Bits Sent in the {FinCap.Adapter} Messagec</th>
<th rowspan="2">Final Negotiated Flit Formatª</th>
</tr>
<tr>
<th>Raw Formatb</th>
<th>68B Flit Formatc</th>
<th>Standard 256B $E n d \quad H e a d e r$</th>
<th>Standard 256B Start Header Flit Format</th>
<th>Latency- Optimized 256B without Optional Bytes Flit Format</th>
<th>Latency- Optimized 256B with Optional Bytes Flit Format</th>
</tr>
<tr>
<td>1</td>
<td>$X$ ☒</td>
<td>$X$ ☒</td>
<td>☒ x</td>
<td>$X$ ☒</td>
<td>$X$ ☒</td>
<td>Format 1: Raw Format</td>
</tr>
<tr>
<td>0</td>
<td>1</td>
<td>0</td>
<td>0</td>
<td>$X$ ☒</td>
<td>0</td>
<td>Format 2: 68B Flit Format</td>
</tr>
<tr>
<td>0</td>
<td>$X$ ☒</td>
<td>1</td>
<td>0</td>
<td>$X$ ☒</td>
<td>0</td>
<td>$\begin{array}{} { \text { Format } 3 : \text { Standard } 2 5 6 E } \\ { \text { End Header Flit Format } } \end{array}$</td>
</tr>
<tr>
<td>0</td>
<td>$X$ ☒</td>
<td>$X$ ☒</td>
<td>1</td>
<td>$X$ ☒</td>
<td>0</td>
<td>Format 4: Standard 256B Start Header Flit Format</td>
</tr>
<tr>
<td>0</td>
<td>0</td>
<td>0</td>
<td>0</td>
<td>1</td>
<td>0</td>
<td>Format 5: Latency- Optimized 256B without Optional Bytes Flit Format</td>
</tr>
<tr>
<td>0</td>
<td>X ☒</td>
<td>$X$ ☒</td>
<td>$X$ ☒</td>
<td>$X$ ☒</td>
<td>1</td>
<td>Format 6: Latency- Optimized 256B with Optional Bytes Flit Format</td>
</tr>
</table>

a. Format 6 is the highest priority format when Raw Format is not advertised because it has the best performance characteristics.
Between Format 4 and Format 3, Format 4 is higher priority because it enables lower latency through the D2D Adapter when
multiplexing different protocols. Format 5 has the highest overhead and therefore has the lowest priority relative to other
formats.

b. Raw Format is always explicitly enabled through UCIe Link Control register and advertised only when it is the required format of
operation to ensure interoperability, and therefore appears as a higher priority in the decision table.

c. x indicates don't care.
☒

# 3.5 State Machine Hierarchy

UCIe has a hierarchical approach to Link state management in order to have well-defined functionality
partitioning between the different layers and also enabling common state transitions or sequencing at
FDI and RDI.

Figure 3-27 shows examples of state machine hierarchy for different configurations. For CXL, the
ARB/MUX vLSMs are exposed on FDI pl_state_sts. The Adapter LSM is used to coordinate Link
states with remote Link Partner and is required for all configurations. Each protocol stack has its
corresponding Adapter LSM. For PCIe or Streaming protocols, the Adapter LSM is exposed on FDI
pl_state_sts.

The RDI state machine (SM) is used to abstract the Physical Layer states for the upper layers. The
Adapter data path and RDI data width can be extended for multi-module configurations; however,
there is a single RDI state machine for this configuration. The Multi-module PHY Logic creates the
abstraction and coordinates between the RDI state and individual modules. The following rules apply:

· vLSM state transitions are coordinated with remote Link partner using ALMPs on mainband data
path. The rules for state transitions follow the CXL 256B Flit Mode rules in the CXL Specification.

· Adapter LSM state transitions are coordinated with remote Link partner using
{LinkMgmt.Adapter*} sideband messages. These messages are originated and received by the
D2D Adapter.

· RDI SM state transitions are coordinated with the remote Link partner using {LinkMgmt.RDI*}
sideband messages. These messages are originated and received by the Physical Layer.

<figure>
<figcaption>Figure 3-27. State Machine Hierarchy Examples</figcaption>

FDI

FDI

FDI

ARB/MUX

vLSM

vLSM

Adapter $L S M$

Adapter $L S M$

-RDI.

RDI SM

RDI-

RDI SM

(a) CXL example

(b) PCIe or Streaming example

</figure>

General rules for State transition hierarchy are captured below. For specific sequencing, see the rules
outlined in Chapter 10.0.

. Active State transitions: RDI SM must be in Active before Adapter LSM can begin negotiation to
transition to Active. Adapter LSM must be in Active before vLSMs can begin negotiations to
transition to Active.

· Retrain State transitions: RDI SM must be in Retrain before propagating Retrain to Adapter LSMs.
If RDI SM is in Retrain, Retrain must be propagated to all Adapter LSMs that are in Active state.

Adapter must not request Retrain exit on RDI before all the relevant Adapter LSMs have
transitioned to Retrain.

· PM State transitions (both L1 and L2): Both CXL.io and CXL.cachemem vLSMs (if CXL), must
transition to PM before the corresponding Adapter LSM can transition to PM. All Adapter LSMs
(if multiple stacks are enabled on the same Adapter) must be in PM before RDI SM is transitioned
to PM.

. LinkError State transitions: RDI SM must be in LinkError before Adapter LSM can transition to
LinkError. RDI SMs coordinate LinkError transition with remote Link partner using sideband, and
each RDI SM propagates LinkError to all enabled Adapter LSMs. Adapter LSM must be in LinkError
before propagating LinkError to both vLSMs if CXL. LinkError transition takes priority over
LinkReset or Disabled transitions. Adapter must not request LinkError exit on RDI before all the
relevant Adapter LSMs and CXL vLSMs have transitioned to LinkError.

· LinkReset or Disabled State transitions: Adapter LSM negotiates LinkReset or Disabled transition
with its remote Link partner using sideband messages. LinkReset or Disabled is propagated to RDI
SM only if all the Adapter LSMs associated with it transition to LinkReset or Disabled. Disabled
transition takes priority over LinkReset transition. If RDI SM moves to LinkReset or Disabled, it
must be propagated to all Adapter LSMs. If Adapter LSM moves to LinkReset or Disabled, it must
propagate it to both vLSMs for CXL protocol.

For UCIe Retimers, it is the responsibility of the Retimer die to negotiate state transitions with the
remote Retimer partner and make sure the different UCIe Die are in sync and do not time out waiting
for a response. As an example, referring to Figure 1-18, if UCIe Die 0 sends an Active Request
message for the Adapter LSM to UCIe Retimer 0, UCIe Retimer 0 must resolve with UCIe Retimer 1
that an Active Request message has been forwarded to UCIe Die 1 and that UCIe Die 1 has responded
with an Active Status message before responding to UCIe Die 0 with an Active Status message. The
Off Package Interconnect cannot be taken to a low power state unless all the relevant states on UCIe
Die 0 AND UCIe Die 1 have reached the low power state. UCIe Retimers must respond with "Stall"
encoding every 4ms while completing resolution with the remote Retimer partner.

## 3.6 Power Management Link States

Power management states are mandatory for PCIe and CXL protocols. FDI supports L1 and L2 power
states which follow the handshake rules and state transitions of CXL 256B Flit Mode. RDI supports L1
and L2 on the interfaces for Physical Layer to perform power management optimizations; however,
the Physical Layer is permitted to internally map both L1 and L2 to a common state. These together
allow for global clock gating and enable system level flows like Package-Level Idle (C-states). Other
Protocols are permitted to disable PM flows by always sending a PMNAK for a PM request from remote
Link partner.

When Management Transport protocol is supported and negotiated with CXL.io/PCIe/Streaming on
the same stack, L1 and L2 entry requests to the Adapter from the Management Port Gateway
multiplexer (MPG mux) must comprehend L1 and L2 entry readiness of the Management Transport
protocol as well as the co-located protocol stack, in an implementation specific manner. Additionally,
the MPG mux must also follow the FDI semantics for PM rules of the co-located CXL.io/PCIe/
Streaming protocol. Similarly, L1 and L2 exit would wake both the Management Transport protocol
and as well as the co-located protocol stack, and exit flow semantics must adhere to the negotiated
CXL.io/PCIe/Streaming protocol.

The Power management state entry sequence is as follows:

1\. Protocol Layer PM entry request: FDI defines a common flow for PM entry request at the
interface that is based on Link idle time. All protocols using UCIe must follow that flow when PM
needs to be supported. For CXL protocol, D2D Adapter implements the ARB/MUX functionality and
follows the handshakes defined in CXL Specification (corresponding to the "CXL 256B Flit Mode",

since all ALMPs also go through the Retry buffer in UCIe). Even CXL 68B Flit Mode over UCIe uses
the "CXL 256B Flit Mode" ALMP formats and flows (but the Flit is truncated to 64B and two bytes
of Flit header and two bytes of CRC are added by the Adapter to make a 68B Flit). For PCIe
protocol in UCIe Flit Mode, PM DLLP handshakes are NOT used. Protocol Layer requests PM entry
on FDI based on Link idle time. The specific algorithm and hysteresis for determining Link idle
time is implementation specific.

2\. Adapter Link State Machine PM entry: The PM transition for this is coordinated over sideband
with remote Link partner. In scenarios where the Adapter is multiplexing between two protocol
stacks, each stack's Link State Machine must transition to PM independently.

3\. PM entry on RDI: Once all the Adapter's LSMs are in a PM state, the Adapter initiates PM entry
on the RDI as defined in Section 10.2.9.

4\. Physical Layer moves to a deeper PM state and takes the necessary actions for power
management. Note that the sideband Link must remain active because the sideband Link is used
to initiate PM exit.

<figure>
<figcaption>Figure 3-28. Example of Hierarchical PM Entry for CXL</figcaption>

ARB/MUX vLSM
Die 0

Adapter LSM
Die 0

Physical Layer SM
Die 0

D2D
CHANNEL

Physical Layer SM
Die 1

Adapter LSM
Die 1

ARB/MUX vLSM
Die 1

vLSM PM handshake using ALMPs
(Mainband)

Once both vLSMs are in PM, Retry buffer empty, then do Adapter LSM handshake
(Sideband)

Once all Adapter LSMs are in PM, Physical Layer handshake
(Sideband)

$P M$ Entry Complete-

</figure>

PM exit follows the reverse sequence of wake up as mentioned below:

1\. Active request from Protocol Layer is transmitted across the FDI and RDI to the local Physical
Layer.

2\. The Physical Layer uses sideband to coordinate wake up and retraining of the physical Link.

3\. Once the physical Link is retrained, the RDI is in Active state on both sides, and the Adapter LSM
PM exit is triggered from both sides (coordinated via sideband messages between Adapters as
outlined in the FDI PM flow). For PCIe or Streaming protocol scenarios, this also transitions the
Protocol Layer to Active state on FDI.

4\. For CXL protocol, this step is followed by ALMP exchanges to bring the required protocol to Active
state and then protocol Flit transfer can begin.

## 3.7 CRC Computation

The CRC generator polynomial is $\left( x + 1 \right) ^ { * } \left( x ^ { 1 5 } + x + 1 \right) = x ^ { 1 6 } + x ^ { 1 5 } + x ^ { 2 } + 1 .$ This gives a 3-bit
detection guarantee for random bit errors: 2 bit detection guarantee is because of the primitive
polynomial $\left( x ^ { 1 5 } + x + 1 \right) ,$ and 1 additional bit error detection guarantee is provided by making it odd
parity because of the (x+1) term in the polynomial.

The CRC is always computed over 128 bytes of the message. For smaller messages, the message is
zero extended in the MSB. Any bytes which are part of the 128B CRC message but are not
transmitted over the Link are assigned to 0b. Whenever non-CRC bytes of the Flit populated by the
Adapter are included for CRC computation (e.g., the Flit Header or DLP bytes), CRC is computed after
the Adapter has assigned those bytes the values that will be sent over the UCIe Link. Any reserved
bits which are part of the Flit are assigned 0b for the purpose of CRC computation.

The initial value of CRC bits for CRC LFSR computation is 0000h. The CRC calculation starts with bit 0
of byte 0 of the message, and proceeds from bit 0 to bit 7 of each byte as shown in Figure 3-29. In
the figure, C[15] is bit 7 of CRC Byte 1, C[14] is bit 6 of CRC Byte 1 and so on; C[7] is bit 7 of CRC
Byte 0, C[6] is bit 6 of CRC Byte 0 and so on.

The Verilog code for CRC code generation is provided in crc_gen.vs (attached to the PDF copy of this
Specification). This Verilog code must be used as the golden reference for implementing the CRC
during encode or decode. The code is provided for the Transmit side. It takes 1024 bits (bit 1023 is bit
7 of message Byte 127, 1022 is bit 6 of message Byte 127 and so on; bit 1015 is bit 7 of message
Byte 126 and so on until bit 0 is bit 0 of message Byte 0) as an input message and outputs 16 bits of
CRC. On the Receiver, the CRC is computed using the received Flit bytes with appropriate zero
padding in the MSB to form a 128B message. If the received CRC does not match the computed CRC,
the flit is declared Invalid and a replay must be requested.

<figure>
<figcaption>Figure 3-29. Diagram of CRC Calculation</figcaption>

Message Byte 127

Message Byte 1

Message Byte 0

76543210

Bit order

Byte Order

\+

\+

\+

$C \left[ 0 \right]$

c[1]

C[2]

C[3]

C[4]

C[5]

C[6]

C[7]

C[8]

C[9]

C[10]

C[11]

C[12]

C[13]

C[14]

C[15]

</figure>

## 3.8 Retry Rules

For configurations where the raw BER is higher than 1e-27, Retry must be supported in the Adapter,
unless the only format of operation is Raw Format. If Retry is not supported by the Adapter, Link
speeds where the raw BER is higher than 1e-27 must NOT be advertised by the Physical Layer during
Link Training, unless the format of operation is Raw Format. See Table 5-32 for the raw BER
characteristics of different configurations. Once Retry has been negotiated during Part 2 of Stage 3 of
Link Initialization described in Section 3.2.1.2, it cannot be disabled even if Link speed degrades
during runtime. Retry can only be re-negotiated at the next Link Initialization (i.e., RDI moves to
Reset). For multiple stacks with a common Adapter, the Tx Retry buffer is shared between the stacks.

The Retry scheme on UCIe is a simplified version of the Retry mechanism for Flit Mode defined in PCIe
Base Specification. The rules that differ from PCIe are as follows:

· Selective Nak and associated rules are not applicable and must not be implemented. Rx Retry
Buffer-related rules are also not applicable and must not be implemented.

· Throughout the duration of Link operation, when not conflicting with PCIe rules of replay, Explicit
Sequence number Flits and Ack/Nak Flits alternate. This allows for faster Ack turnaround and thus
smaller Retry buffer sizes. It is permitted to send consecutive Explicit Sequence number Flits if
there are no pending Ack/Nak Flits to send (see also the Implementation Note below). To meet
this requirement, all Explicit Sequence Number Flit transmissions described by the PCIe rules of
replay that require the condition "CONSECUTIVE_TX_EXPLICIT_SEQ_NUM_FLIT < 3" to be met
require "CONSECUTIVE_TX_EXPLICIT_SEQ_NUM_FLIT < 1" to be met instead, and it is not
required to send three consecutive Flits with Explicit Sequence Number.

· All 10-bit retry related counters are replaced with 8-bit counters, and the maximum-permitted
sequence number is 255 (hence 1023 in all calculations is replaced with 255 and any variables
defined in the "Flit Sequence Number and Retry Mechanism" section of PCIe Base Specification
which had an initial value of 1023 instead have an initial value of 255).

· REPLAY_TIMEOUT_FLIT_COUNT is a 9-bit counter that saturates at 1FFh.

\- In addition to incrementing REPLAY_TIMEOUT_FLIT_COUNT as described in PCIe Base
Specification, the count must also be incremented when in Active state and a Flit Time
(Number of Adapter clock cycles (lclk) that are required to transfer 256B of data at the
current Link speed and width) has elapsed since the last flit was sent and neither a Payload
Flit nor a NOP flit was transmitted. The counter must be incremented for every Flit Time in
which a flit was not sent (this could lead to it being incremented several times in-between flits
or prior to the limit being met). The added requirement compensates for the noncontinuous
transfer of NOP flits. For 68B Flit Format, data transfers are also in 256B granularity (including
the PDS bytes), and thus this counter increments every time 256B of data are transmitted,
OR during idle conditions in Active state, it must be incremented according to the time that is
required to transfer 256B of data at the current Link speed and width.

\- Replay Schedule Rule 0 of PCIe Base Specification must check for
REPLAY_TIMEOUT_FLIT_COUNT ≥ 375. Replay Timer Timeout error is logged in the
Correctable Internal Error in the Adapter for UCIe.

. For the FLIT_REPLAY_NUM counter, it is strongly recommended to follow the rules provided in
PCIe Base Specification for speeds ≤ 32.0 GT/s. This counter tracks the number of times that a
Replay has occurred without making forward progress. Given the significantly lower probability of
Replay for UCIe Links, the rules associated with ≤ 32.0 GT/s PCIe speeds are sufficient for UCIe.

· NAK_WITHDRAWAL_ALLOWED is always cleared to 0. Note that this requires implementations to
set the flag NAK_SCHEDULED=1 in the "Nak Schedule 0" set of rules.

. IDLE Flit Handshake Phase is not applicable. This is because the transition to Link Active
(equivalent to LTSSM being in L0 for PCIe) is managed via handshakes on sideband, and there is
no requirement for IDLE Flits to be exchanged. As per PCIe rules, any Flits received with all 0s in

the Flit Header bytes are discarded by the Adapter. Any variables that are initialized during the
IDLE Flit Handshake Phase in PCIe Base Specification are initialized to the corresponding value
whenever the RDI is in Reset state or Retrain state. Similarly, PCIe rules that indicate relation to
"last entry to IDLE Flit Handshake Phase" would instead apply for UCIe to "last exit from Reset or
Retrain state on RDI".

· Variables applicable to Flit Sequence number and Retry mechanism that are initialized during
DL_Inactive, as with PCIe, would be initialized to their corresponding values when RDI is in Reset
state for UCIe.

· Sequence Number Handshake Phase must be performed as part of every FDI Active Entry
Handshake (see Section 10.2.8). Sequence Number Handshake Phase timeout and exit to Link
Retrain is 128 Flits transmitted without exiting Sequence Number Handshake Phase. As with PCIe,
both NOP flits or Payload flits are permitted to be used to complete the Sequence Number
Handshake Phase. If there are no Payload flits to send, the Adapter must generate NOP flits to
complete the Sequence Number Handshake Phase.

· The variable "Prior Flit was Payload" is always set to 1. This bit does not exist in the Flit Header,
and thus from the Retry perspective, implementations must assume that it is always set to 1.

· MAX_UNACKNOWLEDGED_FLITS is set to the lesser of:

\- Number of Flits that can be stored in the Tx Retry Buffer, or

\- 127

. Flit Discard 2 rule from PCIe does not result in a Data Link Protocol Error condition in UCIe.
Receiving an invalid Flit Sequence number in a received Ack or Nak flit (see the corresponding
conditions in PCIe Base Specification with the adjusted variable widths and values) OR a Payload
Flit with an Explicit Sequence number of 0 results in an Uncorrectable Internal Error in UCIe
(instead of a Data Link Protocol Error).

· Conditions from the "Flit Sequence Number and Retry Mechanism" section in PCIe Base
Specification that led to Recovery for the Port must result in the Adapter initiating Retrain on the
RDI for UCIe.

### IMPLEMENTATION NOTE

In UCIe, to encourage power savings through dynamic clock gating, it is not required
to continuously transmit NOP flits during periods in which there are no Payload flits or
any Ack/Nak pending. Consider an example in which an Adapter's Tx Retry Buffer is
empty and it transmitted a NOP flit with an Ack as the last flit before it stopped
sending additional flits to the Physical Layer. Let's say this flit had a CRC error and
hence the remote Link partner never receives this Ack. Moreover, because the remote
Link partner received a flit with a CRC error, it would transmit a Nak to original
sender. If the Ack is never re-sent and the remote Link partner has a corresponding
Payload flit in its Tx Retry Buffer, eventually a Replay Timeout will trigger from the
remote Link partner and resolve this scenario. However, rather than always relying on
Replay Timeout for these kind of scenarios, it is recommended for implementations to
ensure they have transmitted at least two flits with an Ack (these need not be
consecutive Ack flits) before stopping flit transfer whenever a Nak is received and the
transmitter has completed all the requirements of received Nak processing, including
any Replay related transfers. If no new Payload Flits were received from the remote
Link partner, as per PCIe rules, it is permitted to re-send the last transmitted Ack on
a NOP flit as well to meet this condition.

# 3.9 Runtime Link Testing using Parity

UCIe defines a mechanism to detect Link health during runtime by periodically injecting parity bytes
in the middle of the data stream when this mechanism is enabled. The receiver checks and logs parity
errors for the inserted parity bytes.

When this mechanism is enabled, the Adapter inserts 64\*N Bytes every 256\*256*N Bytes of data,
where N is obtained from the Error and Link Testing Control register (Field name: Number of 64 Byte
Inserts). Software must set N=4 when this feature is enabled during regular Link operation for UCIe
Flit mode because that makes the parity bytes also a multiple of 256B and is more consistent with the
granularity of data transfer. Only bit 0 of the inserted byte has the parity information which is
computed as follows:

ParityByte X, bit 0 = ^((DataByte [X]) ^ (DataByte [X + 64\*N]) ^(DataByte [X +
128\*N])^ .... ^(DataByte [X + (256\*256\*N - 64*N)]))

The remaining 7 bits of the inserted byte are Reserved.

The Transmitter and Receiver in the Adapter must independently keep track of the number of data
bytes elapsed to compute or check the parity information. All data bytes transmitted on the UCIe Link
(excluding the parity bytes themselves) are included for parity computation and count tracking (this
includes NOP Flits, and for 68B Flit Format, it includes the PDS Flit Header and associated zero
padding). If the RDI state moves away from Active state, the data count and parity is reset, and both
sides must renegotiate the enabling of the Parity insertion before next entry to Active from Retrain (if
the mechanism is still enabled in the Error and Link Testing Control register). When entering Active
state with Parity insertion enabled, the number of data bytes elapsed begins counting from 0. On the
transmitter, following the insertion of the parity information, the counter for the number of bytes
elapsed to compute the parity information is reset. On the Receiver, following the receipt and check of
parity bytes, the counter for the number of bytes elapsed to check the parity information is reset.

Parity insertion is independently enabled per direction of data transmission. For each direction of data
transmission, this mechanism is enabled by Software writing 1 to the "Runtime Link Testing Tx
Enable" bit in the "Error and Link Testing Control" register located in the transmitting Adapter (see
Section 9.5.3.9 for register details) and the "Runtime Link Testing Rx Enable" bit in the "Error and
Link Testing Control" register in the receiving Adapter. Parity insertion can be enabled in one direction
only, or simultaneously in both directions. Software must trigger UCIe Link Retrain after changing the
value of the corresponding enable bits on both adapters for the change to take effect. Support for this
feature in Raw Format is beyond the scope of this specification and is implementation-dependent. The
Adapters exchange sideband messages while the Adapter LSMs are in Retrain or L1 to ensure that the
remote Link partner's receiver is prepared to receive the extra parity bytes in the data stream once
the states transition to Active. For Active to Retrain transition, the Adapter that initiates the
{ParityFeature.Req} sideband message must not request Retrain exit to local RDI until a response for
this request has been received from the remote Link partner. For L1 exit, the Adapter that initiates the
{ParityFeature.Req} sideband message must not request L1 exit on the RDI until a response for this
request has been received from the remote Link partner. If an Adapter is only responding to the
{ParityFeature.Req} sideband message (i.e., only "Runtime Link Testing Rx Enable" is set to 1), the
Adapter must not delay the L1 exit or Retrain exit transitions on the RDI. It is permitted to enable
parity insertion during Initial Link bring up, by using sideband to access the remote Link partner's
registers or by other implementation-specific means; however software must trigger Link Retrain for
the feature to take effect. Software is permitted to disable L1 before enabling Runtime Link Testing
Parity.

Adapter sends a {ParityFeature.Req} sideband message to remote Link Partner if its Transmitter is
enabled to send parity bytes ("Runtime Link Testing Tx Enable" bit in Section 9.5.3.9). Remote
Adapter responds with a {ParityFeature.Ack} sideband message if its receiver is enabled and ready to
accept parity bytes ("Runtime Link Testing Rx Enable" bit in Section 9.5.3.9). Figure 3-30 shows an

example of a successful negotiation. If Die 0 Adapter Transmitter is enabled to insert parity bytes, it
must send a {ParityFeature.Req} sideband message from Die 0 to Die 1.

Adapter responds with a {ParityFeature.Nak} sideband message if the Adapter is not ready to accept
parity bytes, or if the feature has not been enabled for it yet. The requesting Adapter must log the
Nak in a status register so that Software can determine that a Nak had occurred. Figure 3-31 shows
an example of an unsuccessful negotiation. A timeout for this explicit Ack/Nak handshake must be
reported in the Header Log 2 register as Adapter Timeout encoding 0001b to indicate that the
parameter exchange flow timed out.

Note:
The Adapters are permitted to transition to a higher latency data path if the Parity
Feature is enabled. The explicit Ack/Nak handshake is provided to ensure both sides
have sufficient time to transition to alternate data path for this mechanism.

The Parity bytes do not consume Retimer receiver buffer credits. The Retimer receiver must not
write the Parity bytes into its receiver buffer or forward these to remote Retimer partner over the Off
Package Interconnect. This mechanism is to help characterize local UCIe Links only.

Parity insertion is disabled in a given direction by programming either "Runtime Link Testing Tx
Enable" in the transmitting Adapter or "Runtime Link Testing Rx Enable" in the receiving Adapter to 0
and then retraining the Link using the Retrain bit in the UCIe Link Control register.

<figure>
<figcaption>Figure 3-30. Successful Parity Feature negotiation between Die 1 Tx and Die 0 Rx</figcaption>

Adapter
Die 0

Physical layer
$D i e \quad 0$

CHANNEL

Physical layer
Die 1

Adapter
Die 1

Adapter LSMs and RDI is in Retrain

SB MSG {ParityFeature.Req}

Die 0 sends
{ParityFeature.Ack} in
response to accept the
request from Die 1. It's
Rx must be ready to
receive the extra
parity bytes before the
response is sent.

Die 1 sends
{ParityFeature.Req} if
it wants to enable
Parity insertion on its
Tx

SB MSG {ParityFeature.Ack}

RDI Active Entry Handshake followed by Adapter LSM Active Entry Handshake

</figure>

<figure>
<figcaption>Figure 3-31. Unsuccessful Parity Feature negotiation between Die 1 Tx and Die 0 Rx</figcaption>

Adapter
Die 0

$\begin{array}{} { \text { Physical layer } } \\ { \text { Die } 0 } \end{array}$

CHANNEL

Physical layer
Die 1

Adapter
Die 1

Adapter LSMs and RDI is in Retrain

SB MSG {ParityFeature.Req}

Die 1 sends
{ParityFeature.Req} if
it wants to enable
Parity insertion on its
Tx

$D i e \quad 0 \quad s e n d s$
{ParityFeature.Nak} in
response to reject the
request from Die 1.

SB MSG {ParityFeature.Nak}

RDI Active Entry Handshake followed by Adapter LSM Active Entry Handshake

</figure>

If a parity error is detected by a chiplet, the error is treated as a Correctable error and reported via
the correctable error reporting mechanism. By enabling interrupt on correctable errors, SW can
implement a BER counter in SW, if so desired.

When a Pause Data Stream occurs the Pause Data Stream and corresponding padding bytes are
included in the number of bytes elapsed before parity injection as well as parity computation.

# 4.0 Logical Physical Layer

The Logical PHY comprehends the following functions:

· Link initialization, training and power management states

· Byte to Lane mapping for data transmission over Lanes

· Interconnect redundancy remapping (when required)

· Transmitting and receiving sideband messages

· Scrambling and training pattern generation

· Lane reversal

· Width degradation (when applicable)

## 4.1 Data and Sideband Transmission Flow

This specification defines clock, valid and Data to send and receive data over the physical Lanes. The
transmitted data is framed by the valid signal.

### 4.1.1 Byte to Lane Mapping

Data packets are transmitted in Bytes. Within each Byte, bit [0] is transmitted first. Figure 4-1 shows
an example of bit arrangement within one byte transmission over Lane 0.

<figure>
<figcaption>Figure 4-1. Bit arrangement within a byte transfer</figcaption>

Clock

Valid

Data

B0[0]

B0[1]

B0[2]

B0[3]

B0[4]

B0[5]

B0[6]

B0[7]

8 UI

</figure>

Each Byte is transmitted on a separate Lane. Byte 0 (B0) is transmitted on Lane 0, Byte 1 is
transmitted on Lane 1 and so on.

Figure 4-2 shows an example of a 256B Flit transmitted over a x64 interface (one x64 Advanced
Package module or two x32 Advanced Package modules or four Standard Package modules). If the I/
O width changes to x32 or x16 interface (Standard Package), transmission of one Byte per Lane is
preserved as shown in Figure 4-3 and Figure 4-4 respectively.

Figure 4-5 shows an example for a width degraded Standard Package module.

<table>
<caption>Figure 4-2. Byte map for x64 interface</caption>
<tr>
<th>LANE $U I$</th>
<th>0</th>
<th>1</th>
<th>2</th>
<th>3</th>
<th>4</th>
<th>5</th>
<th>6</th>
<th>7</th>
<th>...</th>
<th>48</th>
<th>49</th>
<th>50</th>
<th>51</th>
<th>52</th>
<th>53</th>
<th>54</th>
<th>55</th>
<th>56</th>
<th>57</th>
<th>58</th>
<th>59</th>
<th>60</th>
<th>61</th>
<th>62</th>
<th>63</th>
<th></th>
</tr>
<tr>
<td>0 - 7</td>
<td>B00</td>
<td>B01</td>
<td>B02</td>
<td>B03</td>
<td>B04</td>
<td>B05</td>
<td>B06</td>
<td>B07</td>
<td>...</td>
<td>B48</td>
<td>B49</td>
<td>B50</td>
<td>B51</td>
<td>B52</td>
<td>B53</td>
<td>B54</td>
<td>B55</td>
<td>B56</td>
<td>B57</td>
<td>B58</td>
<td>B59</td>
<td>B60</td>
<td>B61</td>
<td>B62</td>
<td>B63</td>
<td></td>
</tr>
<tr>
<td>8 - 15</td>
<td>B64</td>
<td>B65</td>
<td>B66</td>
<td>B67</td>
<td>B68</td>
<td>B69</td>
<td>B70</td>
<td>B71</td>
<td>...</td>
<td>B112</td>
<td>B113</td>
<td>B114</td>
<td>B115</td>
<td>B116</td>
<td>B117</td>
<td>B118</td>
<td>B119</td>
<td>B120</td>
<td>B121</td>
<td>B122</td>
<td>B123</td>
<td>B124</td>
<td>B125</td>
<td>B126</td>
<td>B127</td>
<td></td>
</tr>
<tr>
<td>$1 6 \quad - \quad 2 3$</td>
<td>B128</td>
<td>B129</td>
<td>B130</td>
<td>B131</td>
<td>B132</td>
<td>B133</td>
<td>B134</td>
<td>B135</td>
<td></td>
<td>B176</td>
<td>B177</td>
<td>B178</td>
<td>B179</td>
<td>B180</td>
<td>B181</td>
<td>B182</td>
<td>$B 1 8 3$</td>
<td>B184</td>
<td>B185</td>
<td>B186</td>
<td>B187</td>
<td>B188</td>
<td>B189</td>
<td>B190</td>
<td>B191</td>
<td rowspan="2"></td>
</tr>
<tr>
<td>24 - 31</td>
<td>B192</td>
<td>B193</td>
<td>B194</td>
<td>B195</td>
<td>B196</td>
<td>B197</td>
<td>B198</td>
<td>B199</td>
<td>...</td>
<td>B240</td>
<td>B241</td>
<td>B242</td>
<td>B243</td>
<td>B244</td>
<td>B245</td>
<td>B246</td>
<td>B247</td>
<td>B248</td>
<td>B249</td>
<td>B250</td>
<td>B251</td>
<td>B252</td>
<td>B253</td>
<td>B254</td>
<td>B255</td>
</tr>
</table>

<table>
<caption>Figure 4-3. Byte map for x32 interface</caption>
<tr>
<th>Lane $U I$</th>
<th>0</th>
<th>1</th>
<th>2</th>
<th>3</th>
<th>4</th>
<th>5</th>
<th>6</th>
<th>7</th>
<th>...</th>
<th>16</th>
<th>17</th>
<th>18</th>
<th>19</th>
<th>20</th>
<th>21</th>
<th>22</th>
<th>23</th>
<th>24</th>
<th>25</th>
<th>26</th>
<th>27</th>
<th>28</th>
<th>29</th>
<th>30</th>
<th>31</th>
</tr>
<tr>
<td>0 -7</td>
<td>BO</td>
<td>B1</td>
<td>B2</td>
<td>B3</td>
<td>B4</td>
<td>B5</td>
<td>B6</td>
<td>B7</td>
<td></td>
<td>B16</td>
<td>B17</td>
<td>B18</td>
<td>B19</td>
<td>B20</td>
<td>B21</td>
<td>B22</td>
<td>B23</td>
<td>B24</td>
<td>B25</td>
<td>B26</td>
<td>B27</td>
<td>B28</td>
<td>B29</td>
<td>B30</td>
<td>B31</td>
</tr>
<tr>
<td>8 - 15</td>
<td>832</td>
<td>833</td>
<td>834</td>
<td>835</td>
<td>B36</td>
<td>837</td>
<td>B38</td>
<td>B39</td>
<td></td>
<td>B48</td>
<td>849</td>
<td>850</td>
<td>B51</td>
<td>B52</td>
<td>853</td>
<td>B54</td>
<td>855</td>
<td>856</td>
<td>857</td>
<td>858</td>
<td>859</td>
<td>B60</td>
<td>861</td>
<td>B62</td>
<td>B63</td>
</tr>
<tr>
<td>16 - 23</td>
<td>864</td>
<td>865</td>
<td>866</td>
<td>867</td>
<td>B68</td>
<td>869</td>
<td>B70</td>
<td>B71</td>
<td></td>
<td>B80</td>
<td>B81</td>
<td>B82</td>
<td>683</td>
<td>684</td>
<td>885</td>
<td>686</td>
<td>887</td>
<td>B88</td>
<td>B89</td>
<td>890</td>
<td>891</td>
<td>892</td>
<td>893</td>
<td>B94</td>
<td>B95</td>
</tr>
<tr>
<td>24- 31</td>
<td>896</td>
<td>897</td>
<td>898</td>
<td>899</td>
<td>B100</td>
<td>8101</td>
<td>B102</td>
<td>B103</td>
<td></td>
<td>B112</td>
<td>8113</td>
<td>8114</td>
<td>8115</td>
<td>8116</td>
<td>8117</td>
<td>B118</td>
<td>8119</td>
<td>B120</td>
<td>B121</td>
<td>B122</td>
<td>B123</td>
<td>B124</td>
<td>B125</td>
<td>B126</td>
<td>B127</td>
</tr>
<tr>
<td>32-39</td>
<td>8128</td>
<td>8129</td>
<td>8130</td>
<td>B131</td>
<td>B132</td>
<td>8133</td>
<td>B134</td>
<td>B135</td>
<td></td>
<td>B144</td>
<td>B145</td>
<td>B146</td>
<td>B147</td>
<td>8148</td>
<td>8149</td>
<td>B150</td>
<td>8151</td>
<td>B152</td>
<td>B153</td>
<td>B154</td>
<td>BISS</td>
<td>B156</td>
<td>B157</td>
<td>B158</td>
<td>B159</td>
</tr>
<tr>
<td>40 - 47</td>
<td>8160</td>
<td>8161</td>
<td>8162</td>
<td>8163</td>
<td>B164</td>
<td>8165</td>
<td>8166</td>
<td>B167</td>
<td></td>
<td>B176</td>
<td>8177</td>
<td>8178</td>
<td>B179</td>
<td>8180</td>
<td>8181</td>
<td>B182</td>
<td>8183</td>
<td>B184</td>
<td>B185</td>
<td>B186</td>
<td>B187</td>
<td>B188</td>
<td>B189</td>
<td>B190</td>
<td>B191</td>
</tr>
<tr>
<td>$4 8 - \quad 5 5$</td>
<td>8192</td>
<td>8193</td>
<td>B194</td>
<td>B195</td>
<td>B196</td>
<td>8197</td>
<td>8198</td>
<td>B199</td>
<td></td>
<td>B208</td>
<td>8209</td>
<td>B210</td>
<td>B211</td>
<td>6212</td>
<td>8213</td>
<td>B214</td>
<td>8215</td>
<td>B216</td>
<td>B217</td>
<td>B218</td>
<td>B219</td>
<td>B220</td>
<td>B221</td>
<td>B222</td>
<td>B223</td>
</tr>
<tr>
<td>$5 6 \quad - 6 3$</td>
<td>B224</td>
<td>B225</td>
<td>B226</td>
<td>B227</td>
<td>B228</td>
<td>B229</td>
<td>B230</td>
<td>B231</td>
<td></td>
<td>B240</td>
<td>B241</td>
<td>B242</td>
<td>B243</td>
<td>6244</td>
<td>B245</td>
<td>B246</td>
<td>B247</td>
<td>B248</td>
<td>B249</td>
<td>B250</td>
<td>8251</td>
<td>B252</td>
<td>B253</td>
<td>B254</td>
<td>B255</td>
</tr>
</table>

<table>
<caption>Figure 4-4. Byte map for x16 interface</caption>
<tr>
<th>Lane UI</th>
<th>0</th>
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
</tr>
<tr>
<td>0 - 7</td>
<td>BO</td>
<td>B1</td>
<td>B2</td>
<td>B3</td>
<td>B4</td>
<td>B5</td>
<td>B6</td>
<td>B7</td>
<td>B8</td>
<td>B9</td>
<td>B10</td>
<td>B11</td>
<td>B12</td>
<td>B13</td>
<td>B14</td>
<td>B15</td>
</tr>
<tr>
<td>8 - 15</td>
<td>B16</td>
<td>B17</td>
<td>B18</td>
<td>B19</td>
<td>B20</td>
<td>B21</td>
<td>B22</td>
<td>B23</td>
<td>B24</td>
<td>B25</td>
<td>B26</td>
<td>B27</td>
<td>B28</td>
<td>B29</td>
<td>B30</td>
<td>B31</td>
</tr>
<tr>
<td>16 - 23</td>
<td>B32</td>
<td>B33</td>
<td>B34</td>
<td>B35</td>
<td>B36</td>
<td>B37</td>
<td>B38</td>
<td>B39</td>
<td>B40</td>
<td>B41</td>
<td>B42</td>
<td>B43</td>
<td>B44</td>
<td>B45</td>
<td>B46</td>
<td>B47</td>
</tr>
<tr>
<td>24 - 31</td>
<td>B48</td>
<td>B49</td>
<td>B50</td>
<td>B51</td>
<td>B52</td>
<td>B53</td>
<td>B54</td>
<td>B55</td>
<td>B56</td>
<td>B57</td>
<td>B58</td>
<td>B59</td>
<td>B60</td>
<td>B61</td>
<td>B62</td>
<td>B63</td>
</tr>
<tr>
<td>32 - 39</td>
<td>B64</td>
<td>B65</td>
<td>B66</td>
<td>B67</td>
<td>B68</td>
<td>B69</td>
<td>B70</td>
<td>B71</td>
<td>B72</td>
<td>B73</td>
<td>B74</td>
<td>B75</td>
<td>B76</td>
<td>B77</td>
<td>B78</td>
<td>B79</td>
</tr>
<tr>
<td>40 - 47</td>
<td>B80</td>
<td>B81</td>
<td>B82</td>
<td>B83</td>
<td>B84</td>
<td>B85</td>
<td>B86</td>
<td>B87</td>
<td>B88</td>
<td>B89</td>
<td>B90</td>
<td>B91</td>
<td>B92</td>
<td>B93</td>
<td>B94</td>
<td>B95</td>
</tr>
<tr>
<td>48 - 55</td>
<td>B96</td>
<td>B97</td>
<td>B98</td>
<td>B99</td>
<td>B100</td>
<td>B101</td>
<td>B102</td>
<td>B103</td>
<td>B104</td>
<td>B105</td>
<td>B106</td>
<td>B107</td>
<td>B108</td>
<td>B109</td>
<td>B110</td>
<td>B111</td>
</tr>
<tr>
<td>56 - 63</td>
<td>B112</td>
<td>B113</td>
<td>B114</td>
<td>B115</td>
<td>B116</td>
<td>B117</td>
<td>B118</td>
<td>B119</td>
<td>B120</td>
<td>B121</td>
<td>B122</td>
<td>B123</td>
<td>B124</td>
<td>B125</td>
<td>B126</td>
<td>B127</td>
</tr>
<tr>
<td>64 - 71</td>
<td>B128</td>
<td>B129</td>
<td>B130</td>
<td>B131</td>
<td>B132</td>
<td>B133</td>
<td>B134</td>
<td>B135</td>
<td>B136</td>
<td>B137</td>
<td>B138</td>
<td>B139</td>
<td>B140</td>
<td>B141</td>
<td>B142</td>
<td>B143</td>
</tr>
<tr>
<td>72 - 79</td>
<td>B144</td>
<td>B145</td>
<td>B146</td>
<td>B147</td>
<td>B148</td>
<td>B149</td>
<td>B150</td>
<td>B151</td>
<td>B152</td>
<td>B153</td>
<td>B154</td>
<td>B155</td>
<td>B156</td>
<td>B157</td>
<td>B158</td>
<td>B159</td>
</tr>
<tr>
<td>80 - 87</td>
<td>B160</td>
<td></td>
<td></td>
<td>B163</td>
<td>B164</td>
<td>B165</td>
<td>B166</td>
<td>B167</td>
<td>B168</td>
<td>B169</td>
<td>B170</td>
<td>B171</td>
<td>B172</td>
<td>B173</td>
<td>B174</td>
<td>B175</td>
</tr>
<tr>
<td>88 - 95</td>
<td>B176</td>
<td>$\frac { B 1 6 1 } { B 1 7 7 } | \begin{array}{} { B 1 6 2 } \\ { B 1 7 8 } \end{array}$</td>
<td></td>
<td>B179</td>
<td>B180</td>
<td>B181</td>
<td>B182</td>
<td>B183</td>
<td>B184</td>
<td>B185</td>
<td>B186</td>
<td>B187</td>
<td>B188</td>
<td>B189</td>
<td>B190</td>
<td>B191</td>
</tr>
<tr>
<td>96 - 103</td>
<td>B192</td>
<td>B193</td>
<td>B194</td>
<td>B195</td>
<td>B196</td>
<td>B197</td>
<td>B198</td>
<td>B199</td>
<td>B200</td>
<td>B201</td>
<td>B202</td>
<td>B203</td>
<td>B204</td>
<td>B205</td>
<td>B206</td>
<td>B207</td>
</tr>
<tr>
<td>104 - 111</td>
<td>B208</td>
<td>B209</td>
<td>B210</td>
<td>B211</td>
<td>B212</td>
<td>B213</td>
<td>B214</td>
<td>B215</td>
<td>B216</td>
<td>B217</td>
<td>B218</td>
<td></td>
<td>B220</td>
<td>B221</td>
<td>B222</td>
<td>B223</td>
</tr>
<tr>
<td>$1 1 2 \quad - \quad 1 1 9$</td>
<td>B224</td>
<td>B225</td>
<td>B226</td>
<td>B227</td>
<td>B228</td>
<td>B229</td>
<td>B230</td>
<td>B231</td>
<td>B232</td>
<td>B233</td>
<td>B234</td>
<td>$\frac { B 2 1 9 } { B 2 3 5 }$</td>
<td>B236</td>
<td>B237</td>
<td>B238</td>
<td>B239</td>
</tr>
<tr>
<td>$1 2 0 \quad - \quad 1 2 7$</td>
<td>B240</td>
<td>B241</td>
<td>B242</td>
<td>B243</td>
<td>B244</td>
<td>B245</td>
<td>B246</td>
<td>B247</td>
<td>B248</td>
<td>B249</td>
<td>B250</td>
<td>B251</td>
<td>B252</td>
<td>B253</td>
<td>B254</td>
<td>B255</td>
</tr>
</table>

<table>
<caption>Figure 4-5. Byte to Lane mapping for Standard package x16 degraded to x8</caption>
<tr>
<th>Lane</th>
<th>8</th>
<th>9</th>
<th>10</th>
<th>11</th>
<th>12</th>
<th>13</th>
<th>14</th>
<th>15</th>
</tr>
<tr>
<th></th>
<th colspan="8">or</th>
</tr>
<tr>
<td>Lane Uİ</td>
<td>0</td>
<td>1</td>
<td>2</td>
<td>3</td>
<td>4</td>
<td>5</td>
<td>6</td>
<td>7</td>
</tr>
<tr>
<td>0 - 7</td>
<td>BO</td>
<td>B1</td>
<td>B2</td>
<td>B3</td>
<td>B4</td>
<td>B5</td>
<td>B6</td>
<td>B7</td>
</tr>
<tr>
<td>8 - 15</td>
<td>B8</td>
<td>B9</td>
<td>B10</td>
<td>B11</td>
<td>B12</td>
<td>B13</td>
<td>B14</td>
<td>B15</td>
</tr>
<tr>
<td>$1 6 - 2 3$</td>
<td>B16</td>
<td>B17</td>
<td>B18</td>
<td>B19</td>
<td>B20</td>
<td>B21</td>
<td>B22</td>
<td>B23</td>
</tr>
<tr>
<td>$2 4 - 3 1$</td>
<td>B24</td>
<td>B25</td>
<td>B26</td>
<td>B27</td>
<td>B28</td>
<td>B29</td>
<td>B30</td>
<td>B31</td>
</tr>
<tr>
<td>$3 2 \quad - 3 9$</td>
<td>B32</td>
<td>B33</td>
<td>B34</td>
<td>B35</td>
<td>B36</td>
<td>B37</td>
<td>B38</td>
<td>B39</td>
</tr>
<tr>
<td>$4 0 - 4 7$</td>
<td>B40</td>
<td>B41</td>
<td>B42</td>
<td>B43</td>
<td>B44</td>
<td>B45</td>
<td>B46</td>
<td>B47</td>
</tr>
<tr>
<td>$4 8 \quad - \quad 5 5$</td>
<td>B48</td>
<td>B49</td>
<td>B50</td>
<td>B51</td>
<td>B52</td>
<td>B53</td>
<td>B54</td>
<td>B55</td>
</tr>
<tr>
<td>$5 6 \quad - \quad 6 3$</td>
<td>B56</td>
<td>B57</td>
<td>B58</td>
<td>B59</td>
<td>B60</td>
<td>B61</td>
<td>B62</td>
<td>B63</td>
</tr>
<tr>
<td>$6 4 \quad - \quad 7 1$</td>
<td>B64</td>
<td>B65</td>
<td>B66</td>
<td>B67</td>
<td>B68</td>
<td>B69</td>
<td>B70</td>
<td>B71</td>
</tr>
<tr>
<td>$7 2 \quad - \quad 7 9$</td>
<td>B72</td>
<td>B73</td>
<td>B74</td>
<td>B75</td>
<td>B76</td>
<td>B77</td>
<td>B78</td>
<td>B79</td>
</tr>
<tr>
<td>80- 87</td>
<td>B80</td>
<td>B81</td>
<td>B82</td>
<td>B83</td>
<td>B84</td>
<td>B85</td>
<td>B86</td>
<td>B87</td>
</tr>
<tr>
<td>$8 8 \quad - \quad 9 5$</td>
<td>B88</td>
<td>B89</td>
<td>890</td>
<td>B91</td>
<td>B92</td>
<td>B93</td>
<td>B94</td>
<td>B95</td>
</tr>
<tr>
<td>$9 6 - 1 0 3$</td>
<td>B96</td>
<td>B97</td>
<td>B98</td>
<td>B99</td>
<td>B100</td>
<td>B101</td>
<td>B102</td>
<td>B103</td>
</tr>
<tr>
<td>$1 0 4 \quad - \quad 1 1 1$</td>
<td>B104</td>
<td>B105</td>
<td>B106</td>
<td>B107</td>
<td>B108</td>
<td>B109</td>
<td>B110</td>
<td>B111</td>
</tr>
<tr>
<td>112 - 119</td>
<td>B112</td>
<td>B113</td>
<td>B114</td>
<td>B115</td>
<td>B116</td>
<td>B117</td>
<td>B118</td>
<td>B119</td>
</tr>
<tr>
<td>120 - 127</td>
<td>B120</td>
<td>B121</td>
<td>B122</td>
<td>B123</td>
<td>B124</td>
<td>B125</td>
<td>B126</td>
<td>B127</td>
</tr>
<tr>
<td>128-135</td>
<td>B128</td>
<td>B129</td>
<td>B130</td>
<td>B131</td>
<td>B132</td>
<td>B133</td>
<td>B134</td>
<td>B135</td>
</tr>
<tr>
<td>136-143</td>
<td>B136</td>
<td>$\frac { B 1 3 7 } { 8 1 1 5 }$</td>
<td>B138</td>
<td></td>
<td>B140</td>
<td>B141</td>
<td>B142</td>
<td>B143</td>
</tr>
<tr>
<td>144-151</td>
<td>B144</td>
<td></td>
<td>B146</td>
<td>$\frac { B 1 3 9 } { B 1 1 7 }$</td>
<td>B148</td>
<td>B149</td>
<td>B150</td>
<td>B151</td>
</tr>
<tr>
<td>152-159</td>
<td>B152</td>
<td>B153</td>
<td>B154</td>
<td>B155</td>
<td>B156</td>
<td>B157</td>
<td>B158</td>
<td>B159</td>
</tr>
<tr>
<td>160-167</td>
<td>B160</td>
<td>B161</td>
<td>B162</td>
<td>B163</td>
<td>B164</td>
<td>B165</td>
<td>B166</td>
<td>B167</td>
</tr>
<tr>
<td>168-175</td>
<td>B168</td>
<td>B169</td>
<td>B170</td>
<td>B171</td>
<td>B172</td>
<td>B173</td>
<td>B174</td>
<td>B175</td>
</tr>
<tr>
<td>176-183</td>
<td>B176</td>
<td>B177</td>
<td>B178</td>
<td>B179</td>
<td>B180</td>
<td>B181</td>
<td>B182</td>
<td>B183</td>
</tr>
<tr>
<td>184-191</td>
<td>B184</td>
<td>B185</td>
<td>B186</td>
<td>B187</td>
<td>B188</td>
<td>B189</td>
<td>B190</td>
<td>B191</td>
</tr>
<tr>
<td>192-199</td>
<td>B192</td>
<td>B193</td>
<td>B194</td>
<td>B195</td>
<td>B196</td>
<td>B197</td>
<td>B198</td>
<td>B199</td>
</tr>
<tr>
<td>200-207</td>
<td>B200</td>
<td>B201</td>
<td>B202</td>
<td>B203</td>
<td>B204</td>
<td>B205</td>
<td>B206</td>
<td>B207</td>
</tr>
<tr>
<td>208-215</td>
<td>B208</td>
<td>B209</td>
<td>B210</td>
<td>B211</td>
<td>B212</td>
<td>B213</td>
<td>B214</td>
<td>B215</td>
</tr>
<tr>
<td>216-223</td>
<td>B216</td>
<td>B217</td>
<td>B218</td>
<td>B219</td>
<td>B220</td>
<td>B221</td>
<td>B222</td>
<td>B223</td>
</tr>
<tr>
<td>224-231</td>
<td>B224</td>
<td>B225</td>
<td>B226</td>
<td>B227</td>
<td>B228</td>
<td>B229</td>
<td>B230</td>
<td>B231</td>
</tr>
<tr>
<td>232-239</td>
<td>B232</td>
<td>B233</td>
<td>B234</td>
<td>B235</td>
<td>B236</td>
<td>B237</td>
<td>B238</td>
<td>B239</td>
</tr>
<tr>
<td>240-247</td>
<td>B240</td>
<td>B241</td>
<td>B242</td>
<td>B243</td>
<td>B244</td>
<td>B245</td>
<td>B246</td>
<td>B247</td>
</tr>
<tr>
<td>248-255</td>
<td>B248</td>
<td>B249</td>
<td>B250</td>
<td>B251</td>
<td>B252</td>
<td>B253</td>
<td>B254</td>
<td>B255</td>
</tr>
</table>

### 4.1.2 Valid Framing

Valid signal is used to frame the transmitted data. For each 8-bit data packet, valid is asserted for the
first 4 UI and de-asserted for 4 UI. This will allow data transfer in Raw Format or various Flit Formats
as described in Chapter 3.0 using one or multiple valid frames. An example is shown in Figure 4-6
where Transfer 1 and Transfer 2 can be from the same Flit or different Flits.

Note:
An 8-UI block assertion is enforced by the Transmitter and tracked by the Receiver
during Active state. This means that following the first valid transfer of data over
mainband in Active state, each subsequent transfer is after an integer multiple of 8 UI
from the rising edge of Valid of the first transfer. Note that for Retimers, this means
that the first transfer after entering the Active state cannot be a 'No Flit data transfer +
1 credit release' encoding; this is acceptable because the Retimer-advertised credits
are replenished or readvertised whenever the state moves away from Active.

