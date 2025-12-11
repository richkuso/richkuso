

# 8.3.5.2.8 DMH_Ext_Cap_Low - DMH Extended Capability Pointer Low (Offset 18h)

<table>
<caption>Table 8-49. DMH Extended Capability Pointer Low</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>31:2</td>
<td>$R O$</td>
<td>Lower 30 bits of the DWORD-aligned offset from the DMH starting address, where any extended capabilities start, when present in the DMH. Set to all 0s for this revision of the spec.</td>
</tr>
<tr>
<td>1:0</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

<table>
<caption>$8 . 3 . 5 . 2 . 9$ DMH_Ext_Cap_High - DMH Extended Capability Pointer High (Offset 1Ch) Table 8-50. DMH Extended Capability Pointer High</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>31:0</td>
<td>RO</td>
<td>Upper 32 bits of the DWORD-aligned offset from the DMH starting address, where any extended capabilities start, when present in the DMH. Set to all 0s for this revision of the spec.</td>
</tr>
</table>

# 8.3.5.2.10 DMS_Start_Low - DMS Starting Address Low (Offset 20h)

<table>
<caption>Table 8-51. DMS_Starting_Low</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>$3 1 : 1 2$</td>
<td>RO</td>
<td>Lower 20 bits of the 4K-aligned starting address (in the UMAP address space of the management element that hosts the DMH) of the first DMS connected to the DMH.</td>
</tr>
<tr>
<td>$1 1 : 0$</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

## 8.3.5.2.11 DMS_Start_High - DMS Starting Address High (Offset 24h)

<table>
<caption>Table 8-52. DMS_Starting_High</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>31:0</td>
<td>RO</td>
<td>Upper 32 bits of the 4K-aligned starting address (in the UMAP address space of the management element that hosts the DMH) of the first DMS connected to the DMH.</td>
</tr>
</table>

## 8.3.5.3 DMS Registers

Architected DMS registers are detailed in this section. The UCIe Consortium-assigned Vendor ID at
Offset 00h of the DMS register map uniquely identifies each UCIe Vendor. A value of 0h for the Vendor
ID indicates that the Spoke is an "empty" Spoke and the register map for such a Spoke is shown in
Figure 8-65. For Spokes with a nonzero Vendor ID (also referred to as nonempty Spokes), a 'Spoke
Type' value is defined that indicates whether the Spoke is associated with a UCIe link or if the Spoke
is vendor-defined (see Section 8.3.5.3.2.8 for 'Spoke Type' definition):

· If a Spoke is associated with a UCIe link, its 'Spoke Type' value is either 0, 1, or 2 (see
Figure 8-67 for the register map)

. If the Spoke is a vendor-defined Spoke, the 'Spoke type' value is assigned by the vendor within
the range of 128 to 255 and some of the architected registers are not applicable (see Figure 8-68
for the register map)

Figure 8-66 shows registers that are common for all Spoke types. For security, DMS registers are
classified as follows. See Section 8.1.3.5.1 for the details of each class.

· Spoke STS register falls within the 'Chiplet Status' asset class.

· When applicable, UCIe Link Status in UCIe Link DVSEC, UCIe link-related status/log registers in
the Adapter_Physical_Layer register block (e.g., Correctable/Uncorrectable Error Status),
Compliance and Test-related status registers in the Compliance_Test register block (e.g., Physical
Layer Compliance 1 and 2 Status registers), fall within the 'SiP Status' asset class.

\- All standard UCIe link registers other than the ones noted above fall within the 'SiP
Configuration' asset class.

· All other spec-defined registers in DMS fall within the 'Chiplet Configuration' asset class.

### 8.3.5.3.1 "Empty" Spoke Registers

Figure 8-65 shows the register map for "empty" Spokes. Designs can use this Spoke register
structure to indicate that the Spoke does not have any Spoke functionality.

31
Figure 8-65. Empty Spoke Register Map

<figure>

16 15

0

</figure>

<table>
<tr>
<th>Reserved</th>
<th>Spoke VID = 0hª</th>
<th>0B</th>
</tr>
<tr>
<td colspan="2">DMS_Next_Low</td>
<td>4B</td>
</tr>
<tr>
<td colspan="2">DMS_Next_High</td>
<td>8B</td>
</tr>
</table>

#### a. See Section 8.3.5.3.2.1.

##### 8.3.5.3.1.1 DMS_Next_Low - DMS Next Low Address (Offset 04h)

<table>
<caption>Table 8-53. DMS_Next_Low Address</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>31:12</td>
<td>RO</td>
<td>Lower 20 bits of the 4K-aligned starting address (in the UMAP address space of the management element that hosts the DMH) of the next DMS connected to the DMH. If this is the last Spoke in the Spoke chain, this field needs to be set to all 0s.</td>
</tr>
<tr>
<td>11:0</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

<table>
<caption>8.3.5.3.1.2 DMS_Next_High - DMS Next High Address (Offset 08h) Table 8-54. DMS_Next_High Address</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>31:0</td>
<td>RO</td>
<td>Upper 32 bits of the 4K-aligned starting address (in the UMAP address space of the management element that hosts the DMH) of the next DMS connected to the DMH. If this is the last Spoke in the Spoke chain, this field needs to be set to all 0s.</td>
</tr>
</table>

### 8.3.5.3.2 Common DMS Registers for All Non-empty Spokes

Figure 8-66 shows the registers that are present in all non-empty Spokes. Locations marked as
"Type-Specific" in Figure 8-66 carry registers that are specific to the 'Spoke Type' and are discussed in
Section 8.3.5.3.3 and Section 8.3.5.3.4.

Figure 8-66. Common DMS Registers for All Non-empty Spokes Register Map

<figure>

31

24 23

16 15

8 7

0

Spoke DevID

Spoke VID

0B

DMS_Next_Low

DMS_Next_High

48B

•

•

•

80B

•

•

•

128B

•

•

•

$N$

</figure>

<table>
<caption>8.3.5.3.2.1 Spoke VID - Spoke Vendor ID (Offset 00h) Table 8-55. Spoke Vendor ID</caption>
<tr>
<th colspan="2">Type-Specific</th>
<th>Reserved</th>
<th>Spoke RID</th>
</tr>
<tr>
<td>Associated DMS-ID2</td>
<td>Associated DMS-ID1</td>
<td>Associated DMS-ID0</td>
<td>DMS-ID</td>
</tr>
<tr>
<td colspan="4">Spoke CAP</td>
</tr>
<tr>
<td colspan="4">Spoke CTL</td>
</tr>
<tr>
<td colspan="4">Spoke STS</td>
</tr>
<tr>
<td colspan="4">DMS_Length_Low</td>
</tr>
<tr>
<td></td>
<td colspan="3">DMS_Length_High</td>
</tr>
<tr>
<td colspan="4">DMS_Ext_Cap_Low</td>
</tr>
<tr>
<td colspan="4">DMS_Ext_Cap_High</td>
</tr>
<tr>
<td colspan="4">Type-Specific</td>
</tr>
<tr>
<td colspan="4">Reserved</td>
</tr>
<tr>
<td colspan="4">Type-Specific</td>
</tr>
</table>

<table>
<caption>8.3.5.3.2.2 Spoke DevID - Spoke Device ID (Offset 02h) Table 8-56. Spoke Device ID</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>15:0</td>
<td>RO</td>
<td>Spoke Vendor ID Uniquely identifies a Spoke Vendor to Software. This ID is assigned by UCIe Consortium.</td>
</tr>
</table>

<table>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>15:0</td>
<td>RO</td>
<td>Spoke Device ID Uniquely identifies a device from the Vendor identified by the Vendor ID. This ID is assigned by the vendor.</td>
</tr>
</table>

# 8.3.5.3.2.3 DMS_Next_Low - DMS Next Low Address (Offset 04h)

<table>
<caption>Table 8-57. DMS_Next_Low Address</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>$3 1 : 1 2$</td>
<td>$R O$</td>
<td>Lower 20 bits of the 4K-aligned starting address (in the UMAP address space of the management element that hosts the DMH) of the next DMS connected to the DMH. If this is the last Spoke in the Spoke chain, this field needs to be set to all 0s.</td>
</tr>
<tr>
<td>$1 1 : 0$</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

# 8.3.5.3.2.4 DMS_Next_High - DMS Next High Address (Offset 08h)

<table>
<caption>Table 8-58. DMS_Next_High Address</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>31:0</td>
<td>RO</td>
<td>Upper 32 bits of the 4K-aligned starting address (in the UMAP address space of the management element that hosts the DMH) of the next DMS connected to the DMH. If this is the last Spoke in the Spoke chain, this field needs to be set to all 0s.</td>
</tr>
</table>

<table>
<caption>8.3.5.3.2.5 Spoke RID - Spoke Revision ID (Offset 0Ch) Table 8-59. Spoke Revision ID</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>7:0</td>
<td>RO</td>
<td>Spoke Revision ID Uniquely identifies a Spoke Vendor to Software. This ID is assigned by UCIe Consortium.</td>
</tr>
</table>

<table>
<caption>8.3.5.3.2.6 DMS-ID - Spoke DMS-ID (Offset 10h) Table 8-60. DMS-ID</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>7:0</td>
<td>RO</td>
<td>DFx Management Spoke-ID Statically assigned Spoke-ID value for this Spoke. Spoke-ID is used for ID- routed UDMs.</td>
</tr>
</table>

<table>
<caption>8.3.5.3.2.7 Associated DMS-ID[0, 1, 2] (Offsets 11h, 12h, 13h) Table 8-61. Associated DMS-ID[0, 1, 2]</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>7:0</td>
<td>RO</td>
<td>Associated DMS-ID Spoke-ID associated with other Spokes that constitute the same UCIe link. For example, if there are separate Spokes for some or all of the IPs that constitute a full UCIe stack - Adapter, Physical Layer, Protocol Stack0, Protocol Stack1 - these registers within each Spoke provide the DMS-IDs of the related partner Spokes. If there are no related Spokes, this register reads as FFh. If there are multiple protocol stacks, the lower value DMS-ID belongs to Stack 0 and higher value belongs to Stack 1. These registers are used by SW to identify all the Spokes that constitute a single UCIe link.</td>
</tr>
</table>

# 8.3.5.3.2.8 Spoke CAP - Spoke Capability (Offset 14h)

<table>
<caption>Table 8-62. Spoke Capability</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>3:0</td>
<td>RO</td>
<td>Version Set to 0h for this version of the capability.</td>
</tr>
<tr>
<td>7:4</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
<tr>
<td>15:8</td>
<td>RO</td>
<td>Spoke Type 0: UCIe.Adapter. Indicates a Spoke associated with UCIe Adapter. 1: UCIe.Physical_Layer. Indicates a Spoke associated with UCIe Physical Layer. 2: UCIe.Adapter_Physical_Layer. Indicates a common Spoke across both UCIe Adapter and Physical Layer. 3 to 127: Reserved. 128 to 255: Vendor-defined.</td>
</tr>
<tr>
<td>31:16</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

# 8.3.5.3.2.9 Spoke CTL - Spoke Control (Offset 18h)

<table>
<caption>Table 8-63. Spoke Control</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>0</td>
<td>RW</td>
<td>Enable Test and Debug Vendor-defined UDM as Initiator 0: Spoke cannot initiate Vendor-defined UDM. 1: Spoke can initiate Vendor-defined UDM. Spokes that do not implement Vendor-defined UDM as initiator can hardwire this bit to 0.</td>
</tr>
<tr>
<td>31:1</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

# 8.3.5.3.2.10 Spoke STS - Spoke Status (Offset 1Ch)

<table>
<caption>Table 8-64. Spoke Status</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>0</td>
<td>RO</td>
<td>Spoke Used Indicates that the Spoke has been accessed at least once since the last Management Reset. Access implies sending or receiving UMAP packets or UDMs. Bit is cleared on the next Management Reset.</td>
</tr>
<tr>
<td>31:1</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

# 8.3.5.3.2.11 DMS_Length_Low - DMS Register Space Length Low (Offset 20h)

<table>
<caption>Table 8-65. DMS Register Space Length Low</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>$3 1 : 1 2$</td>
<td>RO</td>
<td>Lower 20 bits of length of the DMS register space from Offset 0h of DMS, in multiples of 4K. Value of 1000h for {DMS_Length_High :: DMS_Length_Low} indicates 4K length, 2000h indicates 8K length, etc. Bits [11:0] in this register are reserved to ensure 4k multiples of length. UCIe Spoke Types 0, 1, and 2 implemented to this revision of the spec must have a value in this register such that the DMS register space is not larger than 4 MB.</td>
</tr>
<tr>
<td>11:0</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

## 8.3.5.3.2.12 DMS_Length_High - DMS Register Space Length High (Offset 24h)

<table>
<caption>Table 8-66. DMS Register Space Length High</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>31:0</td>
<td>RO</td>
<td>Upper 32 bits of length of the DMS register space from Offset 0h of DMS, in multiples of 4K. Value of 1000h for {DMS_Length_High :: DMS_Length_Low} indicates 4K length, 2000h indicates 8K length, etc. UCIe Spoke Types 0, 1, and 2 implemented to this revision of the spec must set this value to all 0s.</td>
</tr>
</table>

<table>
<caption>8.3.5.3.2.13 DMS_Ext_Cap_Low - DMS Extended Capability Pointer Low (Offset 28h) Table 8-67. DMS Extended Capability Pointer Low</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>31:2</td>
<td>RO</td>
<td>Lower 30 bits of the DWORD-aligned offset from the DMS starting address, where any extended capabilities start, when present in the DMS. Value of all Os indicates that there are no extended capabilities (default).</td>
</tr>
<tr>
<td>1:0</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

<table>
<caption>8.3.5.3.2.14 DMS_Ext_Cap_High - DMS Extended Capability Pointer High (Offset 2Ch) Table 8-68. DMS Extended Capability Pointer High</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>31:0</td>
<td>RO</td>
<td>Upper 32 bits of the DWORD-aligned offset from the DMS starting address, where any extended capabilities start, when present in the DMS. Value of all Os indicates that there are no extended capabilities (default).</td>
</tr>
</table>

### 8.3.5.3.3 DMS Registers of UCIe Spoke Types ('Spoke Type' = 0 through 2)

Figure 8-67 shows the DMS register map for the UCIe Spoke types. Figure 8-66 and Section 8.3.5.3.2
detail registers that are common to all Spoke types. This section details the remaining registers,
which are unique to the UCIe Spoke types.

Figure 8-67. DMS Register Map for UCIe Spoke Types

<figure>

31

24 23

16 15

8 7

0

0B

48B

80B

•

•

•

128B

•

•

•

$N$

</figure>

<table>
<tr>
<th colspan="2">Spoke DevID</th>
<th colspan="2">Spoke VID</th>
</tr>
<tr>
<th colspan="4">DMS_Next_Low</th>
</tr>
<tr>
<td colspan="4">DMS_Next_High</td>
</tr>
<tr>
<td colspan="2">Port ID</td>
<td>Reserved</td>
<td>Spoke RID</td>
</tr>
<tr>
<td>Associated DMS-ID2</td>
<td>Associated DMS-ID1</td>
<td>Associated DMS-ID0</td>
<td>DMS-ID</td>
</tr>
<tr>
<td colspan="4">Spoke CAP</td>
</tr>
<tr>
<td colspan="4">Spoke CTL</td>
</tr>
<tr>
<td></td>
<td colspan="3">Spoke STS</td>
</tr>
<tr>
<td></td>
<td colspan="3">DMS_Length_Low</td>
</tr>
<tr>
<td></td>
<td colspan="3">DMS_Length_High</td>
</tr>
<tr>
<td></td>
<td colspan="2">DMS_Ext_Cap_Low</td>
<td></td>
</tr>
<tr>
<td></td>
<td colspan="3">DMS_Ext_Cap_High</td>
</tr>
<tr>
<td></td>
<td colspan="3">Adapter_Physical_Layer_Ptr_Low</td>
</tr>
<tr>
<td colspan="4">Adapter_Physical_Layer_Ptr_High</td>
</tr>
<tr>
<td></td>
<td colspan="3">Compliance_Test_Ptr_Low</td>
</tr>
<tr>
<td></td>
<td colspan="3">Compliance_Test_Ptr_High</td>
</tr>
<tr>
<td></td>
<td colspan="3">Impl_Spec_Adapter_Ptr_Low</td>
</tr>
<tr>
<td></td>
<td colspan="3">Impl_Spec_Adapter_Ptr_High</td>
</tr>
<tr>
<td></td>
<td colspan="3">Impl_Spec_Physical_Layer_Ptr_Low</td>
</tr>
<tr>
<td colspan="4">Impl_Spec_Physical_Layer_Ptr_High</td>
</tr>
<tr>
<td></td>
<td colspan="3">Reserved</td>
</tr>
<tr>
<td></td>
<td colspan="3">UCIe Link DVSEC</td>
</tr>
<tr>
<td></td>
<td colspan="2">Vendor-defined</td>
<td></td>
</tr>
<tr>
<td></td>
<td colspan="3">UCIe Link Register Blocks</td>
</tr>
<tr>
<td></td>
<td colspan="3">Vendor-defined</td>
</tr>
</table>

# 8.3.5.3.3.1 Port ID - Management Port ID (Offset 1Eh)

<table>
<caption>Table 8-69. Port ID</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>15:0</td>
<td>RO</td>
<td>Port ID For Spoke Types 0, 1, and 2, this register indicates the Port ID of the UCIe link that is associated with the Spoke, if a Port ID exists for the link. A UCIe link has a Port ID assigned to it if the link is a Management Port. If the link does not have an assigned Port ID, this register reads as FFFFh.</td>
</tr>
</table>

<table>
<caption>8.3.5.3.3.2 Adapter_Physical_Layer_Ptr_Low - Adapter/Physical Layer Register Block Pointer Low (Offset 30h) Table 8-70. Adapter_Physical_Layer_Ptr_Low</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td rowspan="3">31:12</td>
<td rowspan="3">RO</td>
<td>Lower 20 bits of the 4K-aligned offset (from the starting address of the Spoke) of the UCIe Adapter/Physical Layer register block that is associated with the UCIe link.</td>
</tr>
<tr>
<td>Accesses to registers that are referenced by Adapter_Physical_Layer_Ptr_Low/High pointers in a UCIe.Adapter Spoke are limited to the 4k block(s) that contain the Adapter registers and the register block header itself, and the 4k block(s) that contain Physical Layer registers are treated as reserved.</td>
</tr>
<tr>
<td>Accesses to registers that are referenced by Adapter_Physical_Layer_Ptr_Low/High pointers in a UCIe.Physical_Layer Spoke are limited to the 4k block(s) that contain the PHY registers and the register block header itself, and Adapter registers are treated as reserved.</td>
</tr>
<tr>
<td>11:0</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

# 8.3.5.3.3.3 Adapter_Physical_Layer_Ptr_High - Adapter/PHY Register Block Pointer High (Offset 34h)

<table>
<caption>Table 8-71. Adapter_Physical_Layer_Ptr_High</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>31:0</td>
<td>RO</td>
<td>Upper 32 bits of the 4K-aligned offset (from the starting address of the Spoke) of the UCIe Adapter/PHY register block that is associated with the UCIe link. Accesses to registers that are referenced by Adapter_Physical_Layer_Ptr_Low/High pointers in a UCIe.Adapter Spoke are limited to the 4k block(s) that contain the Adapter registers and the register block header itself, and the 4k block(s) that contain PHY registers are treated as reserved. Accesses to registers that are referenced by Adapter_Physical_Layer_Ptr_Low/High pointers in a UCIe.Physical_Layer Spoke are limited to the 4k block(s) that contain the PHY registers and the register block header itself, and Adapter registers are treated as reserved.</td>
</tr>
</table>

# 8.3.5.3.3.4 Compliance_Test_Ptr_Low - Compliance and Test Register Block Pointer Low (Offset 38h)

<table>
<caption>Table 8-72. Compliance_Test_Ptr_Low</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td rowspan="2">$3 1 : 1 2$</td>
<td rowspan="2">RO</td>
<td>Lower 20 bits of the 4K-aligned offset (from the starting address of the Spoke) of the UCIe Test/Compliance register block that is associated with the UCIe link.</td>
</tr>
<tr>
<td>Accesses to registers that are referenced by Compliance_Test_Ptr_Low/High pointers in a UCIe.Adapter Spoke are limited to the 4k block(s) that contain the Adapter registers and the register block header itself, and the 4k block(s) that contain PHY registers are treated as reserved. Accesses to registers that are referenced by Compliance_Test_Ptr_Low/High pointers in a UCIe.Physical_Layer Spoke are limited to the 4k block(s) that contain the PHY registers and the register block header itself, and the Adapter registers are treated as reserved. Accesses to registers that are referenced by Compliance_Test_Ptr_Low/High pointers in a UCIe.Adapter_Physical_Layer Spoke have no access restrictions. Set to all 0s if this register block is not implemented.</td>
</tr>
<tr>
<td>11:0</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

## 8.3.5.3.3.5 Compliance_Test_Ptr_High - Compliance and Test Register Block Pointer High (Offset 3Ch)

<table>
<caption>Table 8-73. Compliance_Test_Ptr_High</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>31:0</td>
<td>RO</td>
<td>Upper 32 bits of the 4K-aligned offset (from the starting address of the Spoke) of the UCIe Test/Compliance register block that is associated with the UCIe link. Accesses to registers that are referenced by Compliance_Test_Ptr_Low/High pointers in a UCIe.Adapter Spoke are limited to the 4k block(s) that contain the Adapter registers and the register block header itself, and the 4k block(s) that contain PHY registers are treated as reserved. Accesses to registers that are referenced by Compliance_Test_Ptr_Low/High pointers in a UCIe.Physical_Layer Spoke are limited to the 4k block(s) that contain the PHY registers and the register block header itself, and the Adapter registers are treated as reserved. Accesses to registers that are referenced by Compliance_Test_Ptr_Low/High pointers in a UCIe.Adapter_Physical_Layer Spoke have no access restrictions. Set to all 0s if this register block is not implemented.</td>
</tr>
</table>

## 8.3.5.3.3.6 Impl_Spec_Adapter_Ptr_Low - Implementation-specific Adapter Register Block Pointer Low (Offset 40h)

<table>
<caption>Table 8-74. Impl_Spec_Adapter_Ptr_Low</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>$3 1 : 1 2$</td>
<td>RO</td>
<td>Lower 20 bits of the 4K-aligned offset (from the starting address of the Spoke) of the Adapter Implementation-specific register block. In a UCIe.Physical_Layer Spoke type, this pointer must be set to all 0s. Also set to all Os if the register block is not implemented in the design.</td>
</tr>
<tr>
<td>11:0</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

<table>
<caption>8.3.5.3.3.7 Impl_Spec_Adapter_Ptr_High - Implementation-specific Adapter Register Block Pointer High (Offset 44h) Table 8-75. Impl_Spec_Adapter_Ptr_High</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>$3 1 : 0$</td>
<td>RO</td>
<td>Upper 32 bits of the 4K-aligned offset (from the starting address of the Spoke) of the Adapter Implementation-specific register block. In a UCIe.Physical_Layer Spoke type, this pointer must be set to all 0s. Also set to all Os if the register block is not implemented in the design.</td>
</tr>
</table>

<table>
<caption>8.3.5.3.3.8 Impl_Spec_Physical_Layer_Ptr_Low - Implementation-specific Physical Layer Register Block Low (Offset 48h) Table 8-76. Impl_Spec_Physical_Layer_Ptr_Low</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>31:12</td>
<td>RO</td>
<td>Lower 20 bits of the 4K-aligned offset (from the starting address of the Spoke) of the Physical Layer Implementation-specific register block. In a UCIe.Adapter Spoke type, this pointer must be set to all 0s. Also set to all Os if the register block is not implemented in the design.</td>
</tr>
<tr>
<td>11:0</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

<table>
<caption>8.3.5.3.3.9 Impl_Spec_Physical_Layer_Ptr_High - Implementation-specific Physical Layer Register Block High (Offset 4Ch) Table 8-77. Impl_Spec_Physical_Layer_Ptr_High</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>31:0</td>
<td>RO</td>
<td>Upper 32 bits of the 4K-aligned offset (from the starting address of the Spoke) of the Physical Layer Implementation-specific register block. In a UCIe.Adapter Spoke type, this pointer must be set to all 0s. Also set to all Os if the register block is not implemented in the design.</td>
</tr>
</table>

### 8.3.5.3.3.10 UCIe Link DVSEC - UCIe Link DVSEC (Offset 80h)

UCIe Link DVSEC (see Section 9.5.1) is mirrored starting at this location. Accesses to the DVSEC by
the UCIe.Physical_Layer Spoke type are treated as reserved.

#### IMPLEMENTATION NOTE

Spokes can restrict access to UCIe link registers based on access control
considerations (see Section 8.1.3.5 for details).

### 8.3.5.3.3.11 UCIe Link Register Blocks (Offset Is Implementation-dependent)

UCIe link memory register blocks - Adapter_Physical_Layer, Compliance_Test (if supported),
Impl_Spec_Adapter (if supported), and Impl_Spec_Physical_Layer (if supported) - are mirrored at
vendor-defined offsets in the Spoke's memory space.

### 8.3.5.3.4 DMS Registers of Vendor-defined Spoke Types ('Spoke Type' = 128 through 255)

Figure 8-68 shows the DMS register map for the Vendor-defined Spoke types. Figure 8-66 and
Section 8.3.5.3.2 detail registers that are common to all Spoke types. Section 8.3.5.3.3.1 details the
Port ID register. Vendor-defined Spokes do not have any additional architected registers.

<table>
<caption>Figure 8-68. DMS Register Map for Vendor-defined Spoke Types</caption>
<tr>
<th colspan="2">Spoke DevID</th>
<th colspan="2">Spoke VID</th>
<th>0B</th>
</tr>
<tr>
<th colspan="4">DMS_Next_Low</th>
<th></th>
</tr>
<tr>
<td colspan="4">DMS_Next_High</td>
<td></td>
</tr>
<tr>
<td colspan="2">Port ID</td>
<td>Reserved</td>
<td>Spoke RID</td>
<td></td>
</tr>
<tr>
<td>Associated DMS-ID2</td>
<td>Associated DMS-ID1</td>
<td>Associated DMS-ID0</td>
<td>DMS-ID</td>
<td></td>
</tr>
<tr>
<td colspan="4">Spoke CAP</td>
<td></td>
</tr>
<tr>
<td colspan="4">Spoke CTL</td>
<td></td>
</tr>
<tr>
<td colspan="4">Spoke STS</td>
<td></td>
</tr>
<tr>
<td colspan="4">DMS_Length_Low</td>
<td></td>
</tr>
<tr>
<td></td>
<td colspan="3">DMS_Length_High</td>
<td></td>
</tr>
<tr>
<td></td>
<td colspan="3">DMS_Ext_Cap_Low</td>
<td></td>
</tr>
<tr>
<td colspan="4">DMS_Ext_Cap_High</td>
<td></td>
</tr>
<tr>
<td></td>
<td colspan="2">Reserved</td>
<td></td>
<td>48B • • •</td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td>128B</td>
</tr>
<tr>
<td></td>
<td colspan="2"></td>
<td></td>
<td>•</td>
</tr>
<tr>
<td></td>
<td colspan="2">Vendor-defined</td>
<td></td>
<td>•</td>
</tr>
<tr>
<td></td>
<td colspan="2"></td>
<td></td>
<td>•</td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
<td></td>
<td>$N$</td>
</tr>
</table>

<figure>

31
24 23

16 15
8 7
0

</figure>

### 8.3.5.3.5 DMS Register Implementation in UCIe Adapter and in UCIe Physical Layer

#### IMPLEMENTATION NOTE

For Spoke Type 0, the DMS registers are implemented in the Adapter. For Spoke Type
1, the DMS registers are implemented in the Physical Layer. For Spoke Type 2, all but
the register blocks associated with the Physical Layer are implemented in the Adapter.
These registers are accessed over the FDI config bus $\left( 1 p - c f g * / p 1 _ { - } c f g ^ { * } \right)$
DMS Register read/write opcodes (see Table 7-1,
Mapped to Sideband Packet Types"). SoC logic that interfaces with
management fabric (which is implementation-specific) is required to $p e r f o r m \quad t h e$
conversion from Management Transport protocol UMAP packets to FDI config bus
packets. The FDI config bus is defined in Section 10.2.

##### 8.4 Management Capabilities

Management features described in this section are optional unless otherwise specified within the
feature's description.

###### 8.4.1 Early Firmware Download

####### 8.4.1.1 Early Firmware Download Guidelines

The Early Firmware Download capability enables a Management Element to load firmware to another
Management Element. It is not mandatory to use this feature (i.e., some vendors may not require
downloadable firmware).

For Early Firmware Download capability, the management element that loads firmware into another
management element is called the initiator. The management element into which a firmware is loaded
is called the target. Those terms are only used within the description of the Early Firmware Download
capability (Section 8.4.1 and all its subsections).

The firmware downloaded to the target management element can be used by any hardware block that
requires firmware within the chiplet. The target management element can have one or more Early
Firmware Download capabilities structures for one or more hardware blocks.

An Early Firmware Download capability can be used to download multiple distinct firmwares. Each
firmware must be downloaded one after the other.

#### IMPLEMENTATION NOTE

If a chiplet needs to allow for concurrent firmware download of multiple firmwares
then it should expose multiple distinct firmware download capabilities in its
management capability directory (see Section 8.1.3.6.1). Each distinct Early
Firmware Download capability shall have a distinct Early Firmware Download
capability Identifier Value (see Table 8-78).

Implementers are responsible for properly handling concurrent utilization of multiple
distinct firmware download capabilities. Implementers can leverage the Early
Firmware Download capability state (as reported by the EFD_STATE field) of each of
the multiple Early Firmware Download capabilities to enforce proper ordering and
synchronization across distinct Early Firmware Download capabilities.

To uniquely identify which firmware the initiator should download, the initiator should
use the three following identifiers:

· UCIe vendor identifier (see Section 8.1.3.6)

· Early Firmware Download capability Identifier (DWORD 1 in Figure 8-69)

· Firmware identifier (DWORD 2 in Figure 8-69)

### 8.4.1.2 Early Firmware Download Capability

<table>
<caption>Figure 8-69. Early Firmware Download Capability Structure</caption>
<tr>
<th rowspan="2"></th>
<th colspan="8">+3</th>
<th colspan="8">+2</th>
<th colspan="8">+1</th>
<th colspan="8">+0</th>
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
<th></th>
<th></th>
<th></th>
<th></th>
<th>876543210</th>
<th></th>
<th></th>
<th></th>
<th></th>
</tr>
</table>

<figure>

DWORD 0

Rsvd

Management Capability ID

Reserved

Version (RO)

DWORD 1

EFD_CAPABILITY_ID (RO)

DWORD 2

EFD_FIRMWARE_ID (RO)

DWORD 3

Reserved

EFD_Sª

DWORD 4

EFD_Vb
☒

Reserved

EFD_EC

DWORD 5

EFD_PAYLOAD_SIZE (RW)

DWORD 7

Reserved

EFD_COd

Reserved

EFD_CAe

DWORD 7

Reserved

DWORD 8

Sink Circular Buffer Data Structure

…

DWORD 23

</figure>

a. EFD_S is the shorthand for the EFD_STATE field which is read only (RO).

b. EFD_V is the shorthand for the VENDOR_DEFINED_ERROR_STATUS field which is read only (RO).

c. EFD_E is the shorthand for the EFD_ERROR field which is read only (RO).

d. EFD_CO is the shorthand for the EFD_CONTROL field which is read and write (RW).

e. EFD_CA is the shorthand for the EFD_CAPABILITIES field which is read only (RO).

<table>
<caption>Table 8-78. Early Firmware Download Capability Structure Fields</caption>
<tr>
<th>Register/Field Name</th>
<th>DWORD &amp; Bit Location</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>Ver</td>
<td>$0 \left[ 7 : 0 \right]$</td>
<td>RO</td>
<td>Capability Structure Version This field indicates the version of this capability structure. This field has a value of 00h in this specification.</td>
</tr>
<tr>
<td>$\begin{array}{} { \text { Management } } \\ { \text { Capability ID } } \end{array}$</td>
<td>0 [29:16]</td>
<td>RO</td>
<td>Management Capability ID This field specifies the Capability ID of this Management Capability structure. $\begin{array}{} { \text { The Early Firmware Down load Capablity structure has } } \\ { \text { Management Capability ID of 006h. } } \end{array}$ a</td>
</tr>
<tr>
<td>EFD_CAPABILITY_ID</td>
<td>$1 \left[ 3 1 : 0 \right]$</td>
<td>$R O$</td>
<td>Early Firmware Download Capability Identifier Unique identifier for this Early Firmware Download Capability structure. $\begin{array}{} { \text { This register is only useful if there are are multiple distinct early } } \\ { \text { firmware capability in such cases this register can be used tc } } \end{array}$ uniquely identify each distinct early firmware capability.</td>
</tr>
<tr>
<td>EFD_FIRMWARE_ID</td>
<td>$2 \left[ 3 1 : 0 \right]$</td>
<td>$R O$</td>
<td>Firmware Identifier The firmware identifier of the requested firmware payload (see Section 8.4.1.8). If there are multiple firmware blocks to download with this EFD capability, this value will change after each is downloaded. Note a value of FFFF_FFFFh means that the hardware does not need any more firmware to be downloaded.</td>
</tr>
<tr>
<td>EFD_STATE</td>
<td>$3 \left[ 2 : 0 \right]$</td>
<td>$R O$</td>
<td>$T h e \quad c u r r e n t \quad s t a t e \quad o f \quad t h e \quad E a r l y \quad F i r m w a r e \quad D o w n l o a d \left( s e e \right.$</td>
</tr>
<tr>
<td>EFD_ERROR</td>
<td>$4 \left[ 4 : 0 \right]$</td>
<td>$R O$</td>
<td>Error Current error code if any (see Table 8-80 for definitions).</td>
</tr>
<tr>
<td>EFD_VENDOR_DEFINED ERROR_STATUS</td>
<td>$4 \left[ 3 1 : 1 6 \right]$</td>
<td>$R O$</td>
<td>Vendor Defined Error Status $V e n d o r \quad d e f i n e d \quad e r r o r \quad s t a t u s \quad f o r \quad a n \quad e r r o r \quad r e p o r t e d \quad i n \quad E F D \_ E R R O R .$</td>
</tr>
<tr>
<td>EFD_PAYLOAD_SIZE</td>
<td>$5 \left[ 3 1 : 0 \right]$</td>
<td>RW</td>
<td>Firmware Payload Size The size, in DWORDs, of the firmware payload that is downloading.</td>
</tr>
<tr>
<td>EFD_CAPABILITIES</td>
<td>$6 \left[ 3 : 0 \right]$</td>
<td>RO</td>
<td>$S e e \quad S e c t i o n \quad 8 . 4 . 1 . 6 .$</td>
</tr>
<tr>
<td>EFD_CONTROL</td>
<td>$6 \left[ 1 9 : 1 6 \right]$</td>
<td>RW</td>
<td>$S e e \quad S e c t i o n \quad 8 . 4 . 1 . 7 .$</td>
</tr>
<tr>
<td>Sink Circular Buffer Data Structure</td>
<td>8 to 23</td>
<td>-</td>
<td>Sink Circular Buffer Data Structure See Section 8.4.1.9. For descriptions of registers and fields, see Section 8.1.5.1.</td>
</tr>
</table>

### 8.4.1.3 Early Firmware Download Asset Class ID

The security asset class associated with the Early Firmware Download capability is specified by the
management element function capability structure that instantiates it. It is recommended to use
standard Asset Class ID 0, which is for SiP security configuration (see Table 8-7 in Section 8.1.3.5.1).

A management element can expose multiple distinct Early Firmware Download capabilities and each
can have a different Asset Class ID. This can be useful if different firmware downloads are needed
with different asset classes.

# 8.4.1.4 Early Firmware Download Initialization

There is no specific initialization sequence needed for Early Firmware Download capability other than
Circular Buffer Initialization as described in Section 8.1.5.1.3.

## 8.4.1.5 Early Firmware Download States and Error

The values of the EFD_STATE field are defined in Table 8-79. Early Firmware Download capability shall
start in the NOT_READY state while the chiplet is initializing and transition to the READY state when
the Early Firmware Download capability is ready for use (which includes the Circular Buffer being
ready for use); otherwise, if the initialization fails, it goes to ERROR state. The state machine is shown
in Figure 8-70.

<table>
<caption>Table 8-79. EFD_STATE Field Values Definition</caption>
<tr>
<th>Field Values</th>
<th>Description</th>
</tr>
<tr>
<td>0</td>
<td>NOT_READY Early Firmware Download capability is not ready.</td>
</tr>
<tr>
<td>1</td>
<td>ERROR Early Firmware Download detected an error. See the error code and Table 8-80 for details.</td>
</tr>
<tr>
<td>2</td>
<td>READY Early Firmware Download capability is ready. Before downloading firmware the initiator must verify that the Circular Buffer is in READY state.</td>
</tr>
<tr>
<td>3</td>
<td>DOWNLOADING Firmware payload size has been written to allow the download to start and the download has not finished.</td>
</tr>
<tr>
<td>4</td>
<td>PROCESSING The firmware is being loaded and executed.</td>
</tr>
<tr>
<td>Other values</td>
<td>Reserved</td>
</tr>
</table>

<figure>
<figcaption>Figure 8-70. Early Firmware Download State Machine</figcaption>

NOT READY

READY

DOWNLOADING

PROCESSING

Reset

ERROR

</figure>

When an error happens the EFD_ERROR field shall reflect the first error condition that was observed
by the hardware. See Table 8-80 for the definitions of EFD_ERROR field values.

<table>
<caption>Table 8-80. EFD_ERROR Field Value Definitions</caption>
<tr>
<th>Error Code</th>
<th>Error</th>
</tr>
<tr>
<td>0</td>
<td>No errors.</td>
</tr>
<tr>
<td>1</td>
<td>Internal Internal error is for vendor-defined errors.</td>
</tr>
<tr>
<td>2</td>
<td>Initialization Failed The initialization failed (i.e., going from NOT_READY to READY state failed). Must use the Reset bit of EFD_CONTROL (if supported) or a full chiplet reset to clear the error.</td>
</tr>
<tr>
<td>3</td>
<td>Downloading Failed An error did occur while downloading the firmware. The initiator should check the Circular Buffer structure for Circular Buffer error that might explain this error. Must use the Reset bit of EFD_CONTROL (if supported) or a full chiplet reset to clear the error.</td>
</tr>
<tr>
<td>4</td>
<td>Processing Failed The processing step (which is optional; see Section 8.4.1.8 for details) failed. This is vendor defined and can include verifying firmware image signature or other vendor defined reasons for firmware download failing to be successful. Must use the Reset bit of EFD_CONTROL (if supported) or a full chiplet reset to clear the error.</td>
</tr>
<tr>
<td>Other values</td>
<td>Reserved</td>
</tr>
</table>

The EFD_VENDOR_DEFINED_ERROR_STATUS field defined in Table 8-81 is for vendor-defined error
status. It is for providing additional details related to the error reported in EFD_ERROR (i.e., an
initiator does not need to use the EFD_VENDOR_DEFINED_ERROR_STATUS when handling errors).

If there is no vendor-defined status when the Early Firmware Download is in ERROR state, then this
field shall return 0 (see Table 8-81).

Note that if EFD_VENDOR_DEFINED_ERROR_STATUS returns 0, it does not mean that there are no
errors. When an error occurs, EFD_ERROR is set to a nonzero value (see Table 8-80) and EFD_STATE
reports ERROR state.

<table>
<caption>Table 8-81. EFD_VENDOR_DEFINED_ERROR_STATUS Value Definitions</caption>
<tr>
<th>Field Values</th>
<th>Description</th>
</tr>
<tr>
<td>0</td>
<td>No vendor-defined error status. The reported error, if any, does not require any vendor-defined error status.</td>
</tr>
<tr>
<td>Other values</td>
<td>Reserved for vendors. Vendors are free to define meaning for each of those values.</td>
</tr>
</table>

## 8.4.1.6 Early Firmware Download Capabilities

Table 8-82 defines each bit of the EFD_CAPABILITIES field.

<table>
<caption>Table 8-82. EFD_CAPABILITIES Bit Definition</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>0</td>
<td>RO</td>
<td>Reset Supported If 1, then reset is supported (i.e., initiator can reset the Early Firmware Download using reset bit of EFD_CONTROL). See Section 8.4.1.7 for details. If 0, then reset is not supported and if an error occurs, then the initiator may perform a full chiplet reset to recover from error. $\begin{array}{} { \text { Note that this } b } \\ { \text { Section } 8 . 4 . 1 . 8 } \end{array}$ may change value when EFD_STATE becomes READY (see</td>
</tr>
<tr>
<td>3:1</td>
<td>RO</td>
<td>Reserved</td>
</tr>
</table>

## 8.4.1.7 Early Firmware Download Control

Table 8-83 defines each bit of the Early Firmware Download capability control register
(EFD_CONTROL).

<table>
<caption>Table 8-83. EFD_CONTROL - Early Firmware Download Capability Control Bit Definition</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>0</td>
<td>RW</td>
<td>Reset If reset is supported, writing 1 to this bit will cause a reset of the Early Firmware Download capability. Note that writing 1 to this bit will also reset the Circular Buffer part of this Early Firmware Download capability (as if 1 was written to the reset bit of the CB_CONTROL reset bit see Section 8.1.5.1.6). It is illegal to write 1 to the reset bit while the Early Firmware Download is in the NOT_READY state. The Early Firmware Download shall ignore such reset requests and continue with its initialization. Resetting the Early Firmware Download capability shall clear error conditions and transition the Early Firmware Download to the NOT_READY state while it is re- initializing itself. After reset completes (check for READY state in EFD_STATE) the initiator must check EFD_FIRMWARE_ID field to determine which image to download next, as it may be different than the image that was being downloaded prior to the reset.</td>
</tr>
<tr>
<td>3:1</td>
<td>RW</td>
<td>Reserved</td>
</tr>
</table>

Read of EFD_CONTROL shall return 0.

## IMPLEMENTATION NOTE

If the Circular Buffer of an Early Firmware Download capability is reset (using
CB_CONTROL) without resetting the Early Firmware Download capability (see
EFD_CONTROL), then the behavior is implementation-specific and potentially
unpredictable. The initiator should use EFD_CONTROL reset (if supported) to
concurrently reset Early Firmware Download and its Circular Buffer.

### 8.4.1.8 Early Firmware Download Flow

The initiator must wait for the Early Firmware Download capability to be in READY state (see
EFD_STATE field definition). If the Early Firmware Download capability fails to initialize then it shall go
to ERROR state. If Early Firmware Download capability goes to ERROR state, the initiator may try to
reset the Early Firmware Download capability (see Section 8.4.1.7) if supported (see
Section 8.4.1.6). If the Early Firmware Download capability goes to ERROR state again, it is not
operational and full chiplet or chip reset may be necessary.

After the Early Firmware Download capability reports READY state, the initiator may read the
EFD_FIRMWARE_ID register and find the corresponding firmware payload.

The initiator shall write the firmware payload size into the EFD_PAYLOAD_SIZE register. The target
may start processing firmware data as soon as the EFD_PAYLOAD_SIZE register is updated by the
initiator and data is available in the Circular Buffer.

The initiator can start writing the firmware payload into the Circular Buffer as soon as the Early
Firmware Download capability reports the READY state. The initiator should start writing the firmware
payload only if the initiator knows the firmware identifier that will be requested as reported in the
firmware identifier register after firmware download state field reports READY.

A firmware image is done downloading once firmware payload size DWORDs (as programmed in the
EFD_PAYLOAD_SIZE register) have been consumed from the Circular Buffer. The initiator can then
monitor the EFD_STATE field and observe either PROCESSING, READY, or ERROR state.

If the PROCESSING state completes with no errors the state field will transition back to the READY
state. The PROCESSING state may require little or no time and may not be observed by the initiator.
If the PROCESSING state fails then the state field transitions to ERROR state and the EFD_ERROR
register will be updated with the corresponding error value.

When the EFD_STATE field transitions to READY state the EFD_FIRMWARE_ID register changes to the
next requested firmware image. A value of FFFF_FFFFh in EFD_FIRMWARE_ID indicates that no
additional firmware images are being requested, and the firmware download flow is complete.

When the Circular Buffer becomes READY and a new Firmware Identifier (new value in
EFD_FIRMWARE_ID) is requested (and value is not FFFF_FFFFh), the above process repeats.

An Early Firmware Download capability can be used to download multiple distinct firmwares. Each
firmware must be downloaded one after the other.

#### IMPLEMENTATION NOTE

The PROCESSING state is a vendor-defined state during which the vendor can
perform various operations on the firmware payload. For example, a vendor might
implement security checks on the firmware payload, such as verifying the integrity
and origin of the firmware.

If any of those vendor-defined operations fails the vendor shall report it by
transitioning the Early Firmware Download capability state (EFD_STATE) from the
PROCESSING state to ERROR state.

# 8.4.1.9 Circular Buffer Requirements for Early Firmware Download

The Reset Supported bit of the CB_CAPABILITIES field (described in Section 8.1.5.1.4) shall contain
the same value as the Reset Supported bit of the EFD_CAPABILITIES field (described in
Section 8.4.1.6). If the Reset Supported bit of the EFD_CAPABILITIES field changes, the Reset
Supported bit of the CB_CAPABILITIES field must also change.

# 8.4.2 Power Management

This section describes the optional Power Management capabilities that may be implemented by the
chiplets of a UCIe-based SiP.

## 8.4.2.1 Fast Throttle

### 8.4.2.1.1 Fast Throttle Overview

Fast Throttle is an optional feature that can be used to communicate the need for an immediate
throttle response from chiplets in an SiP. This response is needed when a threshold for the configured
function (such as power or thermal) is exceeded. Fast Throttle Threshold is defined in the operational
range of the chiplet, typically close to but not at or exceeding the maximum limit of operation (such
as temperature or power). The purpose of the Fast Throttle is to take corrective action and to prevent
escalation to and beyond the maximum limits. As an example, one of the trigger-enabled Power
Management Elements detects temperature at or exceeding the Fast Throttle temperature threshold.
All Power Management Elements with Fast Throttle response enabled respond to the temperature
throttle trigger.

Figure 8-71 shows an example of an SiP with Fast Throttle support.

<figure>
<figcaption>Figure 8-71. Example Use of Fast Throttle</figcaption>

Platform
throttle
indication

SIP

PM Director

P

PM Element

P

PM Element

Chiplet -1

Bi-directional

Fast Throttle
(Open drain

signal)

Chiplet -2

PM Element

PM Element

Chiplet -N-1

Chiplet -N

</figure>

Figure 8-71 shows an SiP with multiple chiplets. Each chiplet is shown to have one or more Power
Management Elements. One chiplet has the Power Management (PM) Director which is part of one of
its Power Management Elements. The Fast Throttle Trigger is communicated to all these chiplets using
a bidirectional Fast Throttle signal. The platform can also indicate a need to trigger Fast Throttle which
the Power Management Director may pass along to the bidirectional Fast Throttle signal.

Some chiplets on an SiP may not have a Power Management Element and/or capability for Fast
Throttle.

UCIe Management Director will discover the Power Management Elements during the initialization
process.

Fast Throttle communication is recommended to be low latency and bidirectional in nature. When Fast
Throttle is triggered by a chiplet it must be communicated to all the chiplets with Fast Throttle
response enabled. All Power Management Elements with Fast Throttle response enabled should take
configured throttle action in a timely manner, to prevent escalation to or beyond the maximum limit of
operation. Open Drain signaling as described in Section 5.14 may be used for this communication.
Vendor-defined implementation of this signal may also be used. Open Drain is the UCIe-preferred
connection for interoperability between chiplets.

A Power Management Element can have either, both, or neither of Fast Throttle Trigger and Fast
Throttle Response capabilities. Based on the supported capabilities, respective data structures and
controls to configure these capabilities should be supported. Any Power Management Element with
Fast Throttle Trigger capability supported and enabled can trigger Fast Throttle. Any Power
Management Element with Fast Throttle Response capability supported and enabled must respond to
a Fast Throttle Trigger by taking the respective action. Throttle Trigger generation is independent of
Throttle Response handling. If both capabilities are enabled, a Power Management Element may

trigger Fast Throttle assertion from its end even if Fast Throttle is already asserted by some other
chiplet in the SiP.

Trigger capable elements:

· Advertises Trigger capability in its capability structure

· Supports Fast Throttle Trigger Control structure to configure Fast Throttle Trigger behavior

· (Optionally) Supports logging to record trigger history

· Generates and communicates Fast Throttle when the trigger conditions are met

Response capable elements:

· Advertises Fast Throttle Response Capability

· Supports Fast Throttle Response Control structure to configure response on Fast Throttle
assertion

· (Optionally) Supports logging to record response history

· Responds to Fast Throttle by taking the configured action

Power Management Director:

· Enumerates the capabilities of power management entities including Fast Throttle

· Configures trigger and response controls

· Optionally configures trigger and response logging

· Optionally samples Fast Throttle Trigger and response history during runtime by reading the
logging structures

. Optionally sets up and monitors platform throttle requests based on the SiP and platform
requirements. Shown as the SiP input "Platform Throttle Indication" in Figure 8-71.

Power-on Default Behavior:

· Fast Throttle feature is disabled on power-on. It is enabled, typically by the Power Management
Director, after the discovery and initialization process.

The following data structures are defined for Fast Throttle:

. Fast Throttle Trigger Capability Structure

· Fast Throttle Response Capability Structure

· Fast Throttle Logging Capability Structure

. Fast Throttle Trigger Control Structure

· Fast Throttle Response Control Structure

· Fast Throttle Logging Control Structure

· Fast Throttle Logging Structure

<figure>
<figcaption>Figure 8-72. Overview of the Fast Throttle Data Structures</figcaption>

FFFF_FFFF_FFFF_FFFFh

Fast Throttle Logging Strucure

Fast Throttle Open Drain Signal
Capability

Fast Throttle Trigger Capability and
Control

Capability Directory

Fast Throttle Trigger Capability
Fast Throttle Logging Capability
Fast Throttle Responsa Capability

Fast Throttle Response Capability
and Control

Fast Throttle Logging Capability
and Control

0000_0000 0000_0000h

</figure>

## 8.4.2.1.2 Fast Throttle Capability Structures

### 8.4.2.1.2.1 Fast Throttle Trigger Capability Structure

This section defines throttle trigger conditions supported by the Power Management Element (see
Figure 8-73 and Table 8-84).

Figure 8-73. Fast Throttle Trigger Capability Structure

<table>
<tr>
<th rowspan="2"></th>
<th colspan="8">+3</th>
<th colspan="8">+2</th>
<th colspan="8">+1</th>
<th colspan="8">+0</th>
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
<th>110</th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th>9876543210</th>
<th></th>
<th></th>
<th></th>
</tr>
</table>

<figure>

DWORD 0

Rsvd

Management Capability ID

Reserved

Version

DWORD 1

Fast Throttle Signal Capability Address Low

DWORD 2

Fast Throttle Signal Capability Address High

Number of Fast
Throttle Trigger
Capabilities (N)

DWORD 3

Reserved

DWORD 4

Fast Throttle Trigger Capability (0)

DWORD 5

Fast Throttle Trigger Capability (1)

...

...

DWORD
(N-1)+4

Fast Throttle Trigger Capability (N-1)

</figure>

<table>
<caption>Figure 8-74. Fast Throttle Trigger Capability Format</caption>
<tr>
<th></th>
<th colspan="7">+3</th>
<th colspan="8">+2</th>
<th colspan="8">+1</th>
<th></th>
<th colspan="7">+0</th>
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
<th>109876543210</th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
</tr>
</table>

DWORD

Vendor-defined Fast Throttle Trigger Attributes

Reserved

Fast Throttle
Trigger Type

<table>
<caption>Table 8-84. Fast Throttle Trigger Capability Structure Fieldsª</caption>
<tr>
<th>Field Name</th>
<th>DWORD &amp; Bit Location</th>
<th>Standard Security Asset Class IDb</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>Version</td>
<td>0 [7:0]</td>
<td>17</td>
<td>RO</td>
<td>Capability Structure Version This field indicates the version of this capability structure. This field has a value of 00h in this specification.</td>
</tr>
<tr>
<td>Management Capability ID</td>
<td>0 [29:16]</td>
<td>17</td>
<td>RO</td>
<td>Management Capability ID This field specifies the Capability ID of this Management Capability structure. The Fast Throttle Trigger Capability structure has a Management Capability ID of 007h.</td>
</tr>
<tr>
<td>Fast Throttle Signal Capability Address Low</td>
<td>1</td>
<td>17</td>
<td>RO</td>
<td>Fast Throttle Signal Capability Address Low $\begin{array}{} { \text { Lower } 3 2 \text { bits of the pointer to the base address of the } } \\ { \text { signal capability structure. } } \end{array}$ This points to a signal capability structure that can be either Open Drain or Vendor-defined type. The UCIe Standard is to use Open Drain type. Because capability structures must be DWORD-aligned, bits [1:0] must be 00b.</td>
</tr>
<tr>
<td>Fast Throttle Signal Capability Address High</td>
<td>2</td>
<td>17</td>
<td>RO</td>
<td>Fast Throttle Signal Capability Address High Upper 32 bits of the pointer to the base address of the signal capability structure. This points to a signal capability structure that can be either Open Drain or Vendor-defined type. The UCIe Standard is to use Open Drain type.</td>
</tr>
<tr>
<td>Number of Fast Throttle Trigger Capabilities (N)</td>
<td>3 [4:0]</td>
<td>17</td>
<td>RO</td>
<td>Number of Fast Throttle Trigger Capabilities (N) This field identifies the number of Fast Throttle Trigger capabilities that this management endpoint supports to trigger Fast Throttle. 0h: No Fast Throttle Trigger capabilities are supported. 1h - 1Fh: Up to 31 Fast Throttle Trigger capabilities are supported.</td>
</tr>
<tr>
<td>$\begin{array}{} { \text { Fast Inrottie } } \\ { \text { Trigger Capability } } \end{array}$</td>
<td></td>
<td>17</td>
<td>RO</td>
<td>Fast Throttle Trigger Capability One Fast Throttle Trigger Capability entry is added per Fast Throttle Trigger supported. A Fast Throttle Trigger capability is described by a combination of Fast Throttle Trigger Type and the associated attributes. Figure 8-74 and Table 8-85 specify the field definitions and format.</td>
</tr>
</table>

a. If a Power Management Element supports both Fast Throttle Trigger and Response capabilities using a bidirectional signal, then
the address to the Fast Throttle signal capability structure in the Fast Throttle Trigger and Response Capability structures must
be identical.

b. See Table 8-7 for a description of Standard Security Asset Class IDs.

<table>
<caption>Table 8-85. Fast Throttle Trigger Capability Format</caption>
<tr>
<th>Field Name</th>
<th>DWORD &amp; Bit Location</th>
<th>$\begin{array}{} { \text { Standard } } \\ { \text { Security } } \\ { \text { Asset } } \end{array}$ $\mathrm { c l a s s } \mathrm { I D } ^ { \mathrm { a } }$</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>Fast Throttle Trigger Type</td>
<td>$0 \left[ 4 : 0 \right]$</td>
<td>17</td>
<td>RO</td>
<td>Fast Throttle Trigger Type Defines the Fast Throttle Trigger type. See Table 8-86 for Fast Throttle Trigger Type encoding.</td>
</tr>
<tr>
<td>Vendor-defined Fast Throttle Trigger Attributes</td>
<td>$0 \left[ 3 1 : 1 6 \right]$</td>
<td>17</td>
<td>RO</td>
<td>Vendor-defined Fast Throttle Trigger Attributes Defines attributes for the Fast Throttle Trigger. Fast Throttle Trigger Type plus its attributes define a unique Fast Throttle Trigger.</td>
</tr>
</table>

a. See Table 8-7 for a description of Standard Security Asset Class IDs.

The following are examples of how a Fast Throttle Trigger can be defined:

· Fast Throttle Trigger Type=1, Vendor-defined Fast Throttle Trigger Type = Average power,
Sampling period = 1 ms

· Fast Throttle Trigger Type=0, Vendor-defined Fast Throttle Trigger Attributes = Maximum
temperature, Temperature zone = Chiplet

<table>
<caption>Table 8-86. Fast Throttle Trigger Type Encoding</caption>
<tr>
<th>Fast Throttle Trigger Type</th>
<th>Encoding Definition</th>
</tr>
<tr>
<td>00h</td>
<td>Temperature</td>
</tr>
<tr>
<td>01h</td>
<td>Power</td>
</tr>
<tr>
<td>02h</td>
<td>Current</td>
</tr>
<tr>
<td>03h - 17h</td>
<td>Reserved</td>
</tr>
<tr>
<td>18h - 1Fh</td>
<td>Vendor-defined Types</td>
</tr>
</table>

## 8.4.2.1.2.2 Fast Throttle Response Capability Structure

This section defines the actions that could be taken in response to Fast Throttle assertion and de-
assertion. During initialization, the Power Management Director will select the action to be taken by
this Power Management Element when Fast Throttle assertion or de-assertion occurs (see Figure 8-75
and Table 8-87).

<table>
<caption>Figure 8-75. Fast Throttle Response Capability Structure</caption>
<tr>
<th colspan="8">+3</th>
<th colspan="8">+2</th>
<th colspan="8">+1</th>
<th colspan="7">+0</th>
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
<th>211</th>
<th>10</th>
<th>9</th>
<th></th>
<th>87</th>
<th>6</th>
<th>543210</th>
<th></th>
<th></th>
<th></th>
<th></th>
</tr>
</table>

<figure>

DWORD 0

DWORD 1

DWORD 2

DWORD 3

DWORD 4

DWORD 5

DWORD 6

DWORD 7

...

...

DWORD

$2 \left( M - 1 \right) + 4$

DWORD

2(M-1)+5

</figure>

<table>
<caption>Figure 8-76. Fast Throttle Response State Format</caption>
<tr>
<th>Rsvd</th>
<th>Management Capability ID Reserved</th>
<th>Version</th>
</tr>
<tr>
<td colspan="3">Fast Throttle Signal Capability Address Low</td>
</tr>
<tr>
<td colspan="3">Fast Throttle Signal Capability Address High</td>
</tr>
<tr>
<th></th>
<th>Reserved</th>
<th>Number of Fast Throttle Response States (M)</th>
</tr>
<tr>
<td colspan="3">Fast Throttle Response State (0)</td>
</tr>
<tr>
<td></td>
<td>Fast Throttle Response State (1)</td>
<td></td>
</tr>
<tr>
<td></td>
<td>…</td>
<td></td>
</tr>
<tr>
<td colspan="3">Fast Throttle Response State (M-1)</td>
</tr>
<tr>
<td></td>
<td></td>
<td></td>
</tr>
</table>

<table>
<tr>
<th colspan="8">+3</th>
<th colspan="8">+2</th>
<th colspan="8">+1</th>
<th colspan="8">+0</th>
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
<th>1109876543210</th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
</tr>
</table>

DWORD 0

Reserved

$\begin{array}{} { \text { Fast Throuue } } \\ { \text { Response State } } \\ { \text { ID } } \end{array}$

DWORD 1

Vendor-defined Fast Throttle Response State Attributes

<table>
<caption>Table 8-87. Fast Throttle Response Capability Structure Fieldsª (Sheet 1 of 2)</caption>
<tr>
<th>Field Name</th>
<th>DWORD &amp; Bit Location</th>
<th>Standard Security Asset Class IDb</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>Version</td>
<td>0 [7:0]</td>
<td>17</td>
<td>RO</td>
<td>Capability Structure Version This field indicates the version of this capability structure. This field has a value of 00h in this specification.</td>
</tr>
<tr>
<td>Management Capability ID</td>
<td>0 [29:16]</td>
<td>17</td>
<td>RO</td>
<td>$\begin{array}{} { \text { This field specifies the Capability ID of this Managemen } } \\ { \text { Capability structure. } } \end{array}$ The Fast Throttle Response Capability structure has a Management Capability ID of 008h.</td>
</tr>
<tr>
<td>Fast Throttle Signal Capability Address Low</td>
<td>1</td>
<td>17</td>
<td>$R O$</td>
<td>Fast Throttle Signal Capability Address $\begin{array}{} { \text { Lower } 3 2 \text { bits of the pointer to the base address of the } } \\ { \text { signal capability structure. } } \end{array}$ This points to a signal capability structure that can be either Open Drain or Vendor-defined type. The UCIe Standard is to use Open $\begin{array}{} { \text { Because capability structures must be DWORD-aligned } } \\ { \text { bits } \left[ 1 : 0 \right] \text { must be O0b } } \end{array} ,$</td>
</tr>
</table>

<table>
<caption>Table 8-87. Fast Throttle Response Capability Structure Fieldsa (Sheet 2 of 2)</caption>
<tr>
<th>Field Name</th>
<th>DWORD &amp; Bit Location</th>
<th>$\begin{array}{} { \text { Standard } } \\ { \text { Securitiy } } \end{array}$ $I D ^ { b }$</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>Fast Throttle Signal Capability Address High</td>
<td>2</td>
<td>17</td>
<td>RO</td>
<td>Fast Throttle Signal Capability Address High $\begin{array}{} { \text { Upper } 3 2 \text { bits of the pointer to the base address of the } } \\ { \text { signal capability structure. } } \end{array}$ be $\begin{array}{} { \text { This points to a signal capandy sunuucuue ucue vacue } } \\ { \text { either open Drain or vendor-defined type. The UCIe } } \\ { \text { Standard is to use Open Drain type. } } \end{array}$</td>
</tr>
<tr>
<td>Number of Fast Throttle Response States (M)</td>
<td>$3 \left[ 4 : 0 \right]$</td>
<td>17</td>
<td>$R O$</td>
<td>Number of Fast Throttle Response States (M) $\begin{array}{} { \text { This field id entifies the numb } } \\ { \text { States that this management } } \end{array}$ of Fast Throttle Response element supports to respond to Fast Throttle. $O h : N o \quad F a s t \quad T h r o t t l e \quad R e s p o n s e \quad S t a t e s \quad a r e \quad s u p p o r t e d .$ supported.</td>
</tr>
<tr>
<td>Fast Throttle Response State &lt;0:M-1&gt;</td>
<td>4 to 2(M-1)+5</td>
<td>17</td>
<td>RO</td>
<td>Fast Throttle Response State $\begin{array}{} { \text { One Fast Throttle Response State entry \left(each of whict } } \\ { \left. \text { consists of two } D W O R D s \right) \text { is defined for each response } } \end{array}$ state supported. $\begin{array}{} \text { The Power Management Director canr use any criteria } \\ \text { including the attributes to select which Fast } \text { Throttle } \\ \text { Response State to select at initialization . If the Number } \end{array}$ of Fast Throttle Response States is 0, then none of these structures need to be specified. A Fast Throttle Response State is described by a combination of Fast Throttle Response State ID and the associated attributes. See Figure 8-76 and Table 8-88 for Fast Throttle Response State field definitions and format.</td>
</tr>
</table>

a. If a Power Management Element supports both Fast Throttle Trigger and Response capabilities using a bidirectional signal, then
the address to the Fast Throttle signal capability structure in the Fast Throttle Trigger and Response Capability structures must
be identical.

b. See Table 8-7 for a description of Standard Security Asset Class IDs.

<table>
<caption>Table 8-88. Fast Throttle Response State Format</caption>
<tr>
<th>Field Name</th>
<th>DWORD &amp; Bit Location</th>
<th>Standard Security $\mathrm { c l a s s } I D ^ { \varepsilon }$</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>Fast Throttle Response State ID</td>
<td>0 [4:0]</td>
<td>17</td>
<td>RO</td>
<td>Fast Throttle Response State ID This is an enumeration of the Fast Throttle Response States that are supported by the Power Management Element. The Power Management Director will select one of these response states and update the Response Control structure.</td>
</tr>
<tr>
<td>Vendor-defined Fast Throttle Response State Attributes</td>
<td>1 [31:0]</td>
<td>17</td>
<td>RO</td>
<td>Vendor-defined Fast Throttle Response State Attributes These attributes can be used to specify characteristics of the response state.</td>
</tr>
</table>

a. See Table 8-7 for a description of Standard Security Asset Class IDs.

The following are examples of how a Fast Throttle Response State can be defined and selected:

. Fast Throttle Response State ID=1, Vendor-defined Fast Throttle Response State Attributes =
Lowest operational state for all clocks, Entry latency = 100 us, Exit Latency = 1 ms, Exit slow
ramp enabled

· Fast Throttle Response State ID=2, Vendor-defined Fast Throttle Response State Attributes =
Lowest operational state for low-priority compute entity, Entry $l a t e n c y = 5 0 \quad u s ,$ Exit latency = 1
ms, Exit slow ramp enabled

## 8.4.2.1.2.3 Fast Throttle Logging Capability Structure

This section defines a Power Management Element's capability to log the throttle events triggered or
received (see Figure 8-77 and Table 8-89).

<table>
<caption>Figure 8-77. Fast Throttle Logging Capability Structure</caption>
<tr>
<th colspan="6">+3</th>
<th colspan="2"></th>
<th colspan="8">+2</th>
<th colspan="8">+1</th>
<th colspan="8">+0</th>
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
<th></th>
<th></th>
<th></th>
<th></th>
<th>76543210</th>
<th></th>
<th></th>
<th></th>
</tr>
<tr>
<td colspan="2">Rsvd</td>
<td></td>
<td></td>
<td></td>
<td colspan="3">Management</td>
<td></td>
<td></td>
<td>Capability</td>
<td></td>
<td>ID</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td colspan="3">Reserved</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>Version</td>
<td></td>
<td></td>
<td></td>
</tr>
</table>

<figure>

DWORD 0

Number of Fast
Throttle Logging
Capabilities $\left( L \right)$

DWORD 1

Reserved

DWORD 2

Fast Throttle Logging Structure Address Low

DWORD 3

Fast Throttle Logging Structure Address High

DWORD 4

Fast Throttle Logging Capability (0)

DWORD 5

Fast Throttle Logging Capability (1)

...

...

DWORD
L+3

Fast Throttle Logging Capability (L-1)

</figure>

<table>
<caption>Figure 8-78. Fast Throttle Logging Capability Format</caption>
<tr>
<th></th>
<th colspan="7">+3</th>
<th colspan="8">+2</th>
<th colspan="8">+1</th>
<th colspan="8">+0</th>
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
<th>109876543210</th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
</tr>
</table>

DWORD

Fast Throttle Logging Capability Attributes

Reserved

Fast Throttle
Logging
Capability Type

<table>
<caption>Table 8-89. Fast Throttle Logging Capability Fields (Sheet 1 of 2)</caption>
<tr>
<th>Field Name</th>
<th>DWORD &amp; Bit Location</th>
<th>$\begin{array}{} { \text { Standard } } \\ { \text { Security } } \\ { \text { Asset } } \end{array}$ Class IDª</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>Version</td>
<td>0 [7:0]</td>
<td>17</td>
<td>RO</td>
<td>Capability Structure Version This field indicates the version of this capability structure. This field has a value of 00h in this specification.</td>
</tr>
<tr>
<td>Management Capability ID</td>
<td>0 [29:16]</td>
<td>17</td>
<td>RO</td>
<td>Management Capability ID This field specifies the Capability ID of this Management Capability structure. The Fast Throttle Logging Capability structure has a Management Capability ID of 009h.</td>
</tr>
<tr>
<td>Number of Fast Throttle Logging $\mathrm { C a p a b i l i t i e s } \left( \mathrm { L } \right)$</td>
<td>$1 \left[ 4 : 0 \right]$</td>
<td>17</td>
<td>$R O$</td>
<td>Number of Fast Throttle Logging Capabilities (L) $\begin{array}{} { \text { Number of Fast Throttle logging capabilities that are } } \\ { \text { supported by the Power Managemement Element. } } \end{array}$ 00h: No Fast Throttle logging capabilities are supported. 01h - 1Fh: Up to 31 Fast Throttle logging capabilities are supported.</td>
</tr>
</table>

<table>
<caption>Table 8-89. Fast Throttle Logging Capability Fields (Sheet 2 of 2)</caption>
<tr>
<th>Field Name</th>
<th>DWORD &amp; Bit Location</th>
<th>$\begin{array}{} { \text { Standard } } \\ { \text { Security } } \\ { \text { Asset } } \end{array}$</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>Fast Throttle Logging Structure Address Low</td>
<td>2</td>
<td>17</td>
<td>RO</td>
<td>Fast Throttle Logging Structure Address Low Lower 32 bits of the pointer to the base address of the Fast Throttle Logging structure defined in Section 8.4.2.1.4. Because capability structures must be DWORD-aligned, bits [1:0] must be 00b.</td>
</tr>
<tr>
<td>Fast Throttle Logging Structure Address High</td>
<td>3</td>
<td>17</td>
<td>$R O$</td>
<td>Fast Throttle Logging Structure Address High Upper 32 bits of the pointer to the base address of the Fast Throttle Logging structure defined in Section 8.4.2.1.4.</td>
</tr>
<tr>
<td>Fast Throttle Logging Capability &lt;0:L-1&gt;</td>
<td>$4 \quad t o \quad L + 3$</td>
<td>17</td>
<td>$R O$</td>
<td>Fast Throttle Logging Capability $\begin{array}{} { \text { One Fast Throttle logging capability entry is defined for } } \\ { \text { each Fast Throttle loaqing capability suported. } } \end{array}$ A logging capability is described by a combination of Fast Throttle Logging Capability Type and the associated attributes. Figure 8-78 and Table 8-90 specify the field definitions and format.</td>
</tr>
</table>

a. See Table 8-7 for a description of Standard Security Asset Class IDs.

<table>
<caption>Table 8-90. Fast Throttle Logging Capability Format</caption>
<tr>
<th>Field Name</th>
<th>DWORD &amp; Bit Location</th>
<th>$\begin{array}{} { \text { Standard } } \\ { \text { Security } } \\ { \text { Asset } } \end{array}$ Class IDª</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>$F a s t \quad T h r o t t l e$ Logging Capability Type</td>
<td>0 [4:0]</td>
<td>17</td>
<td>RO</td>
<td>Fast Throttle Logging Capability Type This field defines type of the Fast Throttle Logging capability. See Table 8-91 for Fast Throttle Logging Capability types.</td>
</tr>
<tr>
<td>Fast Throttle Logging Capability Attributes</td>
<td>$0 \left[ 3 1 : 1 6 \right]$</td>
<td>17</td>
<td>RO</td>
<td>Fast Throttle Logging Capability Attributes This field defines attributes for the Fast Throttle Logging Capability type. See Table 8-91 for a list of Fast Throttle Logging Capability types and the associated attributes.</td>
</tr>
</table>

a. See Table 8-7 for a description of Standard Security Asset Class IDs.

<table>
<caption>Table 8-91. Fast Throttle Logging Capability Types</caption>
<tr>
<th>Logging Capability Type</th>
<th>Logging Capability</th>
<th>Description</th>
<th>Attributes</th>
</tr>
<tr>
<td>000h</td>
<td>Trigger Count Logging Capability</td>
<td>The number of times Fast Throttle Trigger was asserted by this Power Management Element. Free-running counter, saturates at maximum value.</td>
<td rowspan="2"></td>
</tr>
<tr>
<td>001h</td>
<td>$\begin{array}{} { \text { Trigger Duration } } \\ { \text { Logging Capability } } \end{array}$</td>
<td>The cumulative duration for which Fast Throttle Trigger was asserted by this Power Management Element. Defined in microseconds. Free-running counter, saturates at maximum value.</td>
</tr>
<tr>
<td>$0 0 2 h$</td>
<td>$\begin{array}{} { \text { Trigger Vector } } \\ { \text { Logging Capabilit } } \end{array}$</td>
<td>Vector of which Fast Throttle Trigger capabilities caused assertion of the Trigger from this Power Management Element. $\begin{array}{} { \text { Defined as a sticky \left(until explicitly cleared\right) bit vector with one bit allocate } } \\ { \text { to each Fast Throttle Trigger Typer supported by the Power Mangemement } } \end{array}$ Element in the Fast Throttle Trigger 0. $\begin{array}{} { \text { Up to 31 possible Fast Throttle Triggers can be logged. } } \\ { \text { Bits } \left[ 6 3 : 3 1 \right] \text { of the corresponding logging register arererved. } } \end{array} .$</td>
<td>RW</td>
</tr>
<tr>
<td>003h</td>
<td>Response Count Logging Capability</td>
<td>The number of times this Power Management Element responded to Fast Throttle. The Fast Throttle may have been generated by this Power Management Element itself or a different Power Management Element on the SiP. Free-running counter, saturates at maximum value.</td>
<td></td>
</tr>
<tr>
<td>004h</td>
<td>Response Duration $L o g g i n g \quad C a p a b i l i t y$</td>
<td>The cumulative duration for which this Power Management Element responded to Fast Throttle. The Fast Throttle may have been generated by this Power Management Element itself or a different Power Management Element on the SiP. $\begin{array}{} { \text { Derined in microseconds. } } \\ { \text { Free-running counter, saturates at maximum value. } } \end{array} .$</td>
<td></td>
</tr>
<tr>
<td>005h - 017h</td>
<td>Reserved</td>
<td></td>
<td>RO</td>
</tr>
<tr>
<td>018h - 01Fh</td>
<td>Vendor-defined</td>
<td></td>
<td>Vendor- defined</td>
</tr>
</table>

## $8 . 4 . 2 . 1 . 3$ Fast Throttle Control Structures

### 8.4.2.1.3.1 Fast Throttle Trigger Control Structure

Figure 8-79 and Table 8-92 define the trigger controls per Power Management Element. Power
Management Director will program this to enable zero or more Throttle triggers advertised by the
element in the capability structure. For each of the throttle triggers, the Power Management Director
should program the entry and exit threshold for the trigger to assert.

<table>
<caption>Figure 8-79. Fast Throttle Trigger Control Structure</caption>
<tr>
<th rowspan="2"></th>
<th colspan="6"></th>
<th colspan="7"></th>
<th colspan="4"></th>
<th colspan="2"></th>
<th colspan="7"></th>
</tr>
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
<th>$1 0 9 8 7 6 5 4 3 2 1 0$</th>
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
<td>DWORD 0</td>
<td colspan="4"></td>
<td></td>
<td></td>
<td></td>
<td colspan="9">Fast Throttle Min Assertion Time</td>
<td></td>
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
<td>DWORD 1</td>
<td></td>
<td></td>
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
</tr>
<tr>
<td>DWORD 2</td>
<td></td>
<td></td>
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
</tr>
<tr>
<td>DWORD 3</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td colspan="8">Fast Throttle Trigger Control 0</td>
<td></td>
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
<td>....</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
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
<td>DWORD 8</td>
<td></td>
<td></td>
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
</tr>
<tr>
<td>DWORD 9</td>
<td></td>
<td></td>
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
</tr>
<tr>
<td>DWORD 10</td>
<td></td>
<td></td>
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
</tr>
<tr>
<td>...</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td colspan="8">Fast Throttle Trigger Control 1</td>
<td></td>
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
<td>DWORD 15</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
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
<td>DWORD 16</td>
<td></td>
<td></td>
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
<td colspan="3"></td>
<td colspan="2"></td>
<td colspan="3">...</td>
<td></td>
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
<td>DWORD $8 \left( N - 1 \right) + 1$</td>
<td></td>
<td></td>
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
</tr>
<tr>
<td>DWORD $8 \left( N - 1 \right) + 2$</td>
<td></td>
<td></td>
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
</tr>
<tr>
<td>...</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td colspan="6">Fast Throttle Trigger Control N-1</td>
<td></td>
<td></td>
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
<td rowspan="2">DWORD $8 \left( N - 1 \right) + 7$</td>
<td rowspan="2"></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td rowspan="2"></td>
<td></td>
<td colspan="2" rowspan="2"></td>
<td></td>
<td></td>
<td></td>
<td></td>
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
</tr>
<tr>
<td>DWORD</td>
<td></td>
<td></td>
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
</tr>
<tr>
<td>$8 \left( N - 1 \right) + 8$</td>
<td></td>
<td></td>
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
</tr>
</table>

<figure>
</figure>

Figure 8-80 shows the Fast Throttle Trigger Control format.

<table>
<caption>Figure 8-80. Fast Throttle Trigger Control Format</caption>
<tr>
<th></th>
<th colspan="6">+3</th>
<th colspan="8">+2</th>
<th colspan="8">+1</th>
<th colspan="8">+0</th>
</tr>
<tr>
<th>31</th>
<th>30</th>
<th>29 28</th>
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
<th>9876543210</th>
<th></th>
</tr>
</table>

<figure>

DWORD 0

En

Reserved

Threshold
Encoding ID

DWORD 1

Entry Threshold

DWORD 2

Exit Threshold

DWORD 3

DWORD 4

Reserved

DWORD 5

DWORD 6

Vendor-defined Fast Throttle Trigger Controls

DWORD 7

</figure>

<table>
<caption>Table 8-92. Fast Throttle Trigger Control Fields</caption>
<tr>
<th>Field Name</th>
<th>DWORD &amp; Bit Location</th>
<th>Standard Security $\mathrm { c l a s s } \mathrm { I D } ^ { \bar { s } }$</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>Fast Throttle Min Assertion Time</td>
<td>0</td>
<td>16</td>
<td>RW</td>
<td>Fast Throttle Min Assertion Time (us) Defines the minimum time for which the Fast Throttle should be asserted. If any enabled trigger condition is met then the Fast Throttle is asserted and the minimum assertion time begins. When all enabled trigger conditions are de-asserted and the minimum assertion time has been met, then the Fast Throttle will de-assert. Fast Throttle assertion time from the chiplet should be greater than OR equal to the minimum assertion time. Figure 8-82 shows an example of this.</td>
</tr>
<tr>
<td>Fast Throttle Trigger Control &lt;0:N-1&gt;</td>
<td>$\begin{array}{} { 1 \text { to } } \\ { 8 \left( N - 1 \right) + 8 } \end{array}$</td>
<td>16</td>
<td>RW</td>
<td>Fast Throttle Trigger Control &lt;0:N-1&gt; Defines the enable and other controllable fields for a Fast Throttle Trigger capability.b N:0-Up to 30; for each Fast Throttle Trigger capability supported. Each Fast Throttle Trigger Control structure consists of eight DWORDs. Figure 8-80 and Table 8-93 specify the field definitions and format.</td>
</tr>
</table>

a. See Table 8-7 for a description of Standard Security Asset Class IDs.

b. The Power Management Director can enable zero or more of the Fast Throttle Trigger controls in the Power Management Element.

<table>
<caption>Table 8-93. Fast Throttle Trigger Control Format</caption>
<tr>
<th>Field Name</th>
<th>DWORD &amp; Bit Location</th>
<th>Standard Security Asset Class IDª</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>$\begin{array}{} { \text { Threshold } } \\ { \text { Encoding ID } } \end{array}$</td>
<td>$0 \left[ 4 : 0 \right]$</td>
<td>16</td>
<td>RW</td>
<td>Threshold Encoding ID See Table 8-94 for Fast Throttle Trigger Threshold encodings. These units apply to the Entry and Exit Thresholds specified in this structure.</td>
</tr>
<tr>
<td>$E n$</td>
<td>0 [31]</td>
<td>16</td>
<td>RW</td>
<td>Enable Enables the Fast Throttle Trigger Type.</td>
</tr>
<tr>
<td>Entry Threshold</td>
<td>$1 \left[ 3 1 : 0 \right]$</td>
<td>16</td>
<td>RW</td>
<td>Entry Thresholdb c Defines the Entry threshold for Fast Throttle Trigger assertion.</td>
</tr>
<tr>
<td>Exit Threshold</td>
<td>$2 \left[ 3 1 : 0 \right]$</td>
<td>16</td>
<td>RW</td>
<td>Exit Thresholdb c Defines the Exit threshold for Fast Throttle Trigger de- assertion.</td>
</tr>
<tr>
<td>Vendor-defined Fast Throttle Trigger Controls</td>
<td>5, 6, 7</td>
<td>16</td>
<td>RW</td>
<td>Vendor-defined Fast Throttle Trigger Controls Vendor-defined Fast Throttle Trigger controls.</td>
</tr>
</table>

a. See Table 8-7 for a description of Standard Security Asset Class IDs.

b. The Power Management Director should configure the Entry and Exit Thresholds. If the throttle condition is enabled, a Power
Management Element would assert this Fast Throttle Trigger when the Entry Threshold is exceeded; the Power Management
Element would de-assert this Fast Throttle Trigger when the minimum assertion time has been met, and the condition drops back
to below the Exit Threshold.

c. References to Entry Threshold or Exit Threshold in this document (when discussing Fast Throttle) assume that Fast Throttle is
asserted when one or more trigger values exceed (>) the respective Entry Threshold(s) and is de-asserted when all the Fast
Throttle Triggers are below (<) their respective Exit Threshold(s). Vendor implementations may choose to use other definitions
of comparison against Entry/Exit Thresholds for Fast Throttle assertion/de-assertion and use vendor-defined attribute bits in the
Fast Throttle Trigger Capability structure to specify the same.

<table>
<caption>Table 8-94. Fast Throttle Threshold Encoding ID</caption>
<tr>
<th>Threshold Encoding ID</th>
<th>Encoding Definition</th>
</tr>
<tr>
<td>00h - 1Fh</td>
<td>Vendor-defined encoding</td>
</tr>
</table>

<figure>
<figcaption>Figure 8-81. Fast Throttle Trigger Assertion and De-assertionª</figcaption>

Trigger 0 >
Entry_Threshold_0

Set
RS Flip
Flop

Trigger 0 <
Exit_Threshold_0

Clr

Trigger 1 >
Entry_Threshold_1

Set

RS Flip
Flop
Clr

Trigger 1 <
Exit_Threshold_1

Set
RS Flip
Flop

Chiplet Fast
Throttle

Trigger n >
Entry_Threshold_n

Set
RS Flip
Flop
Clr

Clr

Throttle Min
Assertion Time Met

Trigger n <
Exit_Threshold_n

</figure>

a. Entry/ Exit triggers could be generated across more than one Power Management Elements within a chiplet. However, they may
be combined to generate one final Fast Throttle output from the chiplet as per the logic shown.

<figure>
<figcaption>Figure 8-82. Chiplet Fast Throttle Assertion and De-assertion Timing</figcaption>

Chiplet A

Throttle Trigger 1 Throttle Trigger 0

Chiplet A

...

..

...

...

..

...

...

...

...

...

...

Chiplet A
Throttle Trigger N

Chiplet A
Fast Throttle

Output

Minimum Assertion
Time

Minimum Assertion
Time

Any trigger meeting the
assertion criteria results in
Throttle Trigger assertion

All triggers must meet de-
assertion criteria for Throttle
Triggerto de-assert

</figure>

## 8.4.2.1.3.2 Fast Throttle Response Control Structure

This structure defines the Fast Throttle response controls per Power Management Element. Power
management will respond to the Fast Throttle assertion based on these controls (see Figure 8-83 and
Table 8-95).

<table>
<caption>Figure 8-83. Fast Throttle Response Control Structure</caption>
<tr>
<th colspan="8">+3</th>
<th colspan="8">+2</th>
<th></th>
<th colspan="7">+1</th>
<th colspan="8">+0</th>
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
<th>09876543210</th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
</tr>
</table>

<figure>

DWORD 0

Fast Throttle
Response State
ID

En

Reserved

DWORD 1

Vendor-defined Fast Throttle Response State Controls

</figure>

<table>
<caption>Table 8-95. Fast Throttle Response Control Fields</caption>
<tr>
<th>Field Name</th>
<th>DWORD &amp; Bit Location</th>
<th>Standard Security $\mathrm { c l a s s } \mathrm { I D } ^ { \bar { s } }$</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>Fast Throttle Response State ID</td>
<td>$0 \left[ 4 : 0 \right]$</td>
<td>16</td>
<td>RW</td>
<td>Fast Throttle Response State IDb This field sets the selected Fast Throttle Response State ID that the Power Management Element should go to in response to the Fast Throttle Trigger.</td>
</tr>
<tr>
<td>$E n$</td>
<td>0 [31]</td>
<td>16</td>
<td>RW</td>
<td>Enable Set to enable this Fast Throttle Response State ID.</td>
</tr>
<tr>
<td>Vendor-defined Fast Throttle Response State Controls</td>
<td>1</td>
<td>16</td>
<td>$R W$</td>
<td>Vendor-defined Fast Throttle Response State Controlsc This field specifies control options necessary for the Fast Throttle response.</td>
</tr>
</table>

a. See Table 8-7 for a description of Standard Security Asset Class IDs.

b. The Power Management Director-selected Fast Throttle Response State ID should be one of the State IDs advertised in the Fast
Throttle Response Capability structure.

c. Vendor-defined Fast Throttle Response State controls can be used to provide additional controllability (such as exit ramp rate)
for the response state.

## 8.4.2.1.3.3 Fast Throttle Logging Control Structure

This section defines the control structure for configuring Fast Throttle logging in a Power Management
Element (see Figure 8-84 and Table 8-96).

The number of logging capabilities in this structure (L) matches the number of logging capabilities in
the Fast Throttle Logging Capability structure in Section 8.4.2.1.2.3. There is an in-order mapping of
each entry in the Fast Throttle Logging Control structure to each entry in the Fast Throttle Logging
Capability structure.

<table>
<caption>Figure 8-84. Fast Throttle Logging Control Structure</caption>
<tr>
<th rowspan="2"></th>
<th colspan="7">+3</th>
<th colspan="8">+2</th>
<th colspan="8">+1</th>
<th colspan="4">+0</th>
</tr>
<tr>
<th>31</th>
<th>30</th>
<th>29</th>
<th>28</th>
<th>27</th>
<th>26</th>
<th>25 24</th>
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
<th>11109876543210</th>
<th></th>
<th></th>
</tr>
<tr>
<td>DWORD0</td>
<td colspan="2"></td>
<td colspan="25">Fast Throttle Logging Enable</td>
</tr>
<tr>
<td>DWORD1</td>
<td colspan="2"></td>
<td colspan="18">Fast Throttle Logging Clear</td>
<td colspan="7"></td>
</tr>
<tr>
<td>DWORD 2</td>
<td colspan="2"></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td colspan="2"></td>
<td></td>
<td colspan="10">Fast Throttle Logging Control (0)</td>
<td></td>
<td colspan="2"></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td>DWORD 3</td>
<td colspan="2"></td>
<td colspan="23">Fast Throttle Logging Control (1)</td>
<td></td>
<td></td>
</tr>
<tr>
<td>...</td>
<td colspan="2"></td>
<td></td>
<td></td>
<td colspan="3"></td>
<td colspan="2"></td>
<td colspan="4"></td>
<td colspan="7">...</td>
<td></td>
<td colspan="3"></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td>DWORD L+1</td>
<td colspan="2"></td>
<td></td>
<td></td>
<td colspan="2"></td>
<td colspan="3"></td>
<td colspan="11">Fast Throttle Logging Control (L-1)</td>
<td colspan="4"></td>
<td></td>
<td></td>
<td></td>
</tr>
</table>

<figure>
</figure>

<table>
<caption>Figure 8-85. Fast Throttle Logging Control Format</caption>
<tr>
<th rowspan="2"></th>
<th colspan="8">+3</th>
<th colspan="7">+2</th>
<th colspan="8">+1</th>
<th colspan="7">+0</th>
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
<th>23 22</th>
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
</tr>
<tr>
<td>DWORD</td>
<td></td>
<td></td>
<td colspan="9">Vendor-defined Fast Throttle Logging</td>
<td colspan="4">Controls</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td colspan="4">Reserved</td>
<td></td>
<td></td>
<td></td>
<td colspan="2"></td>
</tr>
</table>

<table>
<caption>Table 8-96. Fast Throttle Logging Control Fields</caption>
<tr>
<th>Field Name</th>
<th>DWORD &amp; Bit Location</th>
<th>Standard Security $\mathrm { c l a s s } \mathrm { I D } ^ { \bar { s } }$</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>Fast Throttle Logging Enable</td>
<td>0</td>
<td>16</td>
<td>$R W$</td>
<td>Fast Throttle Logging Enable Enable bit vector for Fast Throttle logging capabilitiesb. When a bit is set, the corresponding logging capability is enabled. When a bit is cleared, the corresponding logging capability is disabled. One bit per logging capability as described in the Fast Throttle Logging Capability structure. [L-1:0]: Enable control for the L logging capabilities defined. [30:L]: Unused. [31]: Reserved.</td>
</tr>
<tr>
<td>Fast Throttle Logging Clear</td>
<td>1</td>
<td>16</td>
<td>RW</td>
<td>Fast Throttle Logging Clear Clear vector for Fast Throttle logging capabilities. One bit per logging capability as described in the Fast Throttle Logging Capability structure. [L-1:0]: Clear control for the L logging capabilities defined. Writing 1 to a bit in this vector clears the corresponding logging register. Reads return 0s. [30:L]: Unused. [31]: Reserved.</td>
</tr>
<tr>
<td>Fast Throttle Logging Control &lt;0:L-1&gt;</td>
<td>2 to L+1</td>
<td>16</td>
<td>RW</td>
<td>Fast Throttle Logging Control Control for each Fast Throttle logging capability. Figure 8-85 and Table 8-96 provide details of the Fast Throttle logging control format.</td>
</tr>
</table>

a. See Table 8-7 for a description of Standard Security Asset Class IDs.

b. The Power Management Director can enable zero or more of the Fast Throttle logging capabilities.

<table>
<caption>Table 8-97. Fast Throttle Logging Control Format</caption>
<tr>
<th>Field Name</th>
<th>DWORD &amp; Bit Location</th>
<th>Standard Security Asset Class IDª</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>Vendor-defined Fast Throttle Logging Controls</td>
<td>0 [31:16]</td>
<td>16</td>
<td>RW</td>
<td>Vendor-defined Fast Throttle Logging Controls Vendor-defined controls that are used to control the behavior of the Fast Throttle Logging capability.</td>
</tr>
</table>

a. See Table 8-7 for a description of Standard Security Asset Class IDs.

## 8.4.2.1.4 Fast Throttle Logging Structures

This section describes the logging structures that are used to maintain Fast Throttle logs based on the
logging capabilities and controls as defined in Section 8.4.2.1.2.3 and Section 8.4.2.1.3.3,
respectively.

The number of logging capabilities in this structure (L) matches the number of logging capabilities in
the Fast Throttle Logging Capability structure in Section 8.4.2.1.2.3. There is an in-order mapping of
each entry in the Fast Throttle Logging Control structure to each entry in the Fast Throttle Logging
Capability structure.

## 8.4.2.1.4.1 Fast Throttle Logging Structure

Fast Throttle logging registers should be reset to 0 on a chiplet reset.

<table>
<caption>Figure 8-86. Fast Throttle Logging Structure</caption>
<tr>
<th></th>
<th colspan="7">+3</th>
<th colspan="8">+2</th>
<th colspan="8">+1</th>
<th colspan="8">+0</th>
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
<th>9876543210</th>
<th></th>
</tr>
</table>

<figure>

DWORD 0

DWORD 1

Fast Throttle Log 0

DWORD 2

DWORD 3

Fast Throttle Log 1

...

…

DWORD

2L-2

$\begin{array}{} { \text { DWORD } } \\ { 2 L - 1 } \end{array}$

Fast Throttle Log L-1

</figure>

<table>
<caption>Table 8-98. Fast Throttle Logging Fields</caption>
<tr>
<th>Field Name</th>
<th>DWORD &amp; Bit Location</th>
<th>Standard Security Asset Class IDª</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>Fast Throttle Log&lt;0:L-1&gt;</td>
<td>0 to 2L-1</td>
<td>17</td>
<td>RO</td>
<td>Fast Throttle Log Fast Throttle Log entryb as defined by the Fast Throttle Logging Capability structure“. Each Fast Throttle Log is a 64-bit counterd. The first DWORD of the entry is the lower 32 bits of the 64- bit counter. The second DWORD of the entry is the upper 32 bits of the 64-bit counter. Controlled by Fast Throttle logging controls.</td>
</tr>
</table>

a. See Table 8-7 for a description of Standard Security Asset Class IDs.

b. For log entries associated with a Fast Throttle Logging Capability Type of 002h (Trigger Vector Logging Capability), if the log
register is cleared by software while the respective Fast Throttle Trigger is still asserted, the log bit should be set again.

c. The Power Management Director can enable one or more logging capabilities in the Fast Throttle Logging Control structure to
control these logs.

d. The Power Management Director can read these logs and take an action based on the recorded values as appropriate. For
example, as a response, the Power Management Director can choose to adjust the Fast Throttle Trigger controls.

## 8.4.2.1.5 Fast Throttle Address Map

This section describes the address map of all the structures related to Fast Throttle.
Figure 8-87. Fast Throttle Address Map

<figure>

FFFF_FFFF_FFFF_FFFFh

Fast Throttle
Logging
Structure

DW 2 (L-1), 2(L-1)+1

DW 2.3
DW 0. 1

For up to L Fast Throttle
Logs

Fast Throttle
Open Drain
Capability

Open drain signal capability (FT)

Fast Throttle Trigger Capability and Control

$D W \quad 8 \left( N - 1 \right) + 1 + O f f s e t$
to 8 (N-1)+8+Offset

For up to N Fast Throttle
Trigger Control

DW 1-8 + Offset

Fast Throttle Trigger
Control Offset (N+4)

DWO+Offset
DW N+3

DW4
DW3
DWZ high)
DW1 (OD Pointer low)
DWO

For Up to N Fast Throttle
Trigger Capabilities

Fast Throttle Open Drain
Capability Pointer

Capability Directory

Fast Throttle Trigger Capability

Fast Throttle Logging Capability

Fast Throttle Response Capability

Fast Throttle Response
Capability and Control

Fast Throttle
Response Control
Offset (2M+4)

$D W \quad 0 - 1 + O f f s e t$
$D W \quad 2 \left( M - 1 \right) + 4 , 2 \left( M - 1 \right) + 5$

7

Fast Throttle Response
Control

DW 4, 5
DW3
DW2 (OD Pointer high)
DW1 low)
DWO

For up to M Fast Throttle
Response States

Fast Throttle Open Drain
Capability Pointer

Fast Throttle Logging
Capability and Control

$D W \quad L + 1 + O f f s e t$

DW 2 + Offset
1 +
DW 0 + Offset
DW (L-1)+4
DW

For up to L Fast Throttle
Logging Controls

Fast Throttle Logging
Control Offset (L+4)

For up to L Fast Throttle
Logging Capabilities

DW3 (FT logging Pointer high)
DW2 (FT Logging Pointer low)
DWT
DWO

DW4

Fast Throttle Logging
Structure Pointer

0000_0000_0000_0000h

</figure>

## 8.4.2.2 Emergency Shutdown

### 8.4.2.2.1 Emergency Shutdown Overview

Emergency Shutdown is an optional feature that can be used to communicate the need for an
immediate shutdown response across chiplets in an SiP. This response is needed when a specified
shutdown threshold for the configured power management function (such as power or thermal) is
exceeded. Emergency Shutdown Threshold is defined as near or exceeding the maximum limit of
operation (such as temperature or power). The purpose of the Emergency Shutdown is to take
immediate action to prevent physical damage due to exceeding the maximum limits. Emergency
Shutdown is a fatal condition that requires immediate shutdown of the SiP and can only be exited on
reset. An example is when one or more chiplets of the SiP exceed the maximum operating
temperature, thereby requiring them to be powered off to prevent physical damage to those chiplets
or other chiplets in the SiP. A chiplet may respond to Emergency Shutdown by quickly entering a low-
power state and/or taking actions needed to more-cleanly shut down operation before power down.
The platform may respond to the Emergency Shutdown Indication by having the power supply power
down one or more power domains. Powering down these power domains may impact more of the
platform than just the SiP that signaled Emergency Shutdown.

Figure 8-88 shows an example of an SiP with Emergency Shutdown support.

<figure>
<figcaption>Figure 8-88. Example Use of Emergency Shutdown</figcaption>

Power Supply

Off SiP
Shutdown

SİP

PM Director

P

PM Element

P

PM Element

Chiplet -1

Bi-directional

Emergency

Shutdown
(Open Drain)

Chiplet -2

PM Element

PM Element

Chiplet -N-1

Chiplet -N

</figure>

Figure 8-88 shows an SiP with multiple chiplets. Each of these chiplets have one or more Power
Management Elements. It is permissible to have additional chiplets in the SiP without Power
Management Elements. One chiplet has the Power Management Director which is part of one of its
Power Management Elements. The Emergency Shutdown is communicated to all these chiplets using
a bidirectional Emergency Shutdown. The Emergency Shutdown is also communicated to the platform

by the Power Management Director. The platform can also indicate a need for Emergency Shutdown to
the SiP which the Power Management Director must pass along to the bidirectional Emergency
Shutdown.

Emergency Shutdown communication is recommended to be low latency and bidirectional in nature.
When Emergency Shutdown is triggered by a chiplet, the shutdown must be broadcast to all chiplets
with Emergency Shutdown response enabled. If platform notification is enabled, the shutdown may
also be sent to the platform for platform-level actions. All responding elements with Emergency
Shutdown enabled should take their configured Emergency Shutdown action in a timely manner to
prevent damage. A low-latency communication mechanism to all chiplets with Emergency Shutdown
response enabled must be provided. Open Drain signaling as described in Section 5.14 may be used
for this communication. Vendor-defined implementation of this signal may also be used. Open Drain is
UCIe preferred connection for interoperability between chiplets.

A Power Management Element may have either, both, or neither of Emergency Shutdown Trigger
capabilities and Emergency Shutdown Response capabilities. Based on the supported capabilities,
respective data structures and controls to configure these capabilities should be supported. Any
Power Management Element with Emergency Shutdown Trigger capability supported and enabled can
trigger Emergency Shutdown. Any Power Management Element with Emergency Shutdown Response
capability supported and enabled must respond to an incoming Emergency Shutdown trigger by
taking the configured action.

Emergency Shutdown Trigger generation is independent of Emergency Shutdown Response handling.
If both capabilities are enabled, a Power Management Element may trigger Emergency Shutdown
assertion from its end even if Emergency Shutdown is already asserted by some other chiplet in the
SiP. However, given that an Emergency Shutdown event requires reset of the SiP to be resolved, once
Emergency Shutdown is asserted by one or more Chiplets, assertion by any other Chiplets in the SiP
may not have any effect.

An Emergency Shutdown Trigger capable element:

· Advertises Trigger capability in its capability structure

· Supports Emergency Shutdown Trigger Control data structure to configure Emergency Shutdown
trigger behavior

· (Optionally) Supports logging to record trigger history

· Generates and communicates Emergency Shutdown when one or more trigger conditions are met

An Emergency Shutdown Response capable element:

· Advertises Emergency Shutdown Response Capability

· Supports response data structure to configure response on Emergency Shutdown assertion

· Responds to Emergency Shutdown by taking the configured action

Power Management Director:

· Enumerates the capabilities of power management entities discovered during SiP initialization

· Configures trigger and response controls

Power-on Defaults:

· The power-on default response to an Emergency Shutdown event is mapped to a specific
Response State (see Section 8.4.2.2.3.2). Every Power Management Element that supports
Emergency Shutdown Response Capability is required to support this state. This state may also
be defined to enable a platform notification functionality if a given chiplet supports it (typically a
chiplet which implements Power Management Director functionality).

There is provision for an implementation-specific Emergency Shutdown Trigger Override that can be
driven by the Chiplet before the full set of Emergency Shutdown Trigger Capabilities are discovered
and enabled (see Section 8.4.2.2.3.1).

The following data structures are defined for Emergency Shutdown:

· Emergency Shutdown Trigger Capability Structure

· Emergency Shutdown Response Capability Structure

· Emergency Shutdown Logging Capability Structure

· Emergency Shutdown Trigger Control Structure

· Emergency Shutdown Response Control Structure

· Emergency Shutdown Logging Control Structure

· Emergency Shutdown Logging Structure

<figure>
<figcaption>Figure 8-89. Overview of Emergency Shutdown Data Structures</figcaption>

FFFF_FFFF_FFFF_FFFFh

Emergency Shutdown Logging
Structure

Emergency Shutdown Open Drain
Signal Capability

Emergency Shutdown Trigger
Capability and Control

Capability Directory
Emergency Shutdown Trigger
Capability
Emergency Shutdown Logging
Capability
Emergency Shutdown Response
Capability

Emergency Shutdown Response
Capability and Control

Emergency Shutdown Logging
Capability and Control

0000_0000_0000_0000h

</figure>

## 8.4.2.2.2 Emergency Shutdown Capability Structures

### 8.4.2.2.2.1 Emergency Shutdown Trigger Capability Structure

This section defines Emergency Shutdown Trigger capabilities supported by the Power Management
Element (see Figure 8-90 and Table 8-99).

<table>
<caption>Figure 8-90. Emergency Shutdown Trigger Capability Structure</caption>
<tr>
<th rowspan="2"></th>
<th colspan="8">+3</th>
<th colspan="8">+2</th>
<th colspan="8">+1</th>
<th colspan="8">+0</th>
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
</table>

<figure>

DWORD 0

Rsvd

Management Capability ID

Reserved

Version

DWORD 1

Emergency Shutdown Signal Capability Address Low

DWORD 2

Emergency Shutdown Signal Capability Address High

Number of
Emergency
Shutdown Trigger
Capabilities (N)

DWORD 3

Reserved

DWORD 4

Emergency Shutdown Trigger Capability (0)

DWORD 5

Emergency Shutdown Trigger Capability (1)

...

...

DWORD

(N-1)+4

Emergency Shutdown Trigger Capability (N-1)

</figure>

<table>
<caption>Figure 8-91. Emergency Shutdown Trigger Capability Format</caption>
<tr>
<th colspan="8">+3</th>
<th colspan="8">+2</th>
<th colspan="8">+1</th>
<th colspan="8">+0</th>
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
<th>109876543210</th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
</tr>
</table>

DWORD

Vendor-defined Emergency Shutdown Trigger Attributes

Reserved

Emergency
Shutdown Trigger
Type

<table>
<caption>Table 8-99. Emergency Shutdown Trigger Capability Structure Fields (Sheet 1 of 2)</caption>
<tr>
<th>Field Name</th>
<th>DWORD &amp; Bit Location</th>
<th>Standard Security Asset Class IDª</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>Version</td>
<td>$0 \left[ 7 : 0 \right]$</td>
<td>17</td>
<td>RO</td>
<td>Capability Structure Version This field indicates the version of this capability structure. This field has a value of 00h in this specification.</td>
</tr>
<tr>
<td>Management Capability ID</td>
<td>0 [29:16]</td>
<td>17</td>
<td>RO</td>
<td>Management Capability ID This field specifies the Capability ID of this Management Capability structure. The Emergency Shutdown Trigger Capability structure has a Management Capability ID of 00Ah.</td>
</tr>
<tr>
<td>Emergency Shutdown Signal Capability Address Low</td>
<td>1</td>
<td>17</td>
<td>RO</td>
<td>Emergency Shutdown Signal Capability Address Low Lower 32 bits of the pointer to the base address of the Emergency Shutdown Signal Capability structure. This points to a signal capability structure that can be either Open Drain or Vendor-defined type. The UCIe Standard is to use Open Drain type. Because capability structures must be DWORD-aligned, bits [1:0] must be 00b.</td>
</tr>
</table>

<table>
<caption>Table 8-99. Emergency Shutdown Trigger Capability Structure Fields (Sheet 2 of 2)</caption>
<tr>
<th>Field Name</th>
<th>DWORD &amp; Bit Location</th>
<th>Standard Security Asset Class IDª</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>Emergency Shutdown Signal Capability Address High</td>
<td>2</td>
<td>17</td>
<td>RO</td>
<td>Emergency Shutdown Signal Capability Address High Upper 32 bits of the pointer to the base address of the Emergency Shutdown Signal Capability structure. This points to a signal capability structure that can be either Open Drain or Vendor-defined type. The UCIe Standard is to use Open Drain type.b</td>
</tr>
<tr>
<td>Number Of Emergency Shutdown Trigger Capabilities (N)</td>
<td>$3 \left[ 4 : 0 \right]$</td>
<td>17</td>
<td>$R O$</td>
<td>Number of Emergency Shutdown Trigger Capabilities (N) This field identifies the number of Emergency Shutdown Trigger capabilities that this management endpoint supports to trigger Emergency Shutdown. 0h: No Emergency Shutdown Trigger capabilities are supported. 1h - 1Fh: Up to 31 Emergency Shutdown Trigger capabilities are supported.</td>
</tr>
<tr>
<td>Emergency Shutdown Trigger Capability &lt;0:N-1&gt;</td>
<td>4 to $\left( N - 1 \right) + 4$</td>
<td>17</td>
<td>RO</td>
<td>Emergency Shutdown Trigger Capability One Emergency Shutdown Trigger Capability entry is added per Emergency Shutdown Trigger supported. Figure 8-91 and Table 8-100 specify the field definitions and format.</td>
</tr>
</table>

a. See Table 8-7 for a description of Standard Security Asset Class IDs.

b. If a Power Management Element supports both Emergency Shutdown Trigger and Response capabilities using a bidirectional
signal, then the address to the Emergency Shutdown Signal Capability structure in the Emergency Shutdown Trigger and
Response Capability structures must be identical.

<table>
<caption>Table 8-100. Emergency Shutdown Trigger Capability Format</caption>
<tr>
<th>Field Name</th>
<th>DWORD &amp; Bit Location</th>
<th>Standard Security Asset Class IDª</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>Emergency Shutdown Trigger Type</td>
<td>0 [4:0]</td>
<td>17</td>
<td>RO</td>
<td>Emergency Shutdown Trigger Type Defines the Emergency Shutdown Trigger type. See Table 8-101 for Emergency Shutdown Trigger Type encoding.</td>
</tr>
<tr>
<td>Vendor-defined Emergency Shutdown Trigger Attributes</td>
<td>0 [31:16]</td>
<td>17</td>
<td>RO</td>
<td>Vendor-defined Emergency Shutdown Trigger Attributes Defines attributes for the Emergency Shutdown Trigger. Emergency Shutdown Trigger type plus its attributes define a unique Emergency Shutdown Trigger.</td>
</tr>
</table>

a. See Table 8-7 for a description of Standard Security Asset Class IDs.

The following are examples of how an Emergency Shutdown Trigger can be defined:

· Emergency Shutdown Trigger Type=0, Vendor-defined Emergency Shutdown Trigger Attributes =
Maximum Temperature, Temperature Zone = Chiplet

· Emergency Shutdown Trigger Type=2, Vendor-defined Emergency Shutdown Trigger Attributes =
Peak Current, Sampling Rate = 1 us

<table>
<caption>Table 8-101. Emergency Shutdown Trigger Type Encoding</caption>
<tr>
<th>Emergency Shutdown Trigger Type</th>
<th>Encoding Definition</th>
</tr>
<tr>
<td>00h</td>
<td>Temperature</td>
</tr>
<tr>
<td>01h</td>
<td>Power</td>
</tr>
<tr>
<td>02h</td>
<td>Current</td>
</tr>
<tr>
<td>$0 3 h \quad - \quad 1 7 h$</td>
<td>Reserved</td>
</tr>
<tr>
<td>$1 8 h \quad - \quad 1 F h$</td>
<td>Vendor-defined Types</td>
</tr>
</table>

## 8.4.2.2.2.2 Emergency Shutdown Response Capability Structure

This section defines the actions that could be taken in response to Emergency Shutdown. During
initialization, the Power Management Director will select which of these actions will be taken by this
Power Management Element when Emergency Shutdown occurs (see Figure 8-92 and Table 8-102).

Note:
Responses to Emergency Shutdown are aimed at the following purposes:

· Take a faster local-level action while a more-global action (e.g., power rail shutdown) can be
taken by a higher-level entity such as the platform.

· Prepare the hardware for an impending power down cleanly. There could be different steps
specified that trade off what can be done to prepare the hardware vs. the amount of time that
takes.

<table>
<caption>Figure 8-92. Emergency Shutdown Response Capability Structure</caption>
<tr>
<th rowspan="2"></th>
<th colspan="8">+3</th>
<th colspan="8">+2</th>
<th colspan="8">+1</th>
<th colspan="8">+0</th>
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
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th>76543210</th>
<th></th>
</tr>
</table>

<figure>

DWORD 0

Rsvd

Management Capability ID

Reserved

Version

DWORD 1

Emergency Shutdown Signal Capability Address Low

DWORD 2

Emergency Shutdown Signal Capability Address High

Number of
Shutdown
Response States
(M)

DWORD 3

Reserved

DWORD 4

DWORD 5

Emergency Shutdown Response State (0)

DWORD 6

DWORD 7

Emergency Shutdown Response State (1)

...

...

DWORD
$2 \left( M - 1 \right) + 4$

DWORD
$2 \left( M - 1 \right) + 5$

Emergency Shutdown Response State (M-1)

</figure>

<table>
<caption>Figure 8-93. Emergency Shutdown Response State Format</caption>
<tr>
<th colspan="8">+3</th>
<th colspan="8">+2</th>
<th colspan="8">+1</th>
<th colspan="8">+0</th>
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
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th>876543210</th>
<th></th>
</tr>
</table>

DWORD 0

PN

Reserved

Emergency
Shutdown
Response State
ID

DWORD 1

Vendor-defined Emergency Shutdown Response State Attributes

<table>
<caption>Table 8-102. Emergency Shutdown Response Capability Structure Fieldsª (Sheet 1 of 2)</caption>
<tr>
<th>Field Name</th>
<th>DWORD &amp; Bit Location</th>
<th>Standard Security Asset Class IDb</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>Version</td>
<td>0 [7:0]</td>
<td>17</td>
<td>RO</td>
<td>Capability Structure Version This field indicates the version of this capability structure. This field has a value of 00h in this specification.</td>
</tr>
<tr>
<td>Management Capability ID</td>
<td>0 [29:16]</td>
<td>17</td>
<td>RO</td>
<td>Management Capability ID This field specifies the Capability ID of this Management Capability structure. The Emergency Shutdown Response Capability structure has a Management Capability ID of 00Bh.</td>
</tr>
<tr>
<td>Emergency Shutdown Signal Capability Address Low</td>
<td>1</td>
<td>17</td>
<td>$R O$</td>
<td>Emergency Shutdown Signal Capability Address Low Lower 32 bits of the pointer to the base address of the Emergency Shutdown Signal Capability structure. This points to a signal capability structure that can be either Open Drain or Vendor-defined type. The UCIe Standard is to $\begin{array}{} { \text { Because capability structures must be DWORD-aligned, bits } } \\ { \left[ 1 : 0 \right] \text { must be } 0 0 b } \end{array}$</td>
</tr>
<tr>
<td>Emergency Shutdown Signal Capability Address High</td>
<td>2</td>
<td>17</td>
<td>$R O$</td>
<td>$E m e r g e n c y \quad S h u t d o w n \quad S i g n a l \quad C a p a b i l i t y \quad A d d r e s s \quad H i g h$ $\begin{array}{} { \text { Upper } 3 2 \text { bits of the pointer to the base address of the } } \\ { \text { Emergency Shutdown Signal Capability structure. } } \end{array}$ $\begin{array}{} { \text { This points to a signal capability structure that can be eithel } } \\ { \text { Open Drain or Vendor-defined type. The Ucle Standard is tc } } \end{array}$ use Open Drain type.</td>
</tr>
</table>

<table>
<caption>Table 8-102. Emergency Shutdown Response Capability Structure Fieldsª (Sheet 2 of 2)</caption>
<tr>
<th>Field Name</th>
<th>DWORD &amp; Bit Location</th>
<th>Standard Security Asset Class IDb</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>Number Of Emergency Shutdown $\begin{array}{} { \text { Response States } } \\ { \left( M \right) } \end{array}$</td>
<td>$3 \left[ 4 : 0 \right]$</td>
<td>17</td>
<td>$R O$</td>
<td>Number of Emergency Shutdown Response States (M) This field identifies the number of Emergency Shutdown response states that this Management Element supports. If Emergency Shutdown Override is supported, at least one Emergency Shutdown Response State must be supported. 0h: No Emergency Shutdown Response States are supported. 1h - 1Fh: Up to 31 Emergency Shutdown Response States are supported.</td>
</tr>
<tr>
<td>$\mathrm { E m e r q e n c y }$ Shutdown Response State &lt;0:M-1&gt;</td>
<td>4 to $2 \left( M - 1 \right) + 5$</td>
<td>17</td>
<td>RO</td>
<td>Emergency Shutdown Response State One Emergency Shutdown Response State entry (each of of two DWORDs) is defined for each $\begin{array}{} \left. \text { Wnicn cons } \\ \text { Emergenc } \right) \end{array}$ Shutdown Response State supported. The Power Management Director can use any criteria including the attributes to select which Emergency Shutdown Response State to select at initialization. If the Number of Emergency Shutdown Response States is 0, then none of these structures needs to be specified. An Emergency Shutdown Response State is described by a combination of Emergency Shutdown Response State ID and the associated attributes. See Figure 8-93 and Table 8-103 for Emergency Shutdown Response State field definitions and format.</td>
</tr>
</table>

a. If a Power Management Element supports both Emergency Shutdown Trigger and Response capabilities using a bidirectional
signal, then the address to the Emergency Shutdown Signal Capability structure in the Emergency Shutdown Trigger and
Response Capability structures must be identical.

b. See Table 8-7 for a description of Standard Security Asset Class IDs.

<table>
<caption>Table 8-103. Emergency Shutdown Response State Format</caption>
<tr>
<th>Field Name</th>
<th>DWORD &amp; Bit Location</th>
<th>Standard Security $\mathrm { A s s e t }$</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>Emergency Shutdown Response State ID</td>
<td>$0 \left[ 4 : 0 \right]$</td>
<td>17</td>
<td>RO</td>
<td>Emergency Shutdown Response State ID This is an enumeration of the Emergency Shutdown Response States that are supported by the Power $\begin{array}{} { \text { Management Element as a response ro riner yeluer perer } } \\ { \text { Shutdown. The Power Managemement Director will select } } \end{array}$ one of these response states and update the Emergency Shutdown Response Control structure.b</td>
</tr>
<tr>
<td>Platform Notification (PN)</td>
<td>0 [31]</td>
<td>17</td>
<td>RO</td>
<td>Platform Notification (PN) This attribute bit indicates whether the given response state notifies the platform of an Emergency Shutdown event. If the Chiplet supports this functionality, it is recommended that this functionality be enabled for at least Emergency Shutdown Response State ID 0 (default Response State for Emergency Shutdown events at power-up reset).b</td>
</tr>
<tr>
<td>Vendor-defined Emergency Shutdown Response State Attributes</td>
<td>$1 \left[ 3 1 : 0 \right]$</td>
<td>17</td>
<td>RO</td>
<td>Vendor-defined Emergency Shutdown Response State Attributes These attributes can be used to specify vendor-defined characteristics of the response state.</td>
</tr>
</table>

a. See Table 8-7 for a description of Standard Security Asset Class IDs.

b. If a Power Management Element supports Emergency Shutdown Response Capability, Emergency Shutdown Response State ID
0 must be defined and implemented because that is defined as the default Response State for Emergency Shutdown events at
power-up reset (see Section 8.4.2.2.3.2).

\- If the chiplet (typically a Power Management Director) also supports the functionality to notify the platform of an
Emergency Shutdown, it is recommended to enable this functionality for at least Emergency Shutdown Response State
ID 0 so that platform notification is enabled at power-up/reset by default. The Platform Notification (PN) attribute bit
should reflect the behavior in the associated Emergency Shutdown Response State entry in the Emergency Shutdown
Response Capability structure.

\- The implementation of platform notification functionality is beyond the scope of this specification.

## 8.4.2.2.2.3 Emergency Shutdown Logging Capability Structure

This section defines a Power Management Element's capability to log the shutdown events for debug
and other purposes (see Figure 8-94 and Table 8-104).

Emergency Shutdown logging registers should preserve their state across chiplet power cycling and
reset events. Note that because an Emergency Shutdown may result in power down of the main
power rails, any logging capabilities advertised and supported for Emergency Shutdown are
recommended to be implemented on an auxiliary or always-on power domain.

<table>
<caption>Figure 8-94. Emergency Shutdown Logging Capability Structure</caption>
<tr>
<th colspan="6">+3</th>
<th colspan="2"></th>
<th colspan="8">+2</th>
<th colspan="8">+1</th>
<th colspan="8">+0</th>
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
<th></th>
</tr>
<tr>
<td colspan="2">Rsvd</td>
<td></td>
<td></td>
<td></td>
<td colspan="3">Management</td>
<td></td>
<td></td>
<td>Capability</td>
<td></td>
<td>ID</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td colspan="3">Reserved</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td colspan="2">Version</td>
<td></td>
<td></td>
<td></td>
</tr>
</table>

<figure>

DWORD 0

Number of
Emergency
Shutdown
Logging
Capabilities (L)

DWORD 1

Reserved

DWORD 2

Emergency Shutdown Logging Structure Address Low

DWORD 3

Emergency Shutdown Logging Structure Address High

DWORD 4

Emergency Shutdown Logging Capability (0)

DWORD 5

Emergency Shutdown Logging Capability (1)

...

...

DWORD
L+3

Emergency Shutdown Logging Capability (L-1)

</figure>

<table>
<caption>Figure 8-95. Emergency Shutdown Logging Capability Format</caption>
<tr>
<th></th>
<th colspan="7">+3</th>
<th colspan="8">+2</th>
<th colspan="8">+1</th>
<th></th>
<th colspan="7">+0</th>
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
<th>211</th>
<th>10</th>
<th>9</th>
<th></th>
<th></th>
<th>876543210</th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
</tr>
</table>

DWORD

Emergency Shutdown Logging Capability Attributes

Reserved

Emergency
Shutdown
Logging
Capability Type

<table>
<caption>Table 8-104. Emergency Shutdown Logging Capability Fields</caption>
<tr>
<th>Field Name</th>
<th>DWORD &amp; Bit Location</th>
<th>Standard Security Asset Class IDª</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>Version</td>
<td>$0 \left[ 7 : 0 \right]$</td>
<td>17</td>
<td>$R O$</td>
<td>Capability Structure Version This field indicates the version of this capability structure. This field has a value of 00h in this specification.</td>
</tr>
<tr>
<td>Management Capability ID</td>
<td>$0 \left[ 2 9 : 1 6 \right]$</td>
<td>17</td>
<td>$R O$</td>
<td>Management Capability ID This field specifies the Capability ID of this Management Capability structure. The Emergency Shutdown Logging Capability structure has a Management Capability ID of 00Ch.</td>
</tr>
<tr>
<td>Number of $\mathrm { E m e r g e n c y }$ Shutdown Logging Capabilities (L)</td>
<td>$1 \left[ 4 : 0 \right]$</td>
<td>17</td>
<td>$R O$</td>
<td>Number of Emergency Shutdown Logging Capabilities (L) $\begin{array}{} { \text { Number of Emergency Shutdown Logging capabilities that are } } \\ { \text { supported by the Power Managent Element } } \end{array}$ 00h: No Emergency Shutdown Logging capabilities are supported. 01h - 1Fh: Up to 31 Emergency Shutdown Logging capabilities are supported.</td>
</tr>
<tr>
<td>$\mathrm { E m e r g e n c y }$ Shutdown $\mathrm { L o g g i n g }$ Structure Address Low</td>
<td>2</td>
<td>17</td>
<td>$R O$</td>
<td>Emergency Shutdown Logging Structure Address Low Lower 32 bits of the pointer to the base address of the Emergency Shutdown Logging structure defined in Section 8.4.2.2.4. structures must be DWORD-aligned, bits $\left[ 1 : 0 \right] m u s t \quad b e \quad 0 0 b .$</td>
</tr>
<tr>
<td>Emergency Shutdown Logging Structure Address High</td>
<td>3</td>
<td>17</td>
<td>$R O$</td>
<td>Emergency Shutdown Logging Structure Address High Upper 32 bits of the pointer to the base address of the Emergency Shutdown Logging structure defined in Section 8.4.2.2.4.</td>
</tr>
<tr>
<td>Emergency Shutdown Logging Capability &lt;0:L-1&gt;</td>
<td>4 to $L + 3$</td>
<td>17</td>
<td>$R O$</td>
<td>Emergency Shutdown Logging Capability $\begin{array}{} { \text { One Emergency Shutdown Logging capability entry is added pel } } \\ { \text { Emergency Shutdown Logging capability supported. } } \end{array}$ $\begin{array}{} { \text { An Emergency Shutdown Logging capability is described by a } } \\ { \text { combination of Emergency Shutdown Logging Capability Type } } \end{array}$ $\begin{array}{} { \text { Figure } 8 } \\ { \text { format. } } \end{array}$ 8-102 and Table 8-105 specify the field definitions and</td>
</tr>
</table>

a. See Table 8-7 for a description of Standard Security Asset Class IDs.

<table>
<caption>Table 8-105. Emergency Shutdown Logging Capability Format</caption>
<tr>
<th>Field Name</th>
<th>DWORD &amp; Bit Location</th>
<th>$\begin{array}{} { \text { Standalu } } \\ { \text { Security } } \end{array}$ $\mathrm { C l a s s } I D ^ { c }$</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>Emergency Shutdown $\begin{array}{} \text { Logging } \\ \text { Capability } T y p \epsilon \end{array}$</td>
<td>$0 \left[ 4 : 0 \right]$</td>
<td>17</td>
<td>$R O$</td>
<td>Emergency Shutdown Logging Capability Type This field defines the Emergency Shutdown Logging Capability type (see Table 8-106 for the list of types).</td>
</tr>
<tr>
<td>Emergency Shutdown $\begin{array}{} { \text { Logging } } \\ { \text { capability } } \end{array}$ Attributes</td>
<td>$0 \left[ 3 1 : 1 6 \right]$</td>
<td>17</td>
<td>$R O$</td>
<td>Emergency Shutdown Logging Capability Attributes This field defines attributes for the Emergency Shutdown Logging Capability type.</td>
</tr>
</table>

a. See Table 8-7 for a description of Standard Security Asset Class IDs.

<table>
<caption>Table 8-106. Emergency Shutdown Logging Capability Types</caption>
<tr>
<th>Logging Capability Type</th>
<th>Logging Capability</th>
<th>Description</th>
<th>Attributes</th>
</tr>
<tr>
<td>000h - 001h</td>
<td>Reserved</td>
<td></td>
<td>RO</td>
</tr>
<tr>
<td>002h</td>
<td>$T r i g g e r \quad V e c t o r \quad L o g g i n g$</td>
<td>Vector of which Emergency Shutdown Trigger Capability(s) caused assertion of the Emergency Shutdown Trigger from this Power Management Element. Defined as a sticky (until explicitly cleared) bit vector with one bit allocated to each Emergency Shutdown Trigger Capability supported by the Power Management Element in the Emergency Shutdown Trigger Capability structure, starting from bit 0. Up to 31 possible Emergency Shutdown Triggers can be logged. Bits [63:31] of the corresponding logging register are reserved.</td>
<td>RW</td>
</tr>
<tr>
<td>$0 0 5 h \quad - \quad 0 1 7 h$</td>
<td>Reserved</td>
<td></td>
<td>RO</td>
</tr>
<tr>
<td>018h - 01Fh</td>
<td>$\mathrm { v a n d o r - d e f i n e d }$</td>
<td></td>
<td>Vendor-defined</td>
</tr>
</table>

## 8.4.2.2.3 Emergency Shutdown Control Structures

### 8.4.2.2.3.1 Emergency Shutdown Trigger Control Structure

This structure defines the Emergency Shutdown Trigger Controls per Power Management Element.
Power Management Director should configure this to enable one or more Emergency Shutdown
Triggers advertised by the element in the capability structure (see Figure 8-96 and Table 8-107). For
each of the Emergency Shutdown Triggers, the Power Management Director should program the
threshold for the trigger to assert.

Note that because Emergency Shutdown is defined as an event that requires a reset for the SiP to
recover, there are no controls defined for the trigger to de-assert. Once asserted, Emergency
Shutdown must remain asserted until it is reset through a reset of the chiplet.

The number of capabilities in this structure (N) matches the number of Emergency Shutdown Trigger
capabilities declared by the Power Management Element in Section 8.4.2.2.2.1. There is an in-order
mapping of each entry in the Emergency Shutdown Trigger Control structure to each entry in the
Emergency Shutdown Trigger Capability structure.

There is provision for an implementation-specific Emergency Shutdown Trigger Override that can be
used to control Emergency Shutdown, especially at power-up/reset before the other Trigger
capabilities have been discovered and set up. This is controlled by Override Enable (OE) bit in the
Emergency Shutdown Trigger Control structure below. See Figure 8-98 for additional details on the
behavior of Emergency Shutdown Trigger Override.

Figure 8-96. Emergency Shutdown Trigger Control Structure

<table>
<tr>
<th colspan="8">+3</th>
<th colspan="8">+2</th>
<th colspan="8">+1</th>
<th colspan="8">+0</th>
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
<th></th>
<th></th>
<th>876543210</th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
</tr>
</table>

<figure>

DWORD 0

Reserved

OE

DWORD 1

DWORD 2

DWORD 3

Emergency Shutdown Trigger Control 0

....

DWORD 8

DWORD 9

DWORD 10

Emergency Shutdown Trigger Control 1

...

DWORD 15

DWORD 16

...

...

DWORD
$8 \left( N - 1 \right) + 1$

DWORD
$8 \left( N - 1 \right) + 2$

Emergency Shutdown Trigger Control N-1

...

DWORD
$8 \left( N - 1 \right) + 7$

DWORD
$8 \left( N - 1 \right) + 8$

</figure>

Figure 8-97 shows the format of the Emergency Shutdown Trigger Control.

Figure 8-97. Emergency Shutdown Trigger Control Format

<figure>

+3

+2

+1

+0

31

30

29

28

27

26

25

24

23

22

21

20

19

18

17

16

15

14

13

12

11

10

9

876543210

DWORD 0

En

Reserved

Threshold
Encoding ID

DWORD 1

Entry Threshold

DWORD 2

DWORD 3

Reserved

DWORD 4

DWORD 5

DWORD 6

Vendor-defined Emergency Shutdown Trigger Controls

DWORD 7

</figure>

<table>
<caption>Table 8-107. Emergency Shutdown Trigger Control Fields</caption>
<tr>
<th>Field Name</th>
<th>DWORD &amp; Bit Location</th>
<th>Standard Security $\mathrm { c l a s s } \mathrm { I D } ^ { \bar { s } }$</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>Override Enable (OE)</td>
<td>0 [0]</td>
<td>16</td>
<td>RW</td>
<td>Emergency Shutdown Override Enable Controls the Chiplet Emergency Shutdown Override as shown in Figure 8-98. Reset Default: 1. Emergency Shutdown Override is defined to be default enabled to allow a chiplet to drive a vendor- defined implementation of the Emergency Shutdown Override Trigger at power-up/reset before other Emergency Shutdown Trigger capabilities have been discovered and initialized. The Power Management Director may disable the override by clearing this bit to 0 after other Emergency Shutdown Trigger capabilities have been configured and enabled.</td>
</tr>
<tr>
<td>Emergency Shutdown Trigger Control &lt;0:N-1&gt;</td>
<td>$\begin{array}{} { 1 \text { to } } \\ { 8 \left( N - 1 \right) + 8 } \end{array}$</td>
<td>16</td>
<td>RW</td>
<td>Emergency Shutdown Trigger Control &lt;0:N-1&gt; Defines the enable and other controllable fields for an Emergency Shutdown Trigger Type N:0-30, for each Emergency Shutdown Trigger capability supported.b Each Emergency Shutdown Trigger Control structure consists of eight DWORDs. Figure 8-97 and Table 8-108 specify the format description.</td>
</tr>
</table>

a. See Table 8-7 for a description of Standard Security Asset Class IDs.

b. The Power Management Director can enable zero or more of the Emergency Shutdown Trigger controls in the Power Management
Element.

<table>
<caption>Table 8-108. Emergency Shutdown Trigger Control Formata</caption>
<tr>
<th>Field Name</th>
<th>DWORD &amp; Bit Location</th>
<th>Standard $\begin{array}{} { \text { Security } } \\ { \text { Asset } } \end{array}$ Class IDb</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>Threshold Encoding ID</td>
<td>0 [4:0]</td>
<td>16</td>
<td>RW</td>
<td>Threshold Encoding ID See Table 8-109 for Emergency Shutdown Threshold encodings. These units apply to the Entry Threshold specified in this structure.</td>
</tr>
<tr>
<td>En</td>
<td>0 [31]</td>
<td>16</td>
<td>RW</td>
<td>Enable Enables the Emergency Shutdown Trigger type.</td>
</tr>
<tr>
<td>Entry Threshold</td>
<td>1 [31:0]</td>
<td>16</td>
<td>RW</td>
<td>Entry Thresholdc d Defines the Entry threshold for Emergency Shutdown Trigger assertion.</td>
</tr>
<tr>
<td>Vendor-defined Emergency Shutdown Trigger Controls</td>
<td>5, 6, 7</td>
<td>16</td>
<td>RW</td>
<td>Vendor-defined Emergency Shutdown Trigger Controlse Vendor-defined Emergency Shutdown Trigger controls.</td>
</tr>
</table>

a. A Power Management Element should assert Emergency Shutdown if any of the enabled shutdown conditions are met (see
Figure 8-98 and Figure 8-99 for additional details).

b. See Table 8-7 for a description of Standard Security Asset Class IDs.

c. If an Emergency Shutdown Trigger control is enabled, the Power Management Director must define a corresponding Entry
Threshold.

d. References to Entry Threshold in this document (when discussing Emergency Shutdown) assume that Emergency Shutdown is
asserted when one or more trigger values exceed (>) the respective Entry Threshold(s). Vendor implementations may choose
to use other definitions of comparison against the Entry Threshold for Emergency Shutdown assertion and use vendor-defined
attribute bits in the Emergency Shutdown Trigger Capability structure to specify the same.

e. Because Emergency Shutdown is defined as an event that requires a reset for the SiP to recover, there are no controls defined
for the trigger to de-assert. Once asserted, Emergency Shutdown must remain asserted until it is reset through a reset of the
chiplet.

<table>
<caption>Table 8-109. Emergency Shutdown Threshold Encoding ID</caption>
<tr>
<th>Threshold Encoding ID</th>
<th>Encoding Definition</th>
</tr>
<tr>
<td>00h - 1Fh</td>
<td>Vendor-defined encoding</td>
</tr>
</table>

<figure>
<figcaption>Figure 8-98. Emergency Shutdown Assertionª</figcaption>

Trigger 0 >
Entry_Threshold_0

Trigger 1 >
Entry_Threshold_1

Chiplet
Emergency
Shutdown

V

Trigger n>
Entry_Threshold_n

Flop

ES_Ovrd_Trigger
ES_Ovrd_Enable

</figure>

a. Entry triggers could be generated across more than one Power Management Element within a chiplet. However, they should be
combined to generate one final Emergency Shutdown output from the chiplet as per the logic shown.

<figure>
<figcaption>Figure 8-99. Emergency Shutdown Timing Diagram</figcaption>

Chiplet A
Emergency

Shutdown Trigger 0

Chiplet A
Emergency

Shutdown Trigger 1

Power Cycling/Reset

...

...

...

...

...

...

...

...

...

Chiplet A
Emergency
Shutdown Trigger N

Chiplet A
Emergency
Shutdown Output

Any trigger meeting the
assertion criteria results in
Shutdown Trigger assertion

Trigger stays asserted till a
power-cycling/reset event

</figure>

## 8.4.2.2.3.2 Emergency Shutdown Response Control Structure

This structure defines the Emergency Shutdown response controls per Power Management Element.
Power management will respond to the assertion based on these controls (see Figure 8-100 and
Table 8-110).

<table>
<caption>Figure 8-100. Emergency Shutdown Response Control Structure</caption>
<tr>
<th colspan="8">+3</th>
<th colspan="8">+2</th>
<th colspan="8">+1</th>
<th colspan="8">+0</th>
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
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th></th>
<th>76543210</th>
<th></th>
</tr>
</table>

<figure>

Emergency
Shutdown
Response State
ID

DWORD 0

En

Reserved

DWORD 1

Vendor-defined Emergency Shutdown Response State Controls

</figure>

<table>
<caption>Table 8-110. Emergency Shutdown Response Control Fields</caption>
<tr>
<th>Field Name</th>
<th>DWORD &amp; Bit Location</th>
<th>Standard Security Asset Class IDª</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>Emergency Shutdown Response State ID</td>
<td>0 [4:0]</td>
<td>16</td>
<td>RW</td>
<td>Emergency Shutdown Response State IDb This field sets the selected Emergency Shutdown Response State ID that the Power Management Element should go to in response to the Emergency Shutdown Trigger. Reset Default: 0. Default response at power-on/reset is set to Emergency Shutdown Response State ID 0. The Power Management Director can configure the Emergency Shutdown Response State ID to a different response state as part of the initialization sequence or later.</td>
</tr>
<tr>
<td>En</td>
<td>0 [31]</td>
<td>16</td>
<td>RW</td>
<td>Enable Set to enable this Emergency Shutdown Response State ID. Reset Default: 1. If Emergency Shutdown Override is supported, the Power Management Director can choose to disable a response to the Emergency Shutdown Trigger as part of the initialization sequence or later.</td>
</tr>
<tr>
<td>Vendor-defined Emergency Shutdown Response State Controls</td>
<td>1</td>
<td>16</td>
<td>RW</td>
<td>Vendor-defined Emergency Shutdown Response State Controlsc This field specifies other controls necessary for the Emergency Shutdown response.</td>
</tr>
</table>

a. See Table 8-7 for a description of Standard Security Asset Class IDs.

b. Emergency Shutdown Response State ID should be one of the Response Types of which the Power Management Element is
capable and advertises in the Emergency Shutdown Response Capability structure.

c. Vendor-defined response state controls can be used to provide additional controllability for the response state.

### IMPLEMENTATION NOTE

When the Power Management Director is writing to the Emergency Shutdown
Response Control structure, the Power Management Director cannot write both
DWORDs at the same time. The Emergency Shutdown Override may be enabled and
trigger between the two writes that update the Emergency Shutdown Response
Control structure. If this will cause an incorrect response to Emergency Shutdown,
the implementation should take steps to ensure that the updated Emergency
Shutdown Response will not take effect until both DWORDs have been updated.

## 8.4.2.2.3.3 Emergency Shutdown Logging Control Structure

This section defines the control structure for the Power Management Director to configure the
Emergency Shutdown logging capabilities of a Power Management Element (see Figure 8-101 and
Table 8-111).

The number of logging capabilities in this structure (L) matches the number of Emergency Shutdown
logging capabilities declared by the Power Management Element in Section 8.4.2.2.2.3. There is an
in-order mapping of each entry in the Emergency Shutdown Logging Control structure to each entry
in the Emergency Shutdown Logging Capability structure.

<table>
<caption>Figure 8-101. Emergency Shutdown Logging Control Structure</caption>
<tr>
<th colspan="4">+3</th>
<th colspan="2"></th>
<th colspan="6">+2</th>
<th colspan="2"></th>
<th colspan="6">+1</th>
<th colspan="2"></th>
<th colspan="8">+0</th>
</tr>
<tr>
<td>31 30</td>
<td>29 28</td>
<td>27</td>
<td>26</td>
<td>25</td>
<td>24</td>
<td>23</td>
<td>22</td>
<td>21</td>
<td>20</td>
<td>19</td>
<td>18</td>
<td>17</td>
<td>16</td>
<td>15</td>
<td>14</td>
<td>13</td>
<td>12</td>
<td>11</td>
<td>10</td>
<td>9</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td>876543210</td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td colspan="30">Emergency Shutdown Logging Enable</td>
</tr>
<tr>
<td colspan="30">Emergency Shutdown Logging Clear</td>
</tr>
<tr>
<td colspan="4"></td>
<td colspan="23">Emergency Shutdown Logging Control (0)</td>
<td></td>
<td></td>
<td></td>
</tr>
<tr>
<td colspan="4"></td>
<td colspan="24">Emergency Shutdown Logging Control (1)</td>
<td></td>
<td></td>
</tr>
<tr>
<td colspan="2"></td>
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
<td>...</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
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
<td colspan="4"></td>
<td colspan="19">Emergency Shutdown Logging Control (L-1)</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
</tr>
</table>

<figure>

DWORD0

DWORD1

DWORD 2

DWORD 3

...

DWORD
L+1

</figure>

<table>
<caption>Figure 8-102. Emergency Shutdown Logging Control Format</caption>
<tr>
<th></th>
<th colspan="6">+3</th>
<th colspan="8">2+</th>
<th colspan="8">+1</th>
<th colspan="8">+0</th>
</tr>
<tr>
<th>31</th>
<th>30</th>
<th>29</th>
<th>28</th>
<th>27</th>
<th>26</th>
<th>25 24</th>
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
<td colspan="7">Vendor-defined Emergency</td>
<td colspan="3">Shutdown</td>
<td></td>
<td>Logging</td>
<td colspan="3">Controls</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td></td>
<td colspan="4">Reserved</td>
<td></td>
<td></td>
<td></td>
<td></td>
<td colspan="2"></td>
</tr>
</table>

DWORD

<table>
<caption>Table 8-111. Emergency Shutdown Logging Control Fields</caption>
<tr>
<th>Field Name</th>
<th>DWORD &amp; Bit Location</th>
<th>Standard Security $\mathrm { c l a s s } I D ^ { a }$</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>Emergency Shutdown Logging Enable</td>
<td>0</td>
<td>16</td>
<td>RW</td>
<td>Emergency Shutdown Logging Enable Enable bit vector for Emergency Shutdown logging capabilitiesb. One bit per logging capability as described in the Emergency Shutdown Logging Capability structure. [L-1:0]: Enable control for the L logging capabilities defined. [30:L]: Unused. [31]: Reserved.</td>
</tr>
<tr>
<td>Emergency Shutdown Logging Clear</td>
<td>1</td>
<td>16</td>
<td>RW</td>
<td>Emergency Shutdown Logging Clear Clear vector for Emergency Shutdown logging capabilities. One bit per logging capability as described in the Emergency Shutdown Logging Capability structure. [L-1:0]: Clear control for the L logging capabilities defined. Writing 1 to a bit in this vector clears the corresponding logging register. Reads return 0s. [30:L]: Unused. [31]: Reserved.</td>
</tr>
<tr>
<td>Emergency Shutdown Logging Control &lt;0:L-1&gt;</td>
<td>2 to L+1</td>
<td>16</td>
<td>RW</td>
<td>Emergency Shutdown Logging Control Control for each Emergency Shutdown logging capability. Figure 8-102 and Table 8-112 provide details of the logging control format.</td>
</tr>
</table>

a. See Table 8-7 for a description of Standard Security Asset Class IDs.

b. The Power Management Director can enable zero or more of the Emergency Shutdown logging capabilities.

<table>
<caption>Table 8-112. Emergency Shutdown Logging Control Format</caption>
<tr>
<th>Field Name</th>
<th>DWORD &amp; Bit Location</th>
<th>Standard Security Asset Class IDª</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>Vendor-defined Emergency Shutdown Logging Controls</td>
<td>0 [31:16]</td>
<td>16</td>
<td>RW</td>
<td>Vendor-defined Emergency Shutdown Logging Controls Vendor-defined controls that are used to control the behavior of the Emergency Shutdown Logging capability.</td>
</tr>
</table>

a. See Table 8-7 for a description of Standard Security Asset Class IDs.

## 8.4.2.2.4 Emergency Shutdown Logging Structures

This section describes the logging structures that are used to maintain Emergency Shutdown logs
based on the Emergency Shutdown logging capabilities and controls as defined in Section 8.4.2.2.2.3
and Section 8.4.2.2.3.3, respectively.

The number of logging capabilities in this structure (L) matches the number of Emergency Shutdown
logging capabilities declared by the Power Management Element in Section 8.4.2.2.2.3. There is an
in-order mapping of each entry in the Emergency Shutdown Logging Control structure to each entry
in the Emergency Shutdown Logging Capability structure.

Emergency Shutdown logging registers should preserve their state across chiplet power cycling and
reset events. Note that because an Emergency Shutdown may result in power down of the main
power rails, any logging capabilities advertised and supported for Emergency Shutdown are
recommended to be implemented on an auxiliary or always-on power domain.

## 8.4.2.2.4.1 Emergency Shutdown Logging Structure

Figure 8-103 and Table 8-113 describe the Emergency Shutdown Logging structure.

<table>
<caption>Figure 8-103. Emergency Shutdown Logging Structure</caption>
<tr>
<th colspan="8">+3</th>
<th colspan="8">+2</th>
<th colspan="8">+1</th>
<th colspan="8">+0</th>
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
</table>

<figure>

DWORD 0

DWORD 1

Emergency Shutdown Log 0

DWORD 2

DWORD 3

Emergency Shutdown Log 1

...

...

DWORD

2L-2

$\begin{array}{} { \text { DWORD } } \\ { 2 L - 1 } \end{array}$

Emergency Shutdown Log L-1

</figure>

<table>
<caption>Table 8-113. Emergency Shutdown Logging Fields</caption>
<tr>
<th>Field Name</th>
<th>DWORD &amp; Bit Location</th>
<th>Standard Security Asset Class IDª</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>Emergency Shutdown Log&lt;0:L-1&gt;</td>
<td>0 to 2L-1</td>
<td>17</td>
<td>RO</td>
<td>Emergency Shutdown Log Emergency Shutdown Log entryb as defined by the Emergency Shutdown Logging Capability structure“. Each Emergency Shutdown Log is a 64-bit registerd. The lower address DWORD contains the lower 32 bits of the 64-bit register and the upper address DWORD contains the upper 32 bits of the 64-bit register. Controlled by Emergency Shutdown Logging controls.</td>
</tr>
</table>

a. See Table 8-7 for a description of Standard Security Asset Class IDs.

b. For log entries associated with an Emergency Shutdown Logging Capability Type of 002h (Trigger Vector Logging Capability), if
the log register is cleared by software while the respective Emergency Shutdown Trigger is still asserted, the log bit should be
set again.

c. The Power Management Director can enable one or more logging capabilities in the Emergency Shutdown Logging Control
structure to control these logs.

d. The Power Management Director can read these logs and take an action based on the recorded values as appropriate.

## 8.4.2.2.5 Emergency Shutdown Address Map

This section describes the address map of all the structures related to Emergency Shutdown.
Figure 8-104. Emergency Shutdown Address Map

<figure>

FFFF FFFF FFFF FFFFh

Emergency
Shutdown
Logging
Structure

DW 2 (L-1), 2(L-1)+1

DW 2.3
DW 0. 1

For up to L Emergency
Shutdown Logs

Emergency

Shutdown

Open Drain

Capability

Open drain signal capability (ES)

Emergency Shutdown Trigger Capability and
Control

DW 8 (N-1)+1+Offset
to 8 (N-1)+B+Offset

For up to N Emergency
Shutdown Trigger Control

DW 1-8 + Offset

Emergency Shutdown
Trigger Control Offset
(N+4)

DW0+Offset
DW N+3

For Up to N Emergency
Shutdown Trigger
Capabilities
Emergency Shutdown
Open Drain Capability
Pointer

DW4
DW3

DW2 high)
DW1 (OD Pointer low)
DWO

Capability Directory

Emergency Shutdown Trigger
Capability
Emergency Shutdown Logging
Capability
Emergency Shutdown Response
Capability

Emergency Shutdown
Response Capability

and Control

Emergency
Shutdown
Response Control
Offset (2M4+4)

DW 0-1 + Offset
$D W \quad 2 \left( M - 1 \right) + 4 , 2 \left( M - 1 \right) + 5$

Emergency Shutdown Response
Control

DW 4, 5
DW3
DWZ high)
DW1 (OD Pointer low)
DWO

For up to M Emergency Shutdown
Response States

Emergency Shutdown Open Drain
Capability Pointer

Emergency Shutdown
Logging

Capability and Control

DW L+1 + Offset

Emergency Shutdown
Logging Control
Offset (L+4)

2 + Offset
DW 1 + Ultset
DW 0 + Offset

For up to L Emergency
Shutdown Logging Controls

DW
DW (L-1)+4

For up to L Emergency
Shutdown Logging Capabilities

DW4
DW3 (ES logging Pointer high)
DW2 (ES Logging Pointer low)
DWI
DWO

Emergency Shutdown
Logging Structure Pointer

0000 0000 0000 0000h

</figure>

§ §

### 9.0 Configuration and Parameters

#### 9.1 High-level Software View of UCIe

A key goal of UCIe is to leverage all the software investments made for PCIe and CXL while still
defining the interface in an extensible way for future innovative solutions. To that end, UCIe SW view
of the protocol layer is consistent with the associated protocol. For example, the host Downstream
Port for UCIe that is capable of supporting CXL protocols will appear to software as a Root Port with
CXL DVSEC capability and relevant PCIe capabilities. Similarly, a host downstream port for UCIe that
is capable of supporting PCIe protocol only, will appear to software as a Root Port with relevant PCIe
capabilities only. Host side or device side view of software for Streaming protocol is implementation-
specific since the protocol itself is implementation-specific. It is though strongly recommended that
ecosystem implementations define streaming solutions leveraging the SW hooks already in place for
supporting CXL and PCIe. The Upstream Ports that connect to a UCIe Root Port can be a PCIe
endpoint, PCIe Switch, a CXL endpoint-device, or a CXL Switch. This allows for UCIe solution to be
fully backward compatible to pre-UCIe software. The remainder of this chapter talks about SW view of
UCIe when paired with PCIe or CXL protocol layers.

UCIe specification allows for a single UCIe Link to be shared by multiple protocol stacks. In this
version of the spec, this sharing is limited to at most 2 protocol stacks. Shared Link layer is a new
concept from Software perspective and requires new discovery/control mechanisms. The mechanism
by which UCIe-aware SW discovers UCIe capability is described in the next section.

Table 9-1 shows the legal/illegal combinations of Upstream and Downstream devices/ports at a given
UCIe interface, from a SW viewpoint.

<table>
<caption>Table 9-1. Software view of Upstream and Downstream Device at UCIe interface</caption>
<tr>
<th rowspan="2">Downstream Component: SW View</th>
<th colspan="4">Upstream Component: SW View</th>
</tr>
<tr>
<th>PCIe RP, PCIe Switch DSpa</th>
<th>CXL-RP, CXL Switch DSpb</th>
<th>CXL Downstream Port RCRBC</th>
<th>Streaming Device</th>
</tr>
<tr>
<td>PCIe EP, PCIe Switch USP</td>
<td>Valid</td>
<td>Valid</td>
<td>Illegal</td>
<td rowspan="3">Vendor defined</td>
</tr>
<tr>
<td>CXL Upstream Port RCRBd</td>
<td>Illegal</td>
<td>Illegal</td>
<td>Illegal</td>
</tr>
<tr>
<td>CXL EP</td>
<td>Valid</td>
<td>Valid</td>
<td>Illegal</td>
</tr>
<tr>
<td>Streaming Device</td>
<td>Vendor defined</td>
<td></td>
<td colspan="2"></td>
</tr>
</table>

a. PCIe RP = As defined in PCIe Base Specification

b. CXL RP/Switch DSP = Standard PCIe RP/Switch-DSP with additional CXL Flexbus Port DVSEC capability

c. CXL Downstream Port RCRB = CXL Link at host or at Switch DSP that is enumerated via CXL defined
Downstream Port RCRB (instead of via a Root Port)

d. CXL Upstream Port RCRB = CXL upstream port that is enumerated via CXL defined RCRB with CXL Upstream
Port RCRB and that has a RCIEP below it.

All the CXL/PCIe legacy/advanced capabilities/registers defined in the respective specifications apply
to UCIe host and devices as well. Some Link and PHY layer specific registers in PCIe Base
Specification do not apply in UCIe context and these are listed in the appendix. In addition, two new

DVSEC capabilities and four other MMIO mapped register blocks are defined to deal with UCIe-specific
Adapter and Physical Layer capabilities.

#### 9.2 SW Discovery of UCIe Links

UCIe-aware Firmware/Software may discover the presence and capabilities of UCIe Links in the
system per Table 9-2.

<table>
<caption>Table 9-2. SW discovery of UCIe Links</caption>
<tr>
<th>UCIe Links</th>
<th>How discovered?</th>
<th>Salient Points</th>
</tr>
<tr>
<td>In Host</td>
<td>Host specific Register Block called UiRB, containing UCIe Link DVSEC Capability</td>
<td>· UiRB is at a host defined static location. · Each UCIe Link has a separate URB Base address and these are enumerated to OS via UCIe Early discovery table (UEDT)ª · Association of a UCIe Link to 1 or more Root ports is described in UEDT, allowing for UCIe-aware SW to understand the potential shared nature of the UCIe Link.</td>
</tr>
<tr>
<td>In Endpoints</td>
<td>Dev0/Fn0 of the device carries a UCIe Link DVSEC Capability.</td>
<td>. In multi-stack implementations, Dev0/Fn0 of the endpoint in only one of the stacks carries the UCIe Link DVSEC Capability.</td>
</tr>
<tr>
<td>In Switch USP</td>
<td>Dev0/Fn0 of the USP carrying a UCIe Link DVSEC Capability</td>
<td>. In multi-stack implementations, Dev0/Fn0 of the USP in only one of the stacks carries the UCIe Link DVSEC Capability.</td>
</tr>
<tr>
<td>In Switch DSP</td>
<td>Dev0/Fn0 of the Switch USP carrying one ore more UiSRB DVSEC Capability</td>
<td>. UCIe Links below the switch are described in UiSRB whose base address is provided in the UiSRB DVSEC Capability · A UCIe Link DVSEC capability per downstream UCIe Link is present in the UiSRB · Association of a UCIe Link to 1 or more Switch DSPs is described as part of the UCIe Link DVSEC Capability, allowing for UCIe-aware SW to understand the potential shared nature of the UCIe interface Note: It is legal for a Switch USP to carry the UiSRB DVSEC capability but not a UCIe Link DVSEC Capability</td>
</tr>
</table>

a. UEDT structure is standardized as part of the ACPI specification.

#### 9.3 Register Location Details and Access Mechanism

· 2 UCIe DVSEC capabilities (UCIe Link DVSEC, UiSRB DVSEC) and four other MMIO-mapped
register blocks are defined in this version of the Specification.

. UCIe Link DVSEC capability is located in UiRB for host root ports and in UiSRB for Switch
downstream ports.

· UiRB region is defined at a static location on the host side and its size is enumerated in the UEDT
structure. Only UCIe Link related registers are permitted in this region and designs must not
implement non-UCIe related functionality in this region.

. There is a unique UiRB base address for each UCIe Link, in the host

· UiSRB region base address is provided in the UiSRB DVSEC capability. This region is part of a BAR
region of Switch Dev0/Fn0 USP.

. For scalability/flexibility reasons, multiple UiSRB DVSEC capabilities can exist in a Switch USP
function. In case of multiple UiSRB DVSEC capabilities in the USP. a given DSP UCIe Link can only
be described in one of the UiSRB structures.

· Configuration space registers are accessed using configuration reads and configuration writes.
Register Blocks are in memory mapped regions and are accessed using standard memory reads
and memory writes.

. UCIe Retimer registers are not directly accessible from host SW. They can be accessed only by
way of a Mailbox mechanism over the sideband interface (hence the terms SB-MMIO and SB-

Config in Table 9-3). The Mailbox mechanism is available via RP/DSP UCIe Link DVSEC Capability
to access the UCIe Retimer registers on the Retimer closest to the host. For accessing UCIe
Retimer registers on the far end Retimer, the same Mailbox mechanism is also available in the
UCIe Link DVSEC capability of EP/USP. See Section 9.5.1.11 and Section 9.5.1.12 for details of
the Mailbox mechanism.

· For debug and runtime Link health monitoring reasons, host SW can also access the UCIe related
registers in any partner die on the sideband interface, using the same Mailbox mechanism. For
brevity purposes, that is not shown in Table 9-3. Note that register accesses over sideband are
limited to only the UCIe-related Capability registers (the two DVSECs currently defined in the
spec) and the four defined UCIe Register Blocks. Nothing else on the remote die are accessible via
the sideband mechanism.

Table 9-3 summarizes the location of various register blocks in each native UCIe port/device.
Henceforth a "UCIe port/device/EP/Switch" is used to refer to a standard PCIe or CXL port/device/EP/
Switch with UCIe Link DVSEC Capability.

<table>
<caption>Table 9-3. Summary of location of various UCIe Link related registers</caption>
<tr>
<th rowspan="2">Register</th>
<th colspan="5">Where the Register Resides</th>
<th rowspan="2">Comments</th>
</tr>
<tr>
<th>RP</th>
<th>Switch USP</th>
<th>Switch DSP</th>
<th>EP</th>
<th>UCIe Retimer</th>
</tr>
<tr>
<td>UCIe Link DVSEC</td>
<td>UİRB</td>
<td>Config space</td>
<td>UİSRB</td>
<td>Config Space</td>
<td>Sideband Config Space</td>
<td>Registers that define the basic UCIe interface related details</td>
</tr>
<tr>
<td>UCIe D2D/PHY Register Block</td>
<td>UİRB</td>
<td>Switch USP-BAR Region</td>
<td>UİSRB</td>
<td>EP-BAR Region</td>
<td>SB-MMIO Space</td>
<td>Registers that define lower- level functionality for the D2D/ PHY interface of a typical UCIe implementation</td>
</tr>
<tr>
<td>UCIe Test/ Compliance Register Block</td>
<td>UİRB</td>
<td>Switch USP-BAR Region</td>
<td>UİSRB</td>
<td>EP-BAR Region</td>
<td>SB-MMIO Space</td>
<td>Registers for Test/Compliance of UCIe interface</td>
</tr>
<tr>
<td>UCIe Implementation Specific Register Block</td>
<td>UİRB</td>
<td>Switch USP-BAR Region</td>
<td>UİSRB</td>
<td>$\begin{array}{} { E P - B A R } \\ { R e q i o n } \end{array}$</td>
<td>SB-MMIO Space</td>
<td>Registers for vendor specific implementation</td>
</tr>
</table>

#### 9.4 Software view Examples

Figure 9-1 summarizes all the details of UCIe related DVSEC Capabilities and SW discovery, for an
implementation consisting of Root Ports and Endpoints. This example has a host with 2 UCIe
downstream Links that each carry traffic from 2 Root Ports.

<figure>
<figcaption>Figure 9-1. Software view Example with Root Ports and Endpoints</figcaption>

Host Bridge

Host Bridge

UČIeO PHY
Implementation
Specific
Header

UCie1 PHY
Implementation
Specific
Header

UCIc0 D2D
Implementation
Specific
Header

UCle1 D20
Implementation
Specific
Header

Reserved

Reserved

UCleO Comp/Test

UCle1 Comp/Test

Header

Header

Reserved

Recurved

UCle Link DVSEC

UCIeO PHY/D2D

UCle1 PHY/D2D

Header
Reminded

Header
Reserved

UCle Link DVSEC

MSI capability

MSI capability

Pirstorvikİ

Réservedi

Host defined UiRB
Base Address 0

KUCle LinkO DEVSEC
Reg Locator
Next Cap

UCle Link 1 DEVSFC
Reg Locator
Next Cap

Host defined UIRB
Base Address 1

UCle0

Root Port

Root Port

UCle1
Root Port

Root Port

Type 1 Header
DevN, FnD

Type 1 Header
DevM, FriD

Type 1 Header
DevX, Fn0

Type 1 Header
DevY, FnO

UCle0

UGe1

Logical link

Logical link

Logical link

Logical link

UDe

Udle

Type 0 Header
Devo, Fn0

Type D Header
Devo, Fn0

Type O Header
Devo, Fn0

Type O Header
Dev0, Fr0

EP

EP

EP

EP

UCle Link DVSEC

</figure>

Example in Figure 9-2 has a Switch with 2 UCIe Links on its downstream side and each UCIe Link
carries traffic from 2 Switch DSPs.

<figure>
<figcaption>Figure 9-2. Software view Example with Switch and Endpoints</figcaption>

UiSRB in Switch USP BAR region

Reserved

UCIe1 PHY
Implementation
Specific
Header

Reserved

UCIe1 D2D
Implementation
Specific
Header

UCIe1 Comp/Test

Header

UCIe1 PHY/D2D

Header

UCIe Link DVSEC

LICle Link1 DEVSFC
Reg Locator

$\mathrm { N e x t } \mathrm { C a p } = 0 h$

UCIe0 PHY
Implementation
Specific
Header

UCIe0 D2D
Implementation
Specific
Header

UCIe0 Comp/Test

Header

UCIe0 PHY/D2D

Header

UCle Link0 DEVSFC
Reg Locator
Next Cap

From UiSRB DVSEC

UCIe0

Switch DSP

Switch DSP

UCIe1
Switch DSP

Switch DSP

Type 1 Header
DevN, Fn0

Type 1 Header
$\mathrm { D e v N } , F n O$

Type 1 Header
DevN, Fn0

Type 1 Header
DevN, Fn0

UCIe0

UCIe1

$\log _ { 1 } \left( \frac { \ln k } { k } \right.$

Logical link

Logical link

Logical link

UCIe

UCIe

Type 0 Header
Dev0, Fn0

Type 0 Header
Dev0, Fn0

Type 0 Header
Dev0, Fn0

Type 0 Header
Dev0, Fn0

EP

EP

EP

EP

UCIe Link DVSEC

</figure>

Example in Figure 9-3 shows details UCIe registers in an implementation where two EPs are sharing a
common UCIe Link.

<figure>
<figcaption>Figure 9-3. Software view Example of UCIe Endpoint</figcaption>

UCle PHY
Implementation
Specific

Header

From <BIR-BAR + Reg-offset of UCle PHY Implementation Specific Reg Locator>

UCle D2D
Implementation
Specific

Header

From <BIR-BAR + Reg-offset of UCle D2D Implementation Specific Reg Locator>

UCle Comp/Test

Header

From <BIR-BAR + Reg-offset of UCle Comp/Test Reg Locator>

UCle PHY/D2D

Header

From <BIR-BAR + Reg-offset of UCle PHY/D2D Reg Locator>

UCle

Type 0 Header
Dau Cnn

LIClo Link DEVSEC
Reg Locator

Type 0 Header
Dev0, Fn0

Next Cap

UCle Link DVSEC

EP

EP

</figure>

#### 9.5 UCIe Registers

Table 9-4 summarizes the attributes for the register bits defined in this chapter. Unless otherwise
specified, the definition of these attributes is consistent with PCIe Base Specification and CXL
Specification.

<table>
<caption>Table 9-4. Register Attributes</caption>
<tr>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>$R O$</td>
<td>Read Only</td>
</tr>
<tr>
<td>ROS</td>
<td>Read Only Stickyª</td>
</tr>
<tr>
<td>$R W$</td>
<td>Read-Write</td>
</tr>
<tr>
<td>RWL</td>
<td>Read Write Lock Follow RW behavior until locked. When locked, the bit value cannot be altered by software. The locking condition associated with each RWL field is specified as part of the field definition.</td>
</tr>
<tr>
<td>RWO</td>
<td>$R e a d - W r i t e - O n e - T o - L o c k$ Field becomes RO after writing 1 to it. Cleared by management reset.</td>
</tr>
<tr>
<td>RWS</td>
<td>Read Write Stickyª</td>
</tr>
<tr>
<td>RW1C</td>
<td>Read-Write-One-To-Clear</td>
</tr>
<tr>
<td>RW1CS</td>
<td>Read-Write-One-To-Clear-Stickyª</td>
</tr>
<tr>
<td>HWInit</td>
<td>Hardware Initializedb</td>
</tr>
<tr>
<td>RsvdP</td>
<td>Reserved and Preserved</td>
</tr>
<tr>
<td>RsvdZ</td>
<td>Reserved and Zero</td>
</tr>
</table>

a. Definition of 'sticky' follows the underlying protocol definition if any of the Protocol stacks are PCIe or CXL. For
Streaming, the sticky registers are recommended to preserve their value even if the Link is down. In all
scenarios, Domain Reset must initialize these to their default values.

b. Typically, this register attribute is used for functionality/capability that can vary with package integration. For
example, a chiplet that is capable of 32 GT/s maximum speed might be routed to achieve a maximum speed
of 16 GT/s in a given package implementation. To account for such scenarios, the Max link speed field in the
UCIe Link Capability register has the HWInit attribute and its value could be configured by a package-level
strap or device/system firmware to reflect the maximum speed of that implementation.

All numeric values in various data structures, individual registers and register fields defined in this
chapter are always encoded in little endian format, unless stated otherwise.

##### 9.5.1 UCIe Link DVSEC

This is the basic capability register set that is required to operate a UCIe Link. And this is one of two
DVSEC capabilities defined for UCIe in the first generation. Not all the registers in the capability are
applicable to all device/port types. The applicable registers for each device/port type are indicated in
the right side of Figure 9-4. Software may use the presence of this DVSEC to differentiate between a
UCIe device vs. a standard PCIe or CXL device. Software may use this DVSEC to differentiate between
a UCIe Root Port and a standard PCIe or CXL Root Port.

<table>
<caption>Figure 9-4. UCIe Link DVSEC</caption>
<tr>
<th colspan="3">PCI Express Extended Capability Header</th>
</tr>
<tr>
<th colspan="3">Designated Vendor Specific Header 1</th>
</tr>
<tr>
<th>Capability Descriptor</th>
<th colspan="2">Designated Vendor Specific Header 2</th>
</tr>
<tr>
<td>UCIe Link</td>
<td colspan="2">Capability</td>
</tr>
<tr>
<td>UCIe</td>
<td>Link Controle</td>
<td></td>
</tr>
<tr>
<td>UCIe</td>
<td colspan="2">Link Status</td>
</tr>
<tr>
<td>Error Notification Control</td>
<td colspan="2">Link Event Notification Control</td>
</tr>
<tr>
<td colspan="3">Register Locator 0 Low</td>
</tr>
<tr>
<td>Register</td>
<td>Locator 0 High</td>
<td></td>
</tr>
<tr>
<td></td>
<td>...</td>
<td></td>
</tr>
<tr>
<td></td>
<td>...</td>
<td></td>
</tr>
<tr>
<td></td>
<td>Reserved</td>
<td></td>
</tr>
<tr>
<td>Sideband</td>
<td>Mailbox Index Low</td>
<td></td>
</tr>
<tr>
<td colspan="3">Sideband Mailbox Index High</td>
</tr>
<tr>
<td>Sideband</td>
<td>Mailbox Data Low</td>
<td></td>
</tr>
<tr>
<td>Sideband</td>
<td>Mailbox Data High</td>
<td></td>
</tr>
<tr>
<td>Reserved</td>
<td>Sideband Mailbox Status</td>
<td>Sideband Mailbox Control</td>
</tr>
<tr>
<td colspan="3">Requester ID/Reserved</td>
</tr>
<tr>
<td></td>
<td colspan="2">Reserved</td>
</tr>
<tr>
<td>Associated</td>
<td colspan="2">Port Numbers (1-N)</td>
</tr>
<tr>
<td></td>
<td colspan="2">...</td>
</tr>
</table>

<figure>

a

b

c

</figure>

d

a. Applies to UCIe-EP, UCIe-USP, UCIe-Retimer.

b. Applies to UCIe-EP, UCIe-USP when paired with a retimer.

c. Applies to UCIe-RP.

d. Applies to UCIe-DSP.

e. Software writes to this register need to be broadcast to both D2D Adapter and PHY blocks because some registers could be
implemented in either block or both blocks.

###### 9.5.1.1 PCI Express Extended Capability Header (Offset 0h)

Set as follows for UCIe Link DVSEC. All bits in this register are RO.

<table>
<caption>Table 9-5. UCIe Link DVSEC - PCI Express Extended Capability Header</caption>
<tr>
<th>Field</th>
<th>Bit Location</th>
<th>Value</th>
<th>Comments</th>
</tr>
<tr>
<td>Capability ID</td>
<td>15:0</td>
<td>0023h</td>
<td>Value for PCI Express DVSEC capability</td>
</tr>
<tr>
<td>Revision ID</td>
<td>19:16</td>
<td>1h</td>
<td>Latest revision of the DVSEC capability</td>
</tr>
<tr>
<td>Next Capability Offset</td>
<td>31:20</td>
<td>Design Dependent</td>
<td>For UCIe Link DVSEC in UiRB: Set to point to the next capability associated with this UCIe Link. In this revision of the spec, this $T h e \quad o f f s e t \quad i s \quad i n \quad g r a n u l a r i t y \quad o f \quad B y t e s \quad f r o m \quad t h e$ is set to 100h, the next capability is located at offset of 100h from the base of UiRB. UCIe Link DVSEC in UiSRB: Set to point to the UCIe Link DVSEC capability of the next UCIe Link associated with a downstream port of the switch. The last UCIe Link DVSEC capability will set this offset to 0h indicating there are no more UCIe Links on downstream ports. The offset is in granularity of Bytes from the base address of UiSRB. For example, if this is set to 100h, the next DVSEC capability for the next Link is located at offset of 100h from the base of UiSRB. Retimer: Set to 0h Others: design dependent</td>
</tr>
</table>

##### 9.5.1.2 Designated Vendor Specific Header 1, 2 (Offsets 4h and 8h)

A few things to note on the various fields described in Table 9-6. DVSEC Revision ID field represents
the version of the DVSEC structure. The DVSEC Revision ID is incremented whenever the structure is
extended to add more functionality. Backward compatibility shall be maintained during this process.
For all values of n, DVSEC Revision ID n+1 structure may extend Revision ID n by replacing fields that
are marked as reserved in Revision ID n, but must not redefine the meaning of existing fields.
Software that was written for a lower Revision ID may continue to operate on UCIe DVSEC structures
with a higher Revision ID, but will not be able to take advantage of new functionality.

All bits in this register are RO.

<table>
<caption>Table 9-6. UCIe Link DVSEC - Designated Vendor Specific Header 1, 2</caption>
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
<td>Device dependent. See Section 9.5.1.19 for some examples.</td>
</tr>
<tr>
<td>Designated Vendor-Specific Header 2 (offset 08h)</td>
<td>DVSEC ID</td>
<td>15:0</td>
<td>0h</td>
</tr>
</table>

## 9.5.1.3 Capability Descriptor (Offset Ah)

Provides a way for SW to discover which optional capabilities are implemented by the UCIe Port/
Device.

<table>
<caption>Table 9-7. UCIe Link DVSEC - Capability Descriptor</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td rowspan="3">$2 : 0$</td>
<td rowspan="3">RO</td>
<td>Number of Register locators 0h: 2 Register Locators 1h: 3 Register Locators 2h: 4 Register Locators</td>
</tr>
<tr>
<td>... 6h: 8 Register locators 7h: 1 Register Locator</td>
</tr>
<tr>
<td>For this revision of UCIe, only values 0h, 1h, 2h and 7h are valid.</td>
</tr>
<tr>
<td rowspan="2">3</td>
<td rowspan="2">RO(RP/DSP), HWInit(EP/USP), RsvdP(Retimer)</td>
<td>Sideband mailbox Registers Present 0h: No sideband mailbox register set present in this capability 1h: Sideband mailbox register set present in this capability For RP/DSP, default value of this is 1.</td>
</tr>
<tr>
<td>EP/USP must set this bit when they are paired with a retimer and must clear this bit in all other scenarios.</td>
</tr>
<tr>
<td rowspan="5">7:4</td>
<td rowspan="5">RO(DSP), RsvdP (Others)</td>
<td>Number of Switch DSPs associated with this UCIe Link Applies only to UCIe Link DVSEC in UiSRB.</td>
</tr>
<tr>
<td>The specific 'port number' values of each Switch downstream port associated with this UCIe Link is called out in the Associated Port Number register(s) in this capability.</td>
</tr>
<tr>
<td>0h: 1 Port 1h: 2 ports ... Fh: 16 ports</td>
</tr>
<tr>
<td>'Port Number' is bits 31:24 of the PCIe Link capabilities register of the downstream port.</td>
</tr>
<tr>
<td>For first generation of UCIe, only values 0h and 1h are legal.</td>
</tr>
<tr>
<td>15:8</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

### 9.5.1.4 UCIe Link DVSEC - UCIe Link Capability (Offset Ch)

Basic characteristics of the UCIe Link are discovered by SW using this register.

<table>
<caption>Table 9-8. UCIe Link DVSEC - UCIe Link Capability (Sheet 1 of 2)</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>0</td>
<td>RO</td>
<td>Raw Format If set, indicates the Link can support Raw Format.</td>
</tr>
<tr>
<td>3:1</td>
<td>HWInit</td>
<td>Max Link Width 0h: x16 4h: x256 1h: x32 7h: x8 2h: x64 Others: Reserved 3h: x128</td>
</tr>
<tr>
<td>7:4</td>
<td>HWInit</td>
<td>Max Link Speeds $O h : 4 \quad G T / s$ $5 h : 3 2 \quad G T / s$ $\begin{array}{} { 1 h : 8 G 1 / 5 } \\ { 2 h \cdot 1 2 G T / s } \end{array}$ 6h: 48 GT/s 7h: 64 GT/s $3 h : 1 6 \quad G T / s$ Others: Reserved</td>
</tr>
<tr>
<td>8</td>
<td>$R O \left( R e t i m e r \right) _ { r } ,$</td>
<td>Retimer - Set by retimer to indicate it to SW</td>
</tr>
<tr>
<td>9</td>
<td>$\begin{array}{} { \text { RsvdP \left(Retimer } } \\ { \text { RO \left(others\right) } } \end{array} ,$</td>
<td>Multi-protocol capableª $0 - \mathrm { s i n g l e } \sec k$ Only 2 stacks max is possible</td>
</tr>
<tr>
<td>10</td>
<td>RO</td>
<td>Advanced Packaging $0 = S t a n d a r d \quad p a c k a g e$ mode for UCIe Link 1 package mode for UCIe Link</td>
</tr>
<tr>
<td>11</td>
<td>RO</td>
<td>68B Flit Format for Streaming Protocol Format is supported for Streaming protocol. This</td>
</tr>
<tr>
<td rowspan="2">12</td>
<td rowspan="2">$R O$</td>
<td>$S t a n d a r d \quad 2 5 6 B \quad E n d \quad H e a d e r \quad F l i t \quad F o r m a t \quad f o r \quad S t r e a m i n g \quad P r o t o c o l$</td>
</tr>
<tr>
<td>If set, indicates Standard 256B End Header Flit Format is supported Streaming protocol. This is only set if at least one of the Protocol Layers is Streaming protocol.</td>
</tr>
<tr>
<td>13</td>
<td>$R O$</td>
<td>Standard 256B Start Header Flit Format for Streaming Protocol If set, indicates Standard 256B Start Header Flit Format is supported for Streaming protocol. This is only set if at least one of the Protocol Layers is Streaming protocol.</td>
</tr>
<tr>
<td rowspan="2">14</td>
<td rowspan="2">RO</td>
<td>Latency-Optimized 256B Flit Format without Optional Bytes for Streaming Protocol</td>
</tr>
<tr>
<td>If set, indicates Latency-Optimized 256B without Optional Bytes Flit Format is supported for Streaming protocol. This is only set if at least one of the Protocol Layers is Streaming protocol.</td>
</tr>
<tr>
<td rowspan="2">15</td>
<td rowspan="2">RO</td>
<td>Latency-Optimized 256B Flit Format with Optional Bytes for Streaming Protocol</td>
</tr>
<tr>
<td>If set, indicates Latency-Optimized 256B with Optional Bytes Flit Format is supported for Streaming protocol. This is only set if at least one of the Protocol Layers is Streaming protocol.</td>
</tr>
<tr>
<td>16</td>
<td>RO</td>
<td>Enhanced Multi-protocol Capable 0 = Not capable of multi-protocol with different protocols $1 = C a p a b l e$ of multi-protocol with different protocols</td>
</tr>
</table>

<table>
<caption>Table 9-8. UCIe Link DVSEC - UCIe Link Capability (Sheet 2 of 2)</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>17</td>
<td>RO</td>
<td>Standard Start Header Flit for PCIe Protocol If set, indicates Standard Start Header 256B Flit Format is supported for PCIe protocol. This is only set if at least one of the Protocol Layers is PCIe protocol.</td>
</tr>
<tr>
<td>18</td>
<td>RO</td>
<td>Latency-Optimized Flit with Optional Bytes for PCIe Protocol If set, indicates that the Latency-Optimized Flit Format with Optional Bytes is supported for PCIe. This is only set if at least one of the Protocol Layers is PCIe protocol.</td>
</tr>
<tr>
<td>19</td>
<td>$R O$</td>
<td>`Runtime Link Testing Parity' Feature Error Signaling If set, design supports signaling errors detected during Runtime link testing with parity as Correctable errors. If cleared, this error signaling mechanism is not supported.</td>
</tr>
<tr>
<td>$2 0$</td>
<td>HWInit</td>
<td>APMW (Advanced Package Module Width) If set, indicates the Advanced Package Module size is x32 or a x64 module operating in x32 mode (decided at integration time). If reset, indicates x64 Advanced Package Module.</td>
</tr>
<tr>
<td>21</td>
<td>RO/RsvdP</td>
<td>x32 Width Support in x64 Module If set, indicates that a x64 Advanced Package Module can operate in x32 mode; otherwise, it cannot operate in x32 mode. For x32 Advanced Package Module, this bit is reserved.</td>
</tr>
<tr>
<td>$2 2$</td>
<td>HWInit</td>
<td>SPMW (Standard Package Module Width) If 1, indicates the Standard Package Module size is a x8 module, or a x16 module operating in x8 mode (decided at integration time). If 0, indicates x16 Standard Package Module.</td>
</tr>
<tr>
<td>23</td>
<td>$R O$</td>
<td>Sideband Performant Mode Operation (PMO) When set, indicates that the sideband supports performant mode operation. When cleared, performant mode operation is not supported.</td>
</tr>
<tr>
<td>24</td>
<td>$R O$</td>
<td>Priority Sideband Packet Transfer (PSPT) When set, indicates that the sideband supports priority sideband packet transfers as defined in Section 4.1.5.2. When cleared, priority sideband packet transfers are not supported.</td>
</tr>
<tr>
<td>25</td>
<td>RO</td>
<td>L2 Sideband Power Down (L2SPD) When set, indicates that L2SPD is supported as defined in Section 4.5.3.9.1. When cleared, L2SPD is not supported.</td>
</tr>
<tr>
<td>$3 1 : 2 6$</td>
<td>$R s v d P$</td>
<td>Reserved</td>
</tr>
</table>

a. This bit was named and referred to as "Multi-stack" in r1.1 and prior revisions of the spec.

## 9.5.1.5 UCIe Link DVSEC - UCIe Link Control (Offset 10h)

Basic UCIe Link control bits are in this register.

<table>
<caption>Table 9-9. UCIe Link DVSEC - UCIe Link Control (Sheet 1 of 3)</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td rowspan="3">0</td>
<td rowspan="3">RW (RP/DSP), HWInit (Others)</td>
<td>Raw Format Enable: If set, enables the Link to negotiate Raw Format during Link training.</td>
</tr>
<tr>
<td>Default value of this is 0b for RP and firmware/SW sets this bit based on system usage scenario.</td>
</tr>
<tr>
<td>Switch DSP can set the default via implementation-specific mechanisms such as straps/FW/etc., to account of system usage scenario (like UCIe retimer). This allows for the DSP Link to train up without Software intervention and be UCIe-unaware-OS compatible.</td>
</tr>
<tr>
<td rowspan="2">1</td>
<td rowspan="2">RW (RP/DSP), RO (EP/DSP), RsvdP (Retimer)</td>
<td>Multi-protocol enableª: When set, multi-protocol training is enabled else not.</td>
</tr>
<tr>
<td>Default is same as 'Multi-protocol Capable' bit in UCIe Link Capability register.</td>
</tr>
<tr>
<td rowspan="6">$5 : 2$</td>
<td rowspan="6">RW (RP/DSP), RsvdP (Others)</td>
<td>Target Link Width</td>
</tr>
<tr>
<td>0h: Reserved 4h: $x 6 4$</td>
</tr>
<tr>
<td>1h: x8 5h: x128</td>
</tr>
<tr>
<td>2h: x16 6h: $\times 2 5 6$</td>
</tr>
<tr>
<td>3h: x32 Others: Reserved</td>
</tr>
<tr>
<td>Default is same as 'Max Link Width' field in UCIe Link Capability register.</td>
</tr>
<tr>
<td rowspan="7">9:6</td>
<td rowspan="7">$\begin{array}{} { \text { RW \left(RP/DSP\right) } } \\ { \text { RSVdP \left(Others\right) } } \end{array} ,$</td>
<td>Target Link Speed</td>
</tr>
<tr>
<td>0h: 4 GT/s 5h: 32 GT/s</td>
</tr>
<tr>
<td>1h: 8 GT/s 6h: 48 GT/s</td>
</tr>
<tr>
<td>$2 h : 1 2 \quad G T / s$ 7h: 64 GT/s</td>
</tr>
<tr>
<td>3h: 16 GT/s Others: Reserved</td>
</tr>
<tr>
<td>4h: 24 GT/s</td>
</tr>
<tr>
<td>Default is same as 'Max Link speed' field in UCIe Link Capability register.</td>
</tr>
<tr>
<td rowspan="3">10</td>
<td rowspan="3">RW, with auto $\begin{array}{} { \text { clear \left(RP/DSP\right) } } \\ { \text { RsvdP \left(Others\right) } } \end{array} ,$</td>
<td>$\begin{array}{} { \text { Start UCIe Link training } - \text { Whet to t to 1, Link traing starts with } } \\ { \text { Control bits orocnram th this this reaister and with the Drotocol laveol lave } } \end{array}$ capabilities. Bit is automatically cleared when Link training completes with either success or error. The status register captures the final status of the Link training. Note that if the Link is up when this bit is set to 1 from 0, the Link will go through full training through Link Down state thus resetting everything beneath the Link. If Link Status (in UCIe Link Status register) is Ob and the link is already in training (i.e., the link training state machine is in between RESET and ACTIVE states), when this bit transitions from 0 to 1, link does not restart the training and this bit's transition from 0 to 1 is ignored.</td>
</tr>
<tr>
<td>Primary usage intended for this bit is for initial Link training out of reset on the host side.</td>
</tr>
<tr>
<td>Note: For downstream ports of a switch with UCIe, local HW/FW has to autonomously initiate Link training after a conventional reset, without waiting for higher level SW to start the training via this bit, to ensure backward compatibility. Default is 0.</td>
</tr>
</table>

<table>
<caption>Table 9-9. UCIe Link DVSEC - UCIe Link Control (Sheet 2 of 3)</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>11</td>
<td>RW with auto clear (RP/DSP), RsvdP (Others)</td>
<td>Retrain UCIe Link - When set to 1, Link that is already up (Link_status=up) will be retrained without going through Link Down state. SW can use this bit to potentially recover from Link errors. If the Link is down (Link_status=down) when this bit is set, there is no effect from this bit being set. SW should use the 'Start UCIe Link training' bit in case the Link is down. The Link_status bit in the status register can be read by software to determine whether to use this bit or not. Note that when retrain happens, the Link speed or width can change because of reliability reasons, and it will be captured through the appropriate status bit in the Link Status register. $B i t \quad i s \quad a u t o m a t i c a l l y \quad c l e a r e d \quad w h e n \quad L i n k \quad r e t r a i n i n g \quad c o m p l e t e s \quad w i t h \quad e i t h e r$ Status register) or if the Link retrain did not happen at all for the reason $D e f a u l t \quad i s \quad 0 .$</td>
</tr>
<tr>
<td>12</td>
<td>RW/RO</td>
<td>Unused - Implementations are encouraged to implement this as an RO bit with a default value of 0. However, for backward compatibility, implementations are permitted to implement this as an RW bit with a default value of 1. Writes to this bit have no effect on link functionality.</td>
</tr>
<tr>
<td>13</td>
<td>RW</td>
<td>68B Flit Format for Streaming Protocol If set, enables 68B Flit Format advertisement if the corresponding capability is supported. Default is same as the '68B Flit Format for Streaming Protocol' bit in the UCIe Link Capability register.</td>
</tr>
<tr>
<td>14</td>
<td>RW</td>
<td>Standard 256B End Header Flit Format for Streaming Protocol If set, enables Standard 256B End Header Flit Format advertisement if the corresponding capability is supported. Default is same as the 'Standard 256B End Header Flit Format for Streaming Protocol' bit in the UCIe Link Capability register.</td>
</tr>
<tr>
<td>15</td>
<td>RW</td>
<td>Standard 256B Start Header Flit Format for Streaming Protocol If set, enables Standard 256B Start Header Flit Format advertisement if the corresponding capability is supported. $\begin{array}{} { \text { Default is same as th } } \\ { \text { Streamina Protocol^{\prime } b } } \end{array}$ 'Standard 256B Start Header Flit Format for bit in the UCIe Link Capability register.</td>
</tr>
<tr>
<td>16</td>
<td>RW</td>
<td>Latency -Optimized 256B Flit Format without Optional Bytes for $I f \quad s e t , e n a b l e s \quad L a t e n c y - O p t i m i z e d \quad 2 5 6 B \quad F l i t \quad F o r m a t \quad w i t h o u t \quad O p t i o n a l$ bytes Default is same as the 'Latency-Optimized 256B Flit Format without for Streaming Protocol' bit in the UCIe Link Capability register.</td>
</tr>
<tr>
<td>17</td>
<td>RW</td>
<td>Latency-Optimized 256B Flit Format with Optional Bytes for Streaming Protocol If set, enables Latency-Optimized 256B Flit Format with Optional bytes advertisement if the corresponding capability is supported. Default is same as the 'Latency-Optimized 256B Flit Format for Streaming Protocol' bit in the UCIe Link Capability register.</td>
</tr>
<tr>
<td>18</td>
<td>RW (RP/DSP), RO (EP/USP), RsvdP (Retimer)</td>
<td>Enhanced Multi-Protocol Enable When set, enhanced multi-protocol training is enabled else not. Enhanced Multi-Protocol permits 2 stacks with the same or different protocols. Default is same as 'Enhanced Multi-Protocol Capable' bit in UCIe Link Capability register.</td>
</tr>
<tr>
<td>19</td>
<td>RW</td>
<td>Standard Start Header Flit for PCIe Protocol If set, enables Standard Start Header 256B Flit Format for PCIe protocol. Default is same as 'Standard Start Header Flit for PCIe Protocol' bit in UCIe Link Capability register.</td>
</tr>
</table>

<table>
<caption>Table 9-9. UCIe Link DVSEC - UCIe Link Control (Sheet 3 of 3)</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>20</td>
<td>RW</td>
<td>Latency-Optimized Flit with Optional Bytes for PCIe Protocol If set, enables the Latency-Optimized Flit Format with Optional Byte for PCIe. Default is same as 'Latency-Optimized Flit with Optional Bytes for PCIe Protocol' bit in UCIe Link Capability register.</td>
</tr>
<tr>
<td>21</td>
<td>RW</td>
<td>Sideband Performant Mode Operation (PMO) When set, Sideband Performant Mode Operation is enabled for negotiation; otherwise, it is not. Default is the same as the corresponding Capability bit.</td>
</tr>
<tr>
<td>22</td>
<td>RW</td>
<td>Priority Sideband Packet Transfer (PSPT) When set, PSPT is enabled for negotiation; otherwise, it is not. Default is the same as the corresponding Capability bit.</td>
</tr>
<tr>
<td>23</td>
<td>RW</td>
<td>L2 Sideband Power Down (L2SPD) When set, L2SPD is enabled for negotiation; otherwise, it is not. Default is the same as the corresponding Capability bit.</td>
</tr>
<tr>
<td>31:24</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

a. This bit was named and referred to as "Multi-stack" in r1.1 and prior revisions of the spec.

## 9.5.1.6 UCIe Link DVSEC - UCIe Link Status (Offset 14h)

Basic UCIe Link status bits are in this register.

<table>
<caption>Table 9-10. UCIe Link DVSEC - UCIe Link Status (Sheet 1 of 3)</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>0</td>
<td>RO</td>
<td>Raw Format Enabled: If set, indicates the Adapter negotiated Raw Format operation with remote Link partner. This bit is only valid when Link Status bit in this register indicates 'Link Up'.</td>
</tr>
<tr>
<td>1</td>
<td>RsvdZ (Retimer), RO (Others)</td>
<td>Multi-protocol enabledª: When set, multi-protocol training has been enabled with remote training partner. This bit is only valid when Link Status bit in this register indicates 'Link Up'.</td>
</tr>
<tr>
<td>2</td>
<td>$\begin{array}{} { \text { Rsvdz \left(Retimer\right) } } \\ { \text { RO \left(Others\right) } } \end{array} ,$</td>
<td>Enhanced Multi-protocol Enabled When set, multi-protocol training has been enabled with remote training partner. This bit is only valid when Link Status bit in this register indicates 'Link Up'.</td>
</tr>
<tr>
<td>3</td>
<td>$R O$</td>
<td>x32 Advanced Package Module Enabled $\begin{array}{} { \text { When set } } \\ { \times 3 2 } \end{array} ,$ indicates that the Advanced Package operating module size is</td>
</tr>
<tr>
<td>$6 : 4$</td>
<td>RsvdZ</td>
<td>Reserved</td>
</tr>
<tr>
<td rowspan="3">10:7</td>
<td rowspan="3">RO</td>
<td>Link Width enabled 0h: $x 4$ 4h: x64 $\begin{array}{} { 1 h : \times 8 } \\ { 2 h : x 1 } \end{array}$ 5h: x128 6h: x256</td>
</tr>
<tr>
<td>$3 h : x 3 2$</td>
</tr>
<tr>
<td>This has meaning only when Link status bit shows Link is up.</td>
</tr>
<tr>
<td rowspan="2">$1 4 : 1 1$</td>
<td rowspan="2">RO</td>
<td>Link Speed enabled 0h: 4 GT/s $5 h : 3 2 \quad G T / s$ $2 h : 1 2 \quad G T / s$ 6h: 48 GT/s 3h: 16 GT/s 7h: 64 GT/s $4 h : 2 4 \quad G T / s$ Others: Reserved</td>
</tr>
<tr>
<td>This field has meaning only when Link status field shows Link is up.</td>
</tr>
</table>

<table>
<caption>Table 9-10. UCIe Link DVSEC - UCIe Link Status (Sheet 2 of 3)</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>15</td>
<td>RO</td>
<td>Link Status 0 - Link is down. 1 - Link is up This bit indicates the status of the mainband. Transitioning a Link from down to up requires a full Link training, which can be achieved using one of these methods: . Start Link training via the bits in the UCIe Link Control register of the upstream device . Using the protocol layer reset bit associated with the Link, like the SBR bit in the BCTL register of the RP P2P space . Using the protocol layer Link Disable bit associated with the Link, like the Link Disable bit in the Link CTL register of the PCIe capability register in the RP P2P space, and then releasing the disable. Notes: If the Link is actively retraining, this bit reflects a value of 1. This bit is a consolidated status of the RDI and FDI (i.e., if both the RDI and FDI are up, then this bit is set to 1; otherwise, this bit is cleared to 0). In multi-stack implementations, this bit is a consolidated status of the RDI and any of the FDIs (i.e., if RDI is up and any of the to 0). FDIs is up, then this bit is set to 1; otherwise, this bit is cleared</td>
</tr>
<tr>
<td>16</td>
<td>RO</td>
<td>Link Training/Retraining 1b - Currently Link is training or retraining 0b - Link is not training or retraining</td>
</tr>
<tr>
<td>17</td>
<td>RW1C (RP/DSP), RsvdZ (Others)</td>
<td>Link Status changed 1b - Link either transitioned from up to down or down to up. $O b \quad - \quad N o \quad L i n k \quad s t a t u s \quad c h a n g e \quad s i n c e \quad t h e \quad l a s t \quad t i m e \quad S W \quad c l e a r e d \quad t h i s \quad b i t$</td>
</tr>
<tr>
<td>18</td>
<td>RW1C (RP/DSP), RsvdZ (Others)</td>
<td>UCIe autonomously changed the Link width or speed to correct $\mathrm { L i n k }$ reliability related issues.</td>
</tr>
<tr>
<td>19</td>
<td>RW1CS</td>
<td>Detected UCIe Link correctable error Further details of specific type of correctable error is found in Table 9-30 register.</td>
</tr>
<tr>
<td>20</td>
<td>RW1CS</td>
<td>Detected UCIe Link Uncorrectable Non-fatal error Further details of specific type of Uncorrectable error is found in Table 9-27 register.</td>
</tr>
<tr>
<td>21</td>
<td>RW1CS</td>
<td>Detected UCIe Link Uncorrectable Fatal error Further details of specific type of Uncorrectable error is found in Table 9-27 register.</td>
</tr>
<tr>
<td>$2 5 : 2 2$</td>
<td>$R O$</td>
<td>Flit Format Status This field and the Flit Format field in the Header Log 2 register in the D2D/PHY register block (see Section 9.5.3.8) are mirror copies. This field indicates the negotiated Flit Format. This field is only valid when Link Status bit in this register indicates 'Link Up'.</td>
</tr>
<tr>
<td>26</td>
<td>$R O$</td>
<td>Sideband Performant Mode Operation (PMO) When set, Sideband Performant Mode Operation was successfully negotiated and is operational. When cleared, legacy mode sideband operation is active. Sideband Performant Mode is not operational. This bit has meaning only when either Link status indicates link is up (in UCIe Link Status register of UCIe Link DVSEC capability) or Table 8-12). management port capability indicates Port Status as 'Link Not Up' (see</td>
</tr>
</table>

<table>
<caption>Table 9-10. UCIe Link DVSEC - UCIe Link Status (Sheet 3 of 3)</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>27</td>
<td>RO</td>
<td>Priority Sideband Packet Transfer (PSPT) When set, PSPT was successfully negotiated and is operational. When cleared, PSPT is not operational.</td>
</tr>
<tr>
<td>28</td>
<td>RO</td>
<td>L2 Sideband Power Down (L2SPD) When set, L2SPD was successfully negotiated and is applicable for L2 entry and L2 exit. When cleared, L2SPD is not applicable.</td>
</tr>
<tr>
<td>31:29</td>
<td>RsvdZ</td>
<td>Reserved</td>
</tr>
</table>

a. This bit was named and referred to as "Multi-stack" in r1.1 and prior revisions of the spec.

## 9.5.1.7 UCIe Link DVSEC - Link Event Notification Control (Offset 18h)

Link event notification related controls are in this register.

<table>
<caption>Table 9-11. UCIe Link DVSEC - Link Event Notification Control</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>0</td>
<td>RW(RP/DSP), RsvdP (Others)</td>
<td>`Link Status changed' UCIe Link Event Interrupt enable 0: Reporting of this event via interrupt is not enabled 1: Reporting of this event via interrupt is enabled. Default is 0</td>
</tr>
<tr>
<td>1</td>
<td>$R W \left( R P / D S P \right) ,$ RsvdP (Others)</td>
<td>`HW autonomous BW changed' UCIe Link Event Interrupt enable 0: Reporting of this event via interrupt is not enabled 1: Reporting of this event via interrupt is enabled Default is 0</td>
</tr>
<tr>
<td>10:2</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
<tr>
<td rowspan="3">$1 5 : 1 1$</td>
<td rowspan="3">RO(RP/DSP), RsvdP(Others)</td>
<td>Link Event Notification Interrupt number This field indicates which MSI vector (for host UCIe Links), or MSI/MSI-X vector (for switch DSP UCIe Links) is used for the interrupt message generated in association with the events that are controlled via this register. For MSI, the value in this field indicates the offset between the base Message Data and the interrupt message that is generated. Hardware is required to update this field so that it is correct if the number of MSI Messages assigned to the Function changes when software writes to the Multiple Message Enable field in the Message Control Register for MSI. For first generation of UCIe, maximum 2 interrupt vectors could be requested for UCIe related functionality and the 'Link event' is one of them.</td>
</tr>
<tr>
<td>For MSI-X (applicable only for interrupts from Switch DSPs with UCIe Links), the value in this field indicates which MSI-X Table entry is used to generate the interrupt message. The entry must be one of the first 32 entries even if the Function implements more than 32 entries. For a given MSI-X implementation, the entry must remain constant.</td>
</tr>
<tr>
<td>For UCIe related interrupts, a switch should request its interrupt requirements from either MSI or MSI-X capability but not both.</td>
</tr>
</table>

## 9.5.1.8 UCIe Link DVSEC - Error Notification Control (Offset 1Ah)

Link error notification related controls are in this register.

Note:
This register only controls the propagation of the error condition and it has no impact
on the setting of the appropriate status bits in the Link Status register, when the
relevant error happens.

<table>
<caption>Table 9-12. UCIe Link DVSEC - Error Notification Control (Sheet 1 of 3)</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td rowspan="5">0</td>
<td rowspan="5">$R W \left( R P / D S P \right) ,$ RsvdP (Others)</td>
<td>`Correctable error detected' protocol layer based reporting enable</td>
</tr>
<tr>
<td>0: Reporting of this error via protocol layer mechanism is not enabled 1: Reporting of this error via protocol layer mechanism is enabled</td>
</tr>
<tr>
<td>Default is 0</td>
</tr>
<tr>
<td>When enabled, the reported PCIe/CXL protocol layer correctable error type is 'Correctable internal error'.</td>
</tr>
<tr>
<td>This bit is applicable for only RP/DSP.</td>
</tr>
<tr>
<td rowspan="11">1</td>
<td rowspan="11">RW</td>
<td>`Correctable error detected' UCIe Link Error Interrupt enable RP/DSP</td>
</tr>
<tr>
<td>0: Reporting of this error via UCIe Link Error interrupt is not enabled 1: Reporting of this error via UCIe Link Error interrupt is enabled</td>
</tr>
<tr>
<td>EP/USP</td>
</tr>
<tr>
<td>0: Reporting of this error via sideband error message is not enabled 1: Reporting of this error via sideband error message is enabled</td>
</tr>
<tr>
<td>Note that in the case of EP/USP connected to a retimer, their sideband error message targets the retimer and how the retimer sends it across to the partner retimer is vendor specific.</td>
</tr>
<tr>
<td>Retimer connected to RP/DSP</td>
</tr>
<tr>
<td>0: Reporting of this error via sideband error message to RP/DSP is not enabled</td>
</tr>
<tr>
<td>1: Reporting of this error via sideband error message to RP/DSP is enabled</td>
</tr>
<tr>
<td>Retimer connected to EP/USP</td>
</tr>
<tr>
<td>0: Reporting of this error to the partner retimer is disabled. 1: Reporting of this error to the partner retimer is enabled. The specific mechanism for reporting the error to the partner retimer is vendor- specific.</td>
</tr>
<tr>
<td>Default is 0</td>
</tr>
<tr>
<td rowspan="3">2</td>
<td rowspan="3">RW(RP/DSP), RsvdP (Others)</td>
<td>`Uncorrectable non-fatal error detected' protocol layer based reporting enable</td>
</tr>
<tr>
<td>0: Reporting of this error via protocol layer mechanism is not enabled 1: Reporting of this error via protocol layer mechanism is enabled Default is 0</td>
</tr>
<tr>
<td>This bit is applicable for only RP/DSP.</td>
</tr>
</table>

<table>
<caption>Table 9-12. UCIe Link DVSEC - Error Notification Control (Sheet 2 of 3)</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td rowspan="12">3</td>
<td rowspan="12">RW</td>
<td>'Uncorrectable non-fatal error detected' UCIe Link Error Interrupt enable</td>
</tr>
<tr>
<td>RP/DSP</td>
</tr>
<tr>
<td>0: Reporting of this error via UCIe Link Error interrupt is not enabled 1: Reporting of this error via UCIe Link Error interrupt is enabled</td>
</tr>
<tr>
<td>EP/USP</td>
</tr>
<tr>
<td>0: Reporting of this error via sideband error message is not enabled 1: Reporting of this error via sideband error message is enabled</td>
</tr>
<tr>
<td>Note that in the case of EP/USP connected to a retimer, their sideband error message targets the retimer and how the retimer sends it across to the partner retimer is vendor specific.</td>
</tr>
<tr>
<td>Retimer connected to RP/DSP</td>
</tr>
<tr>
<td>0: Reporting of this error via sideband error message to RP/DSP is not enabled</td>
</tr>
<tr>
<td>1: Reporting of this error via sideband error message to RP/DSP is enabled</td>
</tr>
<tr>
<td>Retimer connected to EP/USP</td>
</tr>
<tr>
<td>0: Reporting of this error to the partner retimer is disabled.</td>
</tr>
<tr>
<td>1: Reporting of this error to the partner retimer is enabled. The specific mechanism for reporting the error to the partner retimer is vendor specific. Default is 0</td>
</tr>
<tr>
<td rowspan="3">4</td>
<td rowspan="3">RW (RP/DSP), RsvdP (Others)</td>
<td>'Uncorrectable fatal error detected' protocol layer based reporting enable</td>
</tr>
<tr>
<td>0: Reporting of this error via protocol layer mechanism is not enabled 1: Reporting of this error via protocol layer mechanism is enabled Default is 0</td>
</tr>
<tr>
<td>When enabled, the reported PCIe/CXL protocol layer uncorrectable error type is 'Uncorrectable internal error' This bit is applicable for only RP/DSP.</td>
</tr>
</table>

<table>
<caption>Table 9-12. UCIe Link DVSEC - Error Notification Control (Sheet 3 of 3)</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td rowspan="10">5</td>
<td rowspan="10">RW</td>
<td>'Uncorrectable fatal error detected' UCIe Link Error Interrupt enable RP/DSP 0: Reporting of this error via UCIe Link Error interrupt is not enabled 1: Reporting of this error via UCIe Link Error interrupt is enabled</td>
</tr>
<tr>
<td>EP/USP</td>
</tr>
<tr>
<td>0: Reporting of this error via sideband error message is not enabled 1: Reporting of this error via sideband error message is enabled</td>
</tr>
<tr>
<td>Note that in the case of EP/USP connected to a retimer, their sideband error message targets the retimer and how the retimer sends it across to the partner retimer is vendor specific.</td>
</tr>
<tr>
<td>Retimer connected to RP/DSP</td>
</tr>
<tr>
<td>0: Reporting of this error via sideband error message to RP/DSP is not enabled</td>
</tr>
<tr>
<td>1: Reporting of this error via sideband error message to RP/DSP is enabled</td>
</tr>
<tr>
<td>Retimer connected to EP/USP</td>
</tr>
<tr>
<td>0: Reporting of this error to the partner retimer is disabled. 1: Reporting of this error to the partner retimer is enabled. The specific mechanism for reporting the error to the partner retimer is vendor specific.</td>
</tr>
<tr>
<td>Default is 0</td>
</tr>
<tr>
<td>$1 0 : 6$</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
<tr>
<td rowspan="6">$1 5 : 1 1$</td>
<td rowspan="6">RW/RO</td>
<td>Link Error Notification Interrupt number</td>
</tr>
<tr>
<td>This field indicates which MSI vector (for host UCIe Links), or MSI/MSI-X vector (for switch DSP UCIe Links) is used for the interrupt message generated in association with the events that are controlled via this register.</td>
</tr>
<tr>
<td>For MSI, the value in this field indicates the offset between the base Message Data and the interrupt message that is generated. Hardware is required to update this field so that it is correct if the number of MSI Messages assigned to the Function changes when software writes to the Multiple Message Enable field in the Message Control Register for MSI. For first generation of UCIe, maximum 2 interrupt vectors could be requested for UCIe related functionality and the 'Error' is one of them.</td>
</tr>
<tr>
<td>For MSI-X (applicable only for interrupts from Switch DSPs with UCIe Links), the value in this field indicates which MSI-X Table entry is used to generate the interrupt message. The entry must be one of the first 32 entries even if the Function implements more than 32 entries. For a given MSI-X implementation, the entry must remain constant.</td>
</tr>
<tr>
<td>$$\begin{array}{} { \text { For UCIe related interrupts, a switch should request its interupt } } \\ { \text { requirements from either MSI or } M S I \text { or MSI- } x \text { capability but bot bot both. } } \end{array}$$</td>
</tr>
<tr>
<td>It is strongly recommended that this field be implemented as RO but for backward compatibility reasons, it is also permitted to be implemented as RW. This field has no meaning for Switch USP and EP.</td>
</tr>
</table>

### 9.5.1.9 UCIe Link DVSEC - Register Locator 0, 1, 2, 3 Low (Offset 1Ch and when Register Locators 1, 2, 3 are present Offsets 24h, 2Ch, and 34h respectively)

The starting address of the MMIO-mapped register blocks for D2D/PHY, Compliance/Test and
Implementation-specifics are located by SW via these registers.

Note:
All register blocks start with a header section that indicates the size of the block in
multiples of 4 KB.

<table>
<caption>Table 9-13. UCIe Link DVSEC - Register Locator 0, 1, 2, 3 Low</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td rowspan="5">2:0</td>
<td rowspan="5">RO</td>
<td>Register BIR For UCIe DVSEC capability in host UiRB, Switch UiSRB and in UCIe Retimer, this field is reserved. For others, its defined as follows: Indicates which one of a Dev0/Fn0 Base Address Registers, located beginning at 10h in Configuration Space, or entry in the Enhanced Allocation capability with a matching BAR Equivalent Indicator (BEI), is used to map the UCIe Register blocks into Memory Space. Defined encodings are:</td>
</tr>
<tr>
<td>· 0 Base Address Register 10h</td>
</tr>
<tr>
<td>· 1 Base Address Register 14h</td>
</tr>
<tr>
<td>· $2 \quad B a s e \quad A d d r e s s \quad R e g i s t e r \quad 1 8 h$</td>
</tr>
<tr>
<td>· 3 · $\begin{array}{} { 4 \text { Base Address Register } 2 0 h } \\ { 5 \text { Base Address Register } 2 4 h } \end{array}$ • All other Reserved. The Registers block must be wholly contained within the specified BAR. For a 64-bit Base Address Register, the Register BIR indicates the lower DWORD.</td>
</tr>
<tr>
<td rowspan="6">6:3</td>
<td rowspan="6">RO</td>
<td>Register Block Identifier · Identifies the type of UCIe register blocks. Defined encodings are: 0h UCIe D2D/PHY Register Block</td>
</tr>
<tr>
<td>· 1h UCIe Test/Compliance Register Block</td>
</tr>
<tr>
<td>· 2h D2D Adapter Implementation specific register block</td>
</tr>
<tr>
<td>· 3h PHY Implementation specific register block</td>
</tr>
<tr>
<td>. All other encodings are reserved</td>
</tr>
<tr>
<td>The same register block identifier value cannot be repeated in multiple Register Locator entries.</td>
</tr>
<tr>
<td>$1 1 : 7$</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
<tr>
<td>31:12</td>
<td>RO</td>
<td>Register Block Offset Addr[31:12] of the 4-KB aligned offset from the starting address of the Dev0/Fn0 BAR pointed to by the Register BIR field (for EP, Switch USP) or from the start of UiRB/UiSRB region (for hosts/Switch). This field is reserved for retimers.</td>
</tr>
</table>

### 9.5.1.10 UCIe Link DVSEC - Register Locator 0, 1, 2, 3 High (Offset 20h and when Register Locators 1, 2, 3 Are Present Offsets 28h, 30h, and 38h respectively)

Addr[63:32] of the starting address of the MMIO-mapped register blocks for D2D/PHY, Compliance/
Test and Implementation-specifics are located by SW via these registers.

Note:
All register blocks start with a header section that indicates the size of the block in
multiples of 4 KB.

<table>
<caption>Table 9-14. UCIe Link DVSEC - Register Locator 0, 1, 2, 3 High</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>63:32</td>
<td>RO</td>
<td>Register Block Offset Addr[63:32] of the 4-KB aligned offset from the starting address of the Dev0/Fn0 BAR pointed to by the Register BIR field (for EP, Switch USP) or from the start of UiRB/UiSRB region (for hosts/Switch). This field is reserved for retimers.</td>
</tr>
</table>

### 9.5.1.11 UCIe Link DVSEC - Sideband Mailbox Index Low (Offset is design dependent)

Mailbox registers are to be implemented by all hosts with UCIe Links. Switches with downstream UCIe
Links and EP/USP, when paired with UCIe Retimer, should also implement this register. Note that
accesses to mailbox are inherently non-atomic in nature and hence it is up to higher-level software to
coordinate access to any mailbox-related register so that one agent does not step on another agent
using the mailbox mechanism. Those mechanisms for software coordination are beyond the scope of
this specification.

<table>
<caption>Table 9-15. UCIe Link DVSEC - Sideband Mailbox Index Low</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td rowspan="2">$4 : 0$</td>
<td rowspan="2">RW</td>
<td>Opcode 00000b 32b Memory Read 00001b 32b Memory Write 00100b 32b Configuration Read 00101b 32b Configuration Write 01000b 64b Memory Read 01001b 64b Memory Write 01100b 64b Configuration Read 01101b 64b Configuration Write</td>
</tr>
<tr>
<td>OthersReserved Default 00100</td>
</tr>
<tr>
<td>$1 2 : 5$</td>
<td>RW</td>
<td>$B E \left[ 7 : 0 \right]$ Default Fh</td>
</tr>
<tr>
<td rowspan="2">$3 1 : 1 3$</td>
<td rowspan="2">RW</td>
<td>Addr[18:0] of Sideband Accesses Format for this field is as defined in the sideband interface definition in Chapter 7.0.</td>
</tr>
<tr>
<td>Note: The address offset defined as part of this address field is DWORD aligned for 32bit accesses and QWORD aligned for 64bit accesses. Default is 0.</td>
</tr>
</table>

## 9.5.1.12 UCIe Link DVSEC - Sideband Mailbox Index High (Offset is design dependent)

Mailbox registers are to be implemented by all hosts with UCIe Links. Switches with downstream UCIe
Links and EP/USP, when paired with UCIe Retimer, should also implement this register. Note that
accesses to mailbox are inherently non-atomic in nature and hence it is up to higher-level software to
coordinate access to any mailbox-related register so that one agent does not step on another agent
using the mailbox mechanism. Those mechanisms for software coordination are beyond the scope of
this specification.

<table>
<caption>Table 9-16. UCIe Link DVSEC - Sideband Mailbox Index High</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>4:0</td>
<td>RW</td>
<td>Addr[23:19] of Sideband Accesses Format for this field is as defined in the sideband interface definition in Chapter 7.0. Default is 0.</td>
</tr>
<tr>
<td>31:5</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

<table>
<caption>9.5.1.13 UCIe Link DVSEC - Sideband Mailbox Data Low (Offset is design dependent) Table 9-17. UCIe Link DVSEC - Sideband Mailbox Data Low</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>31:0</td>
<td>RW</td>
<td>For sideband write opcodes, this carries the write data [31:0] to the destination. For sideband read opcodes, this carries the data read from the destination when the Write/Read Trigger bit in the Mailbox Control register is cleared, after it was initially set. This field's value is undefined until the Write/Read trigger bit is cleared on reads.</td>
</tr>
</table>

<table>
<caption>9.5.1.14 UCIe Link DVSEC - Sideband Mailbox Data High (Offset is design dependent) Table 9-18. UCIe Link DVSEC - Sideband Mailbox Data High</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>31:0</td>
<td>RW</td>
<td>For sideband write opcodes, this carries the write data [63:32] to the destination. For sideband read opcodes, this carries the data read from the destination when the Write/Read Trigger bit in the Mailbox Control register is cleared, after it was initially set. This field's value is undefined until the Write/Read trigger bit is cleared on reads. $F o r \quad 3 2 b$ Writes/Reads, this register does not carry valid data.</td>
</tr>
</table>

## 9.5.1.15 UCIe Link DVSEC - Sideband Mailbox Control (Offset is design dependent)

<table>
<caption>Table 9-19. UCIe Link DVSEC - Sideband Mailbox Control</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>0</td>
<td>RW, with auto clear</td>
<td>Write/Read trigger: When this bit is written to a 1 from a value of 0, the mailbox generates traffic on the sideband interface, using the contents of the Mailbox Header and Data registers. This bit automatically clears when the write or read access triggered by this bit being set, is complete on the sideband bus. SW can poll this bit to know when the write/read has actually completed at the destination. It can then go read the Mailbox data register for the read data.</td>
</tr>
<tr>
<td>7:1</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

<table>
<caption>9.5.1.16 UCIe Link DVSEC - Sideband Mailbox Status (Offset is design dependent) Table 9-20. UCIe Link DVSEC - Sideband Mailbox Status</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>1:0</td>
<td>RW1C(RP/DSP), RW1C(EP/USP), when implemented</td>
<td>Write/Read status 00b: CA received 01b: UR received 10b: Reserved 11b: Success This bit has valid value only when the Write/Read Trigger bit is cleared from being a 1 prior to it.</td>
</tr>
<tr>
<td>7:2</td>
<td>RsvdZ</td>
<td>Reserved</td>
</tr>
</table>

## 9.5.1.17 UCIe Link DVSEC - Requester ID (Offset is design dependent)

<table>
<caption>Table 9-21. UCIe Link DVSEC - Requester ID</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>23:0</td>
<td>RW(RP)/RsvdP (Others)</td>
<td>Applicable only for host side UCIe Links. Segment No: Bus No: Dev No: Fn No for MSIs triggered on behalf of the associated UCIe Link Note: For MSIs issued on behalf of UCIe Links on downstream ports of switches, the Switch USP BDF is used. UCIe Link DVSEC capabilities in UiSRB implement this as RO 0.</td>
</tr>
<tr>
<td>31:24</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

## 9.5.1.18 UCIe Link DVSEC - Associated Port Numbers (Offset is design dependent)

These registers apply only to UCIe Link DVSEC capabilities present in UiSRB.

<table>
<caption>Table 9-22. UCIe Link DVSEC - Associated Port Numbers</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>7:0</td>
<td>RO</td>
<td>Port Number 1 - 'Port number' of the 1st switch DSP associated with this UCIe. This value is from the Link Capabilities register of that switch DSP.</td>
</tr>
<tr>
<td>15:8</td>
<td>RO</td>
<td>Port Number 2 - 'Port number' of the 2nd switch DSP associated with this UCIe, if any. If there is no 2nd switch DSP associated with this UCIe Link, this field is treated as reserved and should not be included as part of the "length" field of the 'Designated Vendor specific Header 1' register and SW should not consider this as part of the DVSEC capability. Note: Only a maximum of two Port numbers can be associated with a UCIe Link in the current revision of the specification.</td>
</tr>
</table>

## 9.5.1.19 Examples of setting the Length field in DVSEC for various Scenarios

Example#1: UCIe EP supporting 2 Register Locators and not associated with a UCIe-Retimer, would
set the length field in DVSEC capability to indicate 48B.

Example#2: Host UiRB supporting 3 register locators would set the length to indicate 84B.

Example#3: Switch UiSRB supporting 3 register locators and associated with just 1 DSP port to a
UCIe Link, would set the length to indicate 85B.

## 9.5.2 UCIe Switch Register Block (UiSRB) DVSEC Capability

This capability can only be present in the config space of the upstream port of a Switch. There can be
multiple of these in the same USP config space.

### 9.5.2.1 PCI Express Extended Capability Header (Offset 0h)

Set as follows for UCIe Switch Register Block DVSEC. All bits in this register are RO.

<table>
<caption>Table 9-23. UiSRB DVSEC - PCI Express Extended Capability Header</caption>
<tr>
<th>Field</th>
<th>Bit Location</th>
<th>Value</th>
<th>Comments</th>
</tr>
<tr>
<td>Capability ID</td>
<td>15:0</td>
<td>0023h</td>
<td>Value for PCI Express DVSEC capability</td>
</tr>
<tr>
<td>Revision ID</td>
<td>19:16</td>
<td>1h</td>
<td>Latest revision of the DVSEC capability</td>
</tr>
<tr>
<td>Next Capability Offset</td>
<td>31:20</td>
<td>Design Dependent</td>
<td></td>
</tr>
</table>

### 9.5.2.2 Designated Vendor Specific Header 1, 2 (Offsets 4h and 8h)

A few things to note on the various fields described in Table 9-6. DVSEC Revision ID field represents
the version of the DVSEC structure. The DVSEC Revision ID is incremented whenever the structure is
extended to add more functionality. Backward compatibility shall be maintained during this process.
For all values of n, DVSEC Revision ID n+1 structure may extend Revision ID n by replacing fields that
are marked as reserved in Revision ID n, but must not redefine the meaning of existing fields.
Software that was written for a lower Revision ID may continue to operate on UCIe DVSEC structures
with a higher Revision ID, but will not be able to take advantage of new functionality.

All bits in this register are RO.

<table>
<caption>Table 9-24. UiSRB DVSEC - Designated Vendor Specific Header 1, 2</caption>
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
<td>14h</td>
</tr>
<tr>
<td>Designated Vendor-Specific Header 2 (offset 08h)</td>
<td>DVSEC ID</td>
<td>$1 5 : 0$</td>
<td>1h</td>
</tr>
</table>

## 9.5.2.3 UCIe Switch Register Block (UiSRB) Base Address (Offset Ch)

All bits in this register are RO.

<table>
<caption>Table 9-25. UiSRB DVSEC - UiSRB Base Address</caption>
<tr>
<th>Bit</th>
<th>Attributes</th>
<th>Description</th>
</tr>
<tr>
<td>0</td>
<td>RO</td>
<td>Register BIR Indicates which one of a Switch USP Function's Base Address Registers, located beginning at 10h in Configuration Space, or entry in the Enhanced Allocation capability with a matching BAR Equivalent Indicator (BEI), is used to locate the UCIe Switch Register Block. Defined encodings are: · 0 Base Address Register 10h · 1 Base Address Register 14h · All other Reserved. The Registers block must be wholly contained within the specified BAR. For a 64-bit Base Address Register, the Register BIR indicates the lower DWORD.</td>
</tr>
<tr>
<td>11:1</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
<tr>
<td rowspan="2">$6 3 : 1 2$</td>
<td rowspan="2">$R O$</td>
<td>Register Block Offset A 4-KB-aligned offset from the starting address of the Switch USP BAR indicated by the Register BIR field.</td>
</tr>
<tr>
<td>The BAR value + Offset indicated in this register is where the UCIe Switch Register Block (UiSRB) starts. Ex: If this register is 100, UiSRB starts at the &lt;64-bit BAR value + 100000h&gt;</td>
</tr>
</table>

## 9.5.3 D2D/PHY Register Block

These registers occupy 8 KB of register space. The first 4 KB are for the D2D Adapter, and the next 4
KB are for the Physical Layer. In the PHY register block, extended capabilities start at Offset 200h. If
an implementation does not support any extended capabilities, it must implement a NULL capability
at Offset 200h (which implements 0h for the DWORD at that offset). The D2D Adapter registers are
enumerated below. The location of these registers in the system MMIO region is as described in
Section 9.3.

## 9.5.3.1 UCIe Register Block Header

<table>
<caption>Table 9-26. D2D/PHY Register Block - UCIe Register Block Header (Offset 0h)</caption>
<tr>
<th>Bit</th>
<th>Attributes</th>
<th>Description</th>
</tr>
<tr>
<td>15:0</td>
<td>RO</td>
<td>Vendor ID Default is set to Vendor ID assigned for UCIe Consortium - D2DEh</td>
</tr>
<tr>
<td>$3 1 : 1 6$</td>
<td>RO</td>
<td>Vendor ID Register Block Set to 0h to indicate D2D/PHY register block</td>
</tr>
<tr>
<td>$3 5 : 3 2$</td>
<td>RO</td>
<td>Vendor Register Block Version Set to 0h</td>
</tr>
<tr>
<td>63:36</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
<tr>
<td>95:64</td>
<td>RO</td>
<td>Vendor Register Block Length - The number of bytes in the register block including the UCIe Register block header. Default is 2000h.</td>
</tr>
<tr>
<td>127:96</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

## 9.5.3.2 Uncorrectable Error Status Register (Offset 10h)

<table>
<caption>Table 9-27. Uncorrectable Error Status Register (Sheet 1 of 2)</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>0</td>
<td>RW1CS</td>
<td>Adapter Timeout: Set to 1b by hardware if greater than 8ms has $H e a d e r \quad L o g \quad 2 \quad r e g i s t e r \quad c a p t u r e s \quad t h e \quad r e a s o n \quad f o r \quad a \quad t i m e o u t . T h i s \quad e r r o r$ Default Value is 0b.</td>
</tr>
<tr>
<td>1</td>
<td>RW1CS</td>
<td>Receiver Overflow: Set to 1b by hardware if Receiver overflow errors are detected. The Header Log 2 register captures the encoding to indicate the type of Receiver overflow. This error will bring the Link Down. Default Value is 0b.</td>
</tr>
<tr>
<td>2</td>
<td>RW1CS</td>
<td>Internal Error: Set to 1b by hardware if an internal Data path error is detected or if LinkError state was detected on the RDI. Examples of such errors include (but not limited to) uncorrectable error correcting code (ECC) error in the Retry buffer, sideband parity errors etc. This error will bring the Link Down. It includes fatal error indicated by the Physical Layer that brought the Link Down. Default Value is 0b.</td>
</tr>
<tr>
<td>3</td>
<td>RW1CS (RP/DSP/ $\begin{array}{} { \left. \text { Ketmer } \right) } \\ { \text { Rsvdz \left(Others\right) } } \end{array}$</td>
<td>Sideband Fatal Error Message received: Set to 1b by hardware if the Adapter received a Fatal {ErrMsg} sideband message. Default Value is 0b.</td>
</tr>
</table>

<table>
<caption>Table 9-27. Uncorrectable Error Status Register (Sheet 2 of 2)</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>4</td>
<td>RW1CS(RP/DSP/ $\begin{array}{} \left. \mathrm { R e t i m e r } \right) _ { \prime } \\ \mathrm { R s v d } Z \left( \mathrm { O t h e r s } \right) \end{array}$</td>
<td>Sideband Non-Fatal Error Message received: Set to 1b by hardware if the Adapter received a Non-Fatal {ErrMsg} sideband message. Default Value is 0b.</td>
</tr>
<tr>
<td>5</td>
<td>RW1CS</td>
<td>Invalid Parameter Exchange: Set to 1b if the Adapter was not able to determine a valid protocol or Flit Format for operation.</td>
</tr>
<tr>
<td>31:6</td>
<td>RsvdZ</td>
<td>Reserved</td>
</tr>
</table>

## 9.5.3.3 Uncorrectable Error Mask Register (Offset 14h)

The Uncorrectable Error Mask Register controls reporting of individual errors. When a bit is 1b in this
register, the corresponding error status bit in the Uncorrectable Error Status register is not forwarded
to the Protocol Layer for escalation/signaling but it does not impact error logging in the "First Fatal
Error Indicator" field in the Header Log 2 register.

<table>
<caption>Table 9-28. Uncorrectable Error Mask Register</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>0</td>
<td>RWS</td>
<td>Adapter Timeout Mask Default Value is 1b.</td>
</tr>
<tr>
<td>1</td>
<td>RWS</td>
<td>Receiver Overflow Mask Default Value is 1b.</td>
</tr>
<tr>
<td>2</td>
<td>RWS</td>
<td>Internal Error Mask Default Value is 1b.</td>
</tr>
<tr>
<td>3</td>
<td>RWS</td>
<td>Fatal Error Message received Mask $D e f a u l t \quad V a l u e \quad i s \quad 1 b .$</td>
</tr>
<tr>
<td>4</td>
<td>RWS</td>
<td>Non-Fatal Error Message received Mask $D e f a u l t \quad V a l u e \quad i s \quad 1 b .$</td>
</tr>
<tr>
<td>5</td>
<td>RWS</td>
<td>Invalid Parameter Exchange Mask Default Value is 1b.</td>
</tr>
<tr>
<td>31:6</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

## 9.5.3.4 Uncorrectable Error Severity Register (Offset 18h)

The Uncorrectable Error Severity register controls whether an individual error is reported as a Non-
fatal or Fatal error. An error is reported as a fatal uncorrectable error when the corresponding bit in
the severity register is 1b. If the bit is 0b, the corresponding error is reported as a non-fatal
uncorrectable error.

<table>
<caption>Table 9-29. Uncorrectable Error Severity Register</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>0</td>
<td>RWS</td>
<td>Adapter Timeout Severity Default Value is 1b.</td>
</tr>
<tr>
<td>1</td>
<td>RWS</td>
<td>Receiver Overflow Severity Default Value is 1b.</td>
</tr>
<tr>
<td>2</td>
<td>RWS</td>
<td>Internal Error Severity Default Value is 1b.</td>
</tr>
<tr>
<td>3</td>
<td>RWS</td>
<td>Sideband Fatal Error Message received Severity Default Value is 1b.</td>
</tr>
<tr>
<td>4</td>
<td>RWS</td>
<td>Sideband Non-Fatal Error Message received Severity Default Value is 0b.</td>
</tr>
<tr>
<td>5</td>
<td>RWS</td>
<td>Invalid Parameter Exchange Severity Default Value is 1b</td>
</tr>
<tr>
<td>31:6</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

### 9.5.3.5 Correctable Error Status Register (Offset 1Ch)

<table>
<caption>Table 9-30. Correctable Error Status Register</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>0</td>
<td>RW1CS</td>
<td>CRC Error Detected: Set to 1b by hardware if the Adapter detected a CRC Error when Adapter Retry was negotiated with remote Link partner. Default Value is 0b.</td>
</tr>
<tr>
<td>1</td>
<td>RW1CS</td>
<td>Adapter LSM transition to Retrain: Set to 1b by hardware if the Adapter LSM transitioned to Retrain state. Default Value is 0b.</td>
</tr>
<tr>
<td>2</td>
<td>RW1CS</td>
<td>Correctable Internal Error: Set to 1b by hardware if an internal correctable Data path error is detected. Examples of such errors include (but are not limited to) correctable error correcting code (ECC) error in the Retry buffer, Physical Layer indicated correctable error on RDI, etc. Default Value is 0b.</td>
</tr>
<tr>
<td>3</td>
<td>RW1CS (RP/DSP/ $\begin{array}{} { \left. \text { Retimer } \right) } \\ { \text { Revdz \left(Others\right) } } \end{array}$</td>
<td>Set to 1b by $\begin{array}{} { \text { Sideband Correctable Error iersed a Correctable \left\{Errime sideband } } \\ { \text { hardware if the Adapter received a Corred in the message information. } } \\ { \text { messaqe with Device origin encoding the message information. } } \end{array}$ Default Value is 0b.</td>
</tr>
<tr>
<td>4</td>
<td>RW1CS</td>
<td>`Runtime Link Testing Parity' Error</td>
</tr>
<tr>
<td>31:5</td>
<td>RsvdZ</td>
<td>Reserved</td>
</tr>
</table>

### 9.5.3.6 Correctable Error Mask Register (Offset 20h)

The Correctable Error Mask Register controls the reporting of individual errors. When a bit is 1b in this
register, setting of the corresponding error status bit is not forwarded to the Protocol Layer for
escalation/signaling.

<table>
<caption>Table 9-31. Correctable Error Mask Register</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>0</td>
<td>RWS</td>
<td>CRC Error Detected Mask Default Value is 1b.</td>
</tr>
<tr>
<td>1</td>
<td>RWS</td>
<td>Adapter LSM transition to Retrain Mask Default Value is 1b.</td>
</tr>
<tr>
<td>2</td>
<td>RWS</td>
<td>Correctable Internal Error Mask Default Value is 1b.</td>
</tr>
<tr>
<td>3</td>
<td>RWS</td>
<td>Device Correctable Error Message received Mask Default Value is 1b.</td>
</tr>
<tr>
<td>4</td>
<td>RWS</td>
<td>`Runtime Link Testing Parity' Error Mask Default Value is 1b.</td>
</tr>
<tr>
<td>31:5</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

## 9.5.3.7 Header Log 1 Register (Offset 24h)

This register is used to log the header on sideband register accesses that receive UR/CA error status.

<table>
<caption>Table 9-32. Header Log 1 Register</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td rowspan="3">$6 3 : 0$</td>
<td rowspan="3">ROS</td>
<td>Header Log 1: This logs the header for the sideband mailbox register access that received a completion with Completer Abort status or received a completion with Unsupported Request status. Note that register accesses that time out are not required to be</td>
</tr>
<tr>
<td>$\begin{array}{} { \text { Iogged at the requester. } } \\ { \text { If the Write/Read Status field in the the band Mailbox status } ^ { \prime } } \end{array}$ register indicates 'Success' or the Write/Read Sideband Mailbox Control register is set to 1, this field's value is undefined.</td>
</tr>
<tr>
<td>$\begin{array}{} { \text { This register is rearmed for logging newrors every time the } } \\ { \text { Write/Read Trigger bit in the Maibox Control register sees a O-to- } } \end{array}$ transition. Default Value is 0.</td>
</tr>
</table>

## 9.5.3.8 Header Log 2 Register (Offset 2Ch)

This register is used to log syndrome of various sideband and mainband errors and specific status
logging on link training.

<table>
<caption>Table 9-33. Header Log 2 Register (Sheet 1 of 2)</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>3:0</td>
<td>ROS</td>
<td>Adapter Timeout encoding: Captures the reason for the first Adapter Timeout that was logged in Uncorrectable Error Status. Default Value is 0000b. The encodings are interpreted as follows: 0001b: Parameter Exchange flow timed out $0 0 1 0 b : A d a p t e r \quad L S M \quad r e q u e s t \quad t o \quad r e m o t e \quad L i n k \quad p a r t n e r \quad d i d \quad n o t \quad r e c e i v e$ that did not receive a response. Bit 10 of this register captures which Adapter LSM timed out. 0011b: Adapter LSM transition to Active timeout. This is recorded in case the Adapter never received Active Request from remote Link partner for 8 ms after sending an Active Request on sideband even though it received an Active Response. Bit 10 of this register captures which Adapter LSM timed out. 0100b: Retry Timeout - no Ack or Nak $\begin{array}{} { \text { Retry was enabled. Timeout counter is only incrented wher RDI } } \\ { \text { is in Active and Adapter } s \text { Retry buffer is not empty. } } \end{array}$ 0101b: Local sideband access timeout $\begin{array}{} { \text { O110b: Retimer credit return timeout- no Retimer credit received } } \\ { \text { for greater than } 8 \text { ms if one or more Retimer credits have been } } \end{array}$ consumed by the Adapter. This timer is only counting during Active this timer must be Reset since the $\begin{array}{} { \text { state. If RDI moves to Retrain } } \\ { \text { Retimer credits are also Reset } } \end{array} .$ $\begin{array}{} { \text { O111b: Remote Register Access timeout. This is triggered when if } } \\ { \text { the Adapter has observed Ntimeout for Register Accesses where } } \\ { \text { is } > = \text { register access timeout threshold. } } \end{array}$ other encodings are reserved. If the Adapter Timeout status bit is cleared in the 'Uncorrectable Error Status' register, this field's value is undefined.</td>
</tr>
<tr>
<td>6:4</td>
<td>ROS</td>
<td>Receiver Overflow encoding: Captures the encoding for the first Receiver overflow error that occurred. interpreted as follows: $0 0 1 b : T r a n s m i t t e r \quad R e t r y \quad B u f f e r \quad o v e r f l o w$ 010b: Retimer Receiver Buffer overflow overflow $1 0 0 b : R D I \quad s i d e b a n d \quad b u f f e r \quad o v e r f l o w$ other encodings are reserved. If the Receiver overflow status bit is cleared in the 'Uncorrectable Error Status' register, this field's value is undefined.</td>
</tr>
<tr>
<td>9:7</td>
<td>$R O S$</td>
<td>Adapter LSM response type 001b: Active 100b: LinkReset $0 1 0 b : L 1$ $\begin{array}{} { \text { 101b: Disable } } \\ { \text { Other encodings are reserved } } \end{array}$ If the Adapter Timeout status bit is cleared in the 'Uncorrectable Error Status' register, this field's value is undefined.</td>
</tr>
<tr>
<td>10</td>
<td>$R O S$</td>
<td>Adapter LSM id $1 b : A d a p t e r \quad L S M \quad 1 \quad t i m e d \quad o u t$</td>
</tr>
<tr>
<td>$1 2 : 1 1$</td>
<td>RsvdZ</td>
<td></td>
</tr>
<tr>
<td>13</td>
<td>$R O$</td>
<td>Parameter Successful: Hardware updates this bit to $\begin{array}{} { \text { 1b after successfulp } } \\ { \text { on every link traininc } } \end{array}$ Parameter exchange with remote Link partner,</td>
</tr>
</table>

<table>
<caption>Table 9-33. Header Log 2 Register (Sheet 2 of 2)</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td rowspan="5">$1 7 : 1 4$</td>
<td rowspan="5">ROS</td>
<td>Flit Format: This field logs the negotiated Flit Format, it is the current snapshot of the format the Adapter is informing to the Protocol Layer. See Chapter 3.0 for the definitions of these formats. The encodings are:</td>
</tr>
<tr>
<td>0001b - Format 1 0101b - Format 5</td>
</tr>
<tr>
<td>0010b - Format 2 0110b - Format 6</td>
</tr>
<tr>
<td>$0 0 1 1 b \quad - \quad F o r m a t$ 3 Other encodings are Reserved</td>
</tr>
<tr>
<td>0100b - Format 4</td>
</tr>
<tr>
<td rowspan="4">$2 2 : 1 8$</td>
<td rowspan="4">$R O S$</td>
<td>bit $\begin{array}{} { \text { First Fatal Error Indicator: } 5 \text { -bit encoding that indicat whe value of } } \\ { \text { of Uncorrectable Error Stratus errors warrs waged first } \text { first vatue value of } } \\ { \text { this field has no meaning if thresporonding status bit is cleare } } \end{array}$ The encoding of this field is as follows: $\begin{array}{} { \text { OOh if the error corresponding to Uncorrectable Error Status } } \\ { \text { reaister } 0 1 \text { is the first fatal error. } } \end{array}$</td>
</tr>
<tr>
<td>$\begin{array}{} { \text { O1h if the error corresponding to Uncorrectable Error Status } } \\ { \text { reaister } 1 1 \text { is the first fatal error } } \end{array}$</td>
</tr>
<tr>
<td>... Because reserved bits may be repurposed in future versions of the $\begin{array}{} \text { specitication, sortiware mignte obserive that the the the points to a } \\ \text { reserved bit } \text { \left(from its perspective\right) in the Uncorrectable Etrors tatus } \\ \text { register. This can happen when older version of softuware is ritware is } \end{array}$ on newer hardware. Software must be aware that it still needs to $\begin{array}{} { \text { clear the Status register bit it destres to allow for continued error } } \\ { \text { logging. How swhar har error status bits it oot not underand is } } \end{array}$ Once set, the value of this field does not change until SW clears the corresponding Uncorrectable Status register bit. When SW $\begin{array}{} { \text { clears the corres } } \\ { \text { subseauent first } } \end{array}$ $\log ,$ HW is rearmed to capture fatal</td>
</tr>
<tr>
<td>Note that because of an inherent race condition between HW setting a new status bit and SW clearing an older status bit, SW must be aware that this field might not always indicate the first error amongst all the errors logged in the Uncorrectable Error Status register. For example, if the Uncorrectable Error Status bit 0 was set first by HW and in the time SW reads the status and cleared it, bit 1 $\begin{array}{} { \text { corresponding to bit } 0 \text { recurs, it will be captured as the next first } } \\ { \text { error even though the errorcorresponding to bit } 1 \text { occurred ear earlit } } \end{array}$ If multiple errors are encountered simultaneously, which error is logged as the First Fatal Error is implementation-dependent.</td>
</tr>
<tr>
<td>31:23</td>
<td>RsvdZ</td>
<td>Reserved</td>
</tr>
</table>

## 9.5.3.9 Error and Link Testing Control Register (0ffset 30h)

<table>
<caption>Table 9-34. Error and Link Testing Control Register</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>3:0</td>
<td>RW</td>
<td>Remote Register Access Threshold: Indicates the number of consecutive timeouts for remote register accesses that must occur before the Register Access timeout is logged and the error escalated to a Link_Status=Down condition. Default Value is 0100b.</td>
</tr>
<tr>
<td>4</td>
<td>RW</td>
<td>Runtime Link Testing Tx Enable: Software writes to this bit to enable Parity byte injections in the data stream as described in Section 3.9. Runtime Link Rx Enable must be set to 1b for remote Link Partner for successful enabling of this mode. Default Value is 0b.</td>
</tr>
<tr>
<td>5</td>
<td>RW</td>
<td>Runtime Link Testing Rx Enable: Software writes to this bit to enable Parity byte checking in the data stream as described in Section 3.9. Runtime Link Tx Enable must be set to 1b for remote Link Partner for successful enabling of this mode. Default Value is 0b.</td>
</tr>
<tr>
<td>8:6</td>
<td>RW</td>
<td>Number of 64 Byte Inserts: Software writes to this to indicate the number 64 Byte inserts are done at a time for Runtime Link Testing. The encodings are: 000b: one 64B insert (for debug purposes only) $0 0 1 b : t w o \quad 6 4 B \quad i n s e r t s \left( f o r \quad d e b u g \quad p u r p o s e s \quad o n l y \right)$ Other encodings are reserved. Default value is 000b. See Section 3.9 for guidance on how Software should set this field.</td>
</tr>
<tr>
<td>9</td>
<td>RW1C</td>
<td>Parity Feature Nak received: Hardware updates this bit if it receives a Nak from remote Link partner when attempting to enable Runtime Link Testing.</td>
</tr>
<tr>
<td>$1 2 : 1 0$</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
<tr>
<td>$1 4 : 1 3$</td>
<td>RW</td>
<td>CRC Injection Enable: Software writes to this bit to trigger CRC error injections, The error is injected by inverting 1, 2 or 3 bits in the CRC bytes. The specific bits inverted are implementation specific. The CRC injection must not happen for Flits that are already inverting CRC bits for Viral handling. The encodings are interpreted as: $\begin{array}{} { \text { OOb: CRC Injection is Disabled } } \\ { 0 1 b : 1 \text { bit is inverted } } \end{array} .$ 10b: 2 bits are inverted 11b: 3 bits are inverted. Default Value is 00b.</td>
</tr>
<tr>
<td>$1 6 : 1 5$</td>
<td>RW</td>
<td>CRC Injection Count: Software writes to this bit to program the number of CRC injections. It only takes effect if CRC injection Enable is not Disabled. 00b: Single Flit is corrupted. CRC Injection Busy is reset to 0b after single Flit corruption. $\begin{array}{} { \text { O1b: A CRC error is injected every } 8 \text { Flits. Hardware continues to inject a CRC } } \\ { \text { error every 8 Flits until CRC Injection Enable is OOb. CRC Injection Busy is } } \end{array}$ reset to Ob only after CRC Injection Enable is 00b. $\begin{array}{} { 1 0 b : A \text { CRC error is injected every } 1 6 \text { Filte } } \\ { \text { CRC error every } 1 6 \text { Flits until CRC Injection Enable is OOb. } } \\ { \text { is reset to 0b only after CRC Injection Enable is OOb } } \end{array}$ $1 1 b : A \quad C R C \quad e r r o r \quad i s \quad i n j e c t e d \quad e v e r y \quad 6 4 \quad F l i t s . H a r d w a r e \quad c o n t i n u e s \quad t o \quad i n j e c t \quad a$ CRC error every 64 Flits until CRC Injection Enable is 00b. CRC Injection Busy is reset to Ob only after CRC Injection Enable is 00b.</td>
</tr>
<tr>
<td>17</td>
<td>$R O$</td>
<td>CRC Injection Busy: Hardware loads a 1b to this bit once it has begun CRC Injection. Software is permitted to poll on this bit. See CRC Injection Count description to see how this bit returns to 0b.</td>
</tr>
<tr>
<td>$3 1 : 1 8$</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

## 9.5.3.10 Runtime Link Testing Parity Log 0 (Offset 34h)

<table>
<caption>Table 9-35. Runtime Link Testing Parity Log 0 Register</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>63:0</td>
<td>RW1C</td>
<td>Parity Log for UCIe-S or (UCIe-A Module 0): Hardware updates the bit corresponding to the parity error byte with error over the period when Runtime Link Testing was enabled at the Rx. The Adapter sets the bit corresponding to the RDI byte number with an error modulo the number of Lanes in the Link as indicated by pl_Ink_cfg. For example, if RDI Byte 18 has an error of a x16 Link, bit [2] of this register would be set to 1. Because UCIe-S configurations cannot exceed a maximum of 64 Lanes, this register is used for all configurations of UCIe-S. For UCIe-A, the Adapter sets the corresponding bit if the result of the modulo operation was less than 64. Default Value is 0.</td>
</tr>
</table>

## 9.5.3.11 Runtime Link Testing Parity Log 1 (Offset 3Ch)

<table>
<caption>Table 9-36. Runtime Link Testing Parity Log 1 Register</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>63:0</td>
<td>RW1C</td>
<td>Parity Log for UCIe-A Module 1: Hardware updates the bit corresponding to the parity error byte with error over the period when Runtime Link Testing was enabled at the Rx. Default Value is 0. This is register is only applicable if the Adapter is designed for handling two or more Physical Layer modules for UCIe-A. It is reserved otherwise. The Adapter sets the bit corresponding to the RDI byte number with an error modulo the number of Lanes in the Link as indicated by pl_lnk_cfg, if the result of the modulo operation is greater than 63 but less than 128.</td>
</tr>
</table>

## 9.5.3.12 Runtime Link Testing Parity Log 2 (Offset 44h)

<table>
<caption>Table 9-37. Runtime Link Testing Parity Log 2 Register</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>63:0</td>
<td>RW1C</td>
<td>Parity Log for UCIe-A Module 2: Hardware updates the bit corresponding to the parity error byte with error over the period when Runtime Link Testing was enabled at the Rx. Default Value is 0. This is register is only applicable if the Adapter is designed for handling four Physical Layer modules for UCIe-A. It is reserved otherwise. The Adapter sets the bit corresponding to the RDI byte number with an error modulo the number of Lanes in the Link as indicated by pl_Ink_cfg, if the result of the modulo operation is greater than 127 but less than 192.</td>
</tr>
</table>

## 9.5.3.13 Runtime Link Testing Parity Log 3 (Offset 4Ch)

<table>
<caption>Table 9-38. Runtime Link Testing Parity Log 3 Register</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>63:0</td>
<td>RW1C</td>
<td>Parity Log for UCIe-A Module 3: Hardware updates the bit corresponding to the parity error byte with error over the period when Runtime Link Testing was enabled at the Rx. Default Value is 0. This is register is only applicable if the Adapter is designed for handling four Physical Layer modules for UCIe-A. It is reserved otherwise. The Adapter sets the bit corresponding to the RDI byte number with an error modulo the number of Lanes in the Link as indicated by pl_Ink_cfg, if the result of the modulo operation is greater than 191 but less than 256.</td>
</tr>
</table>

## 9.5.3.14 Advertised Adapter Capability Log (Offset 54h)

<table>
<caption>Table 9-39. Advertised Adapter Capability Log Register</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>63:0</td>
<td>RW1C</td>
<td>Advertised Adapter Capability: Hardware updates the bits corresponding to the data bits it sent in the {AdvCap.Adapter} sideband message. Default Value is 0.</td>
</tr>
</table>

## 9.5.3.15 Finalized Adapter Capability Log (Offset 5Ch)

<table>
<caption>Table 9-40. Finalized Adapter Capability Log Register</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>63:0</td>
<td>RW1C</td>
<td>Finalized Adapter Capability: Hardware updates the bits corresponding to the data bits it sent (DP) or received (UP) in the {FinCap.Adapter} sideband message. Default Value is 0.</td>
</tr>
</table>

## 9.5.3.16 Advertised CXL Capability Log (Offset 64h)

<table>
<caption>Table 9-41. Advertised CXL Capability Log Register</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>63:0</td>
<td>RW1C</td>
<td>Advertised CXL Capability: Hardware updates the bits corresponding to the data bits it sent in the {AdvCap.CXL} sideband message, when it is sent with MsgInfo=0000h. Default Value is 0.</td>
</tr>
</table>

## 9.5.3.17 Finalized CXL Capability Log (Offset 6Ch)

<table>
<caption>Table 9-42. Finalized CXL Capability Log Register</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>63:0</td>
<td>RW1C</td>
<td>Finalized CXL Capability: Hardware updates the bits corresponding to the data bits it sent (DP) or received (UP) in the {FinCap.CXL} sideband message, when it is sent with MsgInfo=0000h. Default Value is 0.</td>
</tr>
</table>

## 9.5.3.18 Advertised Multi-Protocol Capability Log Register (Offset 78h)

This register is reserved for designs that do not implement the Enhanced Multi-protocol capability.

<table>
<caption>Table 9-43. Advertised Multi-Protocol Capability Log Register</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>63:0</td>
<td>RW1C</td>
<td>Advertised Multi-Protocol Capability: Hardware updates the bits corresponding to the data bits it sent in the { MultiProtAdvCap.Adapter} sideband message. Default value is 0.</td>
</tr>
</table>

## 9.5.3.19 Finalized Multi-Protocol Capability Log Register (Offset 80h)

This register is reserved for designs that do not implement the Enhanced Multi-protocol capability.

<table>
<caption>Table 9-44. Finalized Multi-Protocol Capability Log Register</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>63:0</td>
<td>RW1C</td>
<td>Finalized Multi-Protocol Capability: Hardware updates the bits corresponding to the data bits it sent in the { MultiProtFinCap.Adapter} sideband message. Default value is 0.</td>
</tr>
</table>

## 9.5.3.20 Advertised CXL Capability Log Register for Stack 1 (Offset 88h)

This register is reserved for designs that do not implement the Enhanced Multi-protocol capability.

<table>
<caption>Table 9-45. Advertised CXL Capability Log Register for Stack 1</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>63:0</td>
<td>RW1C</td>
<td>Advertised CXL Capability: Hardware updates the bits corresponding to the data bits it sent in the {AdvCap.CXL} sideband message when it is sent with MsgInfo=0001h. Default value is 0.</td>
</tr>
</table>

## 9.5.3.21 Finalized CXL Capability Log Register for Stack 1 (Offset 90h)

This register is reserved for designs not implementing the Enhanced multi-protocol capability.

<table>
<caption>Table 9-46. Finalized CXL Capability Log Register for Stack 1</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>63:0</td>
<td>RW1C</td>
<td>Finalized CXL Capability: Hardware updates the bits corresponding to the data bits it sent in the {FinCap.CXL} sideband message when it is sent with MsgInfo=0001h. Default value is 0.</td>
</tr>
</table>

## 9.5.3.22 PHY Capability (Offset 1000h)

This register is global, and not per module.

<table>
<caption>Table 9-47. Physical Layer Capability Register</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>$2 : 0$</td>
<td>$R O$</td>
<td>Reserved</td>
</tr>
<tr>
<td>3</td>
<td>$R O$</td>
<td>Terminated Link If set to 1, the Receiver supports termination. See Section 5.4.2 for additional information and the termination requirements for different maximum supported data rate and channel length combinations.</td>
</tr>
<tr>
<td>4</td>
<td>$R O$</td>
<td>TX Equalization support 0: TXEQ not supported 1: TXEQ supported</td>
</tr>
<tr>
<td>$9 : 5$</td>
<td>RO</td>
<td>Supported Tx Vswing encodings 01h: 0.4 V 07h: 0.7 V 0Dh: 1.0 V 02h: 0.45 V 08h: 0.75 V 0Eh: 1.05 V $0 3 h : 0 . 5 \quad V$ 09h: 0.8 V 0Fh: 1.1 V 0.55 V $O A h : 0 . 8 5 \quad V$ 10h: 1.15 V $0 5 h : 0 . 6 \quad V$ 06h: 0.65 V $0 C h : 0 . 9 5 \quad V$ All other encodings are reserved. This field matches the value advertised by the UCIe Module in the 'Voltage swing' field during MBINIT.PARAM.</td>
</tr>
<tr>
<td>10</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
<tr>
<td>$1 2 : 1 1$</td>
<td>$R O$</td>
<td>Rx Clock Mode Support for &lt;= 32 GT/s $\begin{array}{} { \text { 00b: Supports both free running and strobe modes } } \\ { 1 0 b : \text { Free running mode only } } \end{array}$ All other encodings are reserved. This reflects the local UCIe Module's capability when the operating speed is $< = 3 2$ GT/s (including the situation where &gt; 32 GT/s was negotiated but the Link went $\begin{array}{} { \text { through a speed degrade and is operating } } \\ { \text { Rx Clock Phase Support for } < = 3 2 \text { GT/ } } \end{array}$ at a speed &lt;= 32 GT/s).</td>
</tr>
<tr>
<td>14:13</td>
<td>$R O$</td>
<td>00b: Differential clock only (all data rates) 01b: $\begin{array}{} { \text { Quadrature clock } \left( 2 4 / 3 2 \text { GT/s\right) } \right. } \\ { \text { Differential clock } \left( 1 6 G T / s \text { and lower\right) } \right. } \end{array}$ 10b: Same as 01b (for backward compatibility) This reflects the local UCIe Module's capability when the operating speed is &lt;= 32 GT/s (including the situation where &gt; 32 GT/s was negotiated but the Link went through a speed degrade and is operating at a speed &lt;= 32 GT/s).</td>
</tr>
<tr>
<td>15</td>
<td>$R O$</td>
<td>Package type 0b: Advanced Package 1b: Standard Package</td>
</tr>
<tr>
<td>16</td>
<td>$R O$</td>
<td>Tightly coupled mode (TCM) support 0b: TCM not supported 1b: TCM supported This corresponds to the local UCIe Module's capability.</td>
</tr>
<tr>
<td>17</td>
<td>RO</td>
<td>Tx Adjustment for Runtime Recalibration (TARR) $\begin{array}{} { \text { O: TARR is not supportea } } \\ { 1 : \text { TARR is supported \left(see Section 4.6 for details\right) } } \end{array}$</td>
</tr>
<tr>
<td>$3 1 : 1 8$</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

## 9.5.3.23 PHY Control (Offset 1004h)

This register is global, and not per module.

<table>
<caption>Table 9-48. Physical Layer Control Register (Sheet 1 of 2)</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>$2 : 0$</td>
<td>$R W / R O$</td>
<td>Reserved. Implementations are encouraged to implement this as an RO bit with a default value of 000b. However, for backward compatibility, implementations are permitted to implement this as an RW bit with a default value of 000b.</td>
</tr>
<tr>
<td>3</td>
<td>RW</td>
<td>$R x \quad T e r m i n a t e d \quad C o n t r o l$ 0: Rx Termination disabled 1: Rx Termination enabled Default is same as 'Terminated Link' bit in PHY capability register. $\begin{array}{} { \text { Note that this bit is always cle } } \\ { \text { rate supported is } < = 3 2 \text { GT/s } } \end{array}$ to 0 for Advanced Packages if the maximum data This control is provided for debug purposes only.</td>
</tr>
<tr>
<td>4</td>
<td>$R W$</td>
<td>Tx Eq Enable 0: Eq Disabled $\begin{array}{} { 1 : \text { Eq Enabled } } \\ { \text { Default is } 0 } \end{array}$ Note that this field only affects hardware behavior while the operating data rate is &lt;= 32 GT/s. When the operating data rate is &gt; 32 GT/s, Tx equalization will be enabled regardless of the setting of this bit.</td>
</tr>
<tr>
<td>5</td>
<td>RW</td>
<td>Rx Clock Mode Select 0: Strobe Mode 1: Free running mode Default is 0 if the Rx of the local UCIe Module supports Strobe Mode; otherwise, the bit is set to 1. This control is provided for debug purposes only. This bit is sent as the 'Clock Mode' bit in the {MBINIT.PARAM configuration req} sideband message. Note that this field only affects hardware behavior while the operating data rate is &lt;= 32 GT/s. When the operating data rate is &gt; 32 GT/s, the Rx Clock will use free running mode regardless of the setting of this bit.</td>
</tr>
<tr>
<td>6</td>
<td>RW</td>
<td>Rx Clock phase support select 0: Differential clock only (all data rates &lt;= 32 GT/s) $\begin{array}{} { \text { 1: Quadrature clock } \left( 2 4 / 3 2 \text { GT/s\right) } \right. } \\ { \text { Differential clock } \left( 1 6 G T / s \text { and lower\right) } \right. } \end{array}$ $T h i s \quad c o n t r o l \quad i s \quad p r o v i d e d \quad f o r \quad d e b u g \quad p u r p o s e s \quad o n l y . T h i s \quad b i t \quad i s \quad s e n t \quad a s \quad t h e C l o c k \quad P h a s e$ Note that this field only affects hardware behavior while the operating data rate is &lt;= 32 GT/s. When the operating data rate is &gt; 32 GT/s, the Rx Clock will use the Quadrature clock regardless of the setting of this bit.</td>
</tr>
<tr>
<td>7</td>
<td>$R W / R s v d P$</td>
<td>Force x32 Width Mode in x64 Module $\begin{array}{} \text { This bit is used only for } \\ \text { should be reset to } 0 . \end{array}$ test and debug purposes. In normal operation, this bit When set, this bit will force the x64 module to present "UCIe-A x32 bit =1" during the MBINIT.PARAM exchange phase independent of the value of bit 20, APMW, in the $T h i s \quad b i t \quad a p p l i e s \quad t o \quad a l l \quad m o d u l e s \quad i n \quad a \quad m u l t i - m o d u l e \quad l i n k .$ For x32 Advanced Package modules, this bit is reserved.</td>
</tr>
<tr>
<td>8</td>
<td>RW/RsvdP</td>
<td>Force x8 Width Mode in a UCIe-S x16 Module This bit is used only for test and debug purposes. In normal operation, this bit should be reset to 0. When set, this bit will force the x16 module to present "UCIe-S x8" bit =1 during the MBINIT.PARAM exchange phase independent of the value of bit 22, SPMW, in the UCIe Link Capability register. This feature can be used only when there is no lane reversal on the UCIe-S x16 link. This bit applies only to Module 0 in a multi-module link. When set in a multi-module link, it trains only Module 0. For a x8 Standard Package Module, this bit is reserved.</td>
</tr>
</table>

<table>
<caption>Table 9-48. Physical Layer Control Register (Sheet 2 of 2)</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>9</td>
<td>RW</td>
<td>$F o r c e \quad I / Q \quad C o r r e c t i o n \quad E n a b l e$ 0: Software override is disabled 1: Software override is enabled This bit is used only for compliance and debug purposes, and is provided to permit software to force I/Q correction during MBTRAIN.RXCLKCAL when the operating speed is &gt; 32 GT/s. When not in a compliance mode, software must trigger Link Retrain or Link Initialization for "Force I/Q Correction" to take effect. It is also permitted to use this bit in @PHY-Compliance mode. Note that this field only affects hardware behavior while the operating data rate is &gt; 32 GT/s. When the operating data rate is &lt;= 32 GT/s, I/Q correction is not supported.</td>
</tr>
<tr>
<td>$1 5 : 1 0$</td>
<td>RW</td>
<td>Force I/Q Correction Parameter Corresponds to bits [5:0] in the Message Info field of the {MBTRAIN.RXCLKCAL TCKN_L shift req} sideband message (see Table 7-9). If "Force I/Q Correction Enable" is set to 1, hardware only sends the value from "Force I/Q Correction Parameter" (this field) in the {MBTRAIN.RXCLKCAL TCKN_L shift req} sideband message. It is permitted to use this field in @PHY-Compliance mode. Note that this field only affects hardware behavior while the operating data rate is &gt; 32 GT/s. When the operating data rate is &lt;= 32 GT/s, I/Q correction is not supported.</td>
</tr>
<tr>
<td>16</td>
<td>RW</td>
<td>Force Tx EQ Preset 0: Software override is disabled 1: Software override is enabled This bit permits software to force an EQ preset value during MBTRAIN.RXDESKEW. When not in a compliance mode, software must trigger Link Retrain or Link Initialization for this bit to take effect. It is also permitted to use this bit in @PHY-Compliance mode. Note that this field only affects hardware behavior while the operating data rate is &gt; 32 GT/s. When the operating data rate is &lt;= 32 GT/s, the forcing of Tx EQ Preset is not supported.</td>
</tr>
<tr>
<td>$2 0 : 1 7$</td>
<td>RW</td>
<td>Force Tx EQ Preset Setting Corresponds to bits [4:0] in the Message Info field of the {MBTRAIN.RXDESKEW EQ Preset req} sideband message (see Table 7-9). If "Force TX EQ Preset" is set to 1, hardware only sends the value from "Force Tx EQ Preset Setting" (this field) in the {MBTRAIN.RXDESKEW EQ Preset req} sideband message. It is permitted to use this field in @PHY-Compliance mode. Note that this field only affects hardware behavior while the operating data rate is &gt; 32 GT/s. When the operating data rate is &lt;= 32 GT/s, the forcing of Tx EQ Preset is not supported.</td>
</tr>
<tr>
<td>21</td>
<td>$R W$</td>
<td>Tx Adjustment for Runtime Recalibration (TARR) 0: TARR is not enabled for negotiation 1: TARR is enabled for negotiation</td>
</tr>
<tr>
<td>31:22</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

## 9.5.3.24 PHY Status (Offset 1008h)

This register is global and not per module.

<table>
<caption>Table 9-49. Physical Layer Status Register</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>$2 : 0$</td>
<td>$R O$</td>
<td>Reserved</td>
</tr>
<tr>
<td>3</td>
<td>$R O$</td>
<td>Rx $0 : R \times \text { Termination disable }$ 1: Rx Termination enabled Default is same as 'Terminated Link' bit in PHY capability register. This is the current status of the local UCIe Module. Note that this is always 0 for Advanced Packages. For Standard packages, whether the Rx decides to terminate the Link could depend on several factors (including channel length in the Package, etc.), and that decision is implementation-specific. For Transmitter of a remote Link partner, it needs this information in order to know whether to Hi-Z the Data and Track Lanes during clock gating and when not performing Runtime Recalibration, respectively. It is expected that this information is known a priori at Package integration time, and the Transmitter is informed of this in an implementation- specific manner.</td>
</tr>
<tr>
<td>4</td>
<td>$R O$</td>
<td>Tx Eq Status 0: Eq Disabled 1: Eq Enabled Default is 0</td>
</tr>
<tr>
<td>5</td>
<td>$R O$</td>
<td>Clock Mode Status 0: Strobe Mode 1: Free running mode Default is 0. This is remote partner's advertised value during MBINIT.PARAM.</td>
</tr>
<tr>
<td>6</td>
<td>$R O$</td>
<td>Clock phase Status 0: Differential clock only (all data rates) 1: Quadrature clock (24/32 GT/s); Differential clock (16 GT/s and lower)</td>
</tr>
<tr>
<td>7</td>
<td>$R O$</td>
<td>$\begin{array}{} { \text { This is remote partner^{\prime } s \text { advertised value during Naing NANIT.PARAM. } } } \\ { \text { Lane Reversal within Module: Indicates if Lanes within a module areversed } } \end{array}$ 0: Lanes within module not reversed 1: Lanes within module are reversed</td>
</tr>
<tr>
<td>$1 3 : 8$</td>
<td>$R O$</td>
<td>I/Q Correction Parameter Default is 0. Contains the most-recently received values in bits [5:0] in the Message Info field of the {MBTRAIN.RXCLKCAL TCKN_L shift req} sideband message from the remote UCIe Module Partner. Note that this field is only updated by hardware while the operating data rate is &gt; 32 GT/s.</td>
</tr>
<tr>
<td>17:14</td>
<td>$R O$</td>
<td>EQ Preset Setting Default is 0. Contains the most-recently received value in bits [4:0] in the Message Info field of Module partner. {MBTRAIN.RXDESKEW EQ Preset req} sideband message from the remote UCIe Note that this field is only updated by hardware while the operating data rate is &gt; 32 GT/s.</td>
</tr>
<tr>
<td>18</td>
<td>RO</td>
<td>Tx Adjustment for Runtime Recalibration (TARR) 0: TARR is not supported 1: TARR was successfully negotiated and is operational</td>
</tr>
<tr>
<td>31:19</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

## 9.5.3.25 PHY Initialization and Debug (Offset 100Ch)

This register is global, and not per module.

<table>
<caption>Table 9-50. Phy Init and Debug Register</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td rowspan="3">2:0</td>
<td></td>
<td>Initialization control 000b: Initialize to Active. This is the regular Link bring up. $\begin{array}{} { \text { OO1b: Initialize to MBINIT } \left( \text { Debug mode\right) } \left( \text { i.e. pause training after } \right. \right. } \\ { \text { completing step-2 of MBINIT.PARAM\right). } } \end{array}$ 010b: Initialize to MBTRAIN (Debug/compliance mode) (i.e., pause training after entering MBTRAIN after completing step-1 of MBTRAIN.VALVREF). $\begin{array}{} { \text { O11b = Pause after completing step-1 of MBTRAIN.RXDESKEW } } \\ { \text { regardless of entering for intial bring up or from Retrain. } } \end{array}$ $\begin{array}{} { 1 0 0 b = \text { Pause after completing } \mathrm { s t e p - 1 } o f } \\ { \text { MBTRAIN.DATATRAINCENTERTERI } ; \text { regardiess of enterring for inttial } } \end{array}$</td>
</tr>
<tr>
<td rowspan="2">$R W$</td>
<td>$\begin{array}{} \text { bring up or trom Retrain. } \\ \text { All other encodings are reserved } . \end{array} .$</td>
</tr>
<tr>
<td>When training has paused, the corresponding state timeouts must be disabled, and hardware resumes training on any of the following triggers: · A Ob-to-1b transition on 'Resume Training' bit in this register · Sideband message for the corresponding state is received from remote link partner (e.g., if paused in MBINIT, receiving {MBINIT.CAL Done req} from remote link partner is also a trigger to move forward) A device that does not support the UCIe Test and Compliance register block is permitted to only implement encodings 000b through 010b. Default is 000b.</td>
</tr>
<tr>
<td>$4 : 3$</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
<tr>
<td>5</td>
<td>$R W$</td>
<td>$A \quad O b - t o - 1 b \quad t r a n s i t i o n \quad o n \quad t h i s \quad b i t \quad t r i g g e r s \quad h a r d w a r e \quad t o \quad r e s u m e$ Control' field in this register until ACTIVE. A device that does not support the UCIe Test and Compliance $\begin{array}{} { \text { register bloc } } \\ { \text { Default is 0b } } \end{array}$ is permitted to hardwire this bit to 0b.</td>
</tr>
<tr>
<td>$3 1 : 6$</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

## 9.5.3.26 Training Setup 1 (Offset 1010h)

This register is replicated per module. Offsets 1010h to 101Ch are used in 4B increments for multi-
module scenarios

<table>
<caption>Table 9-51. Training Setup 1 Register</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td rowspan="2">$2 : 0$</td>
<td rowspan="2">RW</td>
<td>Data pattern used during training 000b: Per-Lane LFSR pattern 001b: Per-Lane ID pattern 010b: If @PHY-Compliance {Per-Lane Clock pattern AA pattern} Else Reserved</td>
</tr>
<tr>
<td>011b: If @PHY-Compliance {Per-Lane all 0 pattern} Else Reserved 100b: If @PHY-Compliance {Per-Lane all 1 pattern} Else Reserved 101b: If {@PHY-Compliance Per-Lane inverted Clock pattern} Else Reserved All other encodings are reserved Default is 000b.</td>
</tr>
<tr>
<td>$5 : 3$</td>
<td>RW</td>
<td>Valid Pattern used during training 000b: Functional valid pattern (1111 0000 (lsb first)) All other encodings are reserved Default is 000b.</td>
</tr>
<tr>
<td>$9 : 6$</td>
<td>RW</td>
<td>Clock Phase control 0h: Clock PI center found by Transmitter 1h: Left edge found through Data to clock training 2h: Right edge found through Data to clock training $\begin{array}{} { \text { All other encodings are reservec } } \\ { \text { Default } = 0 } \end{array}$</td>
</tr>
<tr>
<td>10</td>
<td>RW</td>
<td>Training mode 0b: Continuous mode 1b: Burst Mode $D e f a u l t = 0$</td>
</tr>
<tr>
<td>$2 6 : 1 1$</td>
<td>$R W$</td>
<td>Count: Indicates the duration of selected pattern (UI count) $D e f a u l t = 4 h$</td>
</tr>
<tr>
<td>31:27</td>
<td>RsvdP</td>
<td>Reserved</td>
</tr>
</table>

## 9.5.3.27 Training Setup 2 (Offset 1020h)

This register is replicated per module. Offsets 1020h to 102Ch are used in 4B offset increments for
multi-module scenarios.

<table>
<caption>Table 9-52. Training Setup 2 Register</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>15:0</td>
<td>RW</td>
<td>Idle count: Indicates the duration of low following the burst (UI count) $D e f a u l t = 4 h$</td>
</tr>
<tr>
<td>$3 1 : 1 6$</td>
<td>$R W$</td>
<td>Iterations: Indicates the iteration count of bursts followed by idle (UI count) $D e f a u l t = 4 h$</td>
</tr>
</table>

## 9.5.3.28 Training Setup 3 (Offset 1030h)

This register is replicated per module. Offsets 1030h to 1048h are used in 8B offset increments for
multi-module scenarios.

<table>
<caption>Table 9-53. Training Setup 3 Register</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>63:0</td>
<td>RW</td>
<td>Lane mask: Indicated the Lanes to mask during Rx comparison. Example 1h = Lane 0 is masked during comparison. Default = 0 (no mask).</td>
</tr>
</table>

## 9.5.3.29 Training Setup 4 (Offset 1050h)

This register is replicated per module. Offsets 1050h to 105Ch are used in 4B offset increments for
multi-module scenarios.

<table>
<caption>Table 9-54. Training Setup 4 Register</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>$3 : 0$</td>
<td>$R W$</td>
<td>Repair Lane mask: Indicated the Redundant Lanes to mask during Rx comparison. Example 1h =RDO is masked during comparison 2h: RD1 mask. Default = 0 (no mask).</td>
</tr>
<tr>
<td>$1 5 : 4$</td>
<td>RW</td>
<td>Max error Threshold in per Lane comparison: Indicates threshold for error counting to start. values are sent in the corresponding $S t a r t \quad T x \quad I n i t \quad D \quad t o \quad C \quad p o i n t$ test req} and {Start Tx Init D to C eye sweep req} sideband messages. The remote Link partner must use these values for checking errors against the threshold. For Rx-initiated tests, these values are sent in the corresponding {Start Rx Init D to C point test req} and {Start Rx Init D to C eye sweep req} sideband messages as an inform. The receiver uses against the threshold. $D e f a u l t = 0 \left( a l l \quad e r r o r s \quad a r e \quad c o u n t e d \right) .$</td>
</tr>
<tr>
<td>$3 1 : 1 6$</td>
<td>RW</td>
<td>Max error Threshold in aggregate comparison: Indicates threshold for error counting to start. For Tx-initiated tests, these values are sent in the corresponding {Start Tx Init D to C point test req} and {Start Tx Init D to $\mathrm { C } \mathrm { e y e }$ sweep req} sideband messages. The remote Link partner must use these values for checking errors against the threshold. $\begin{array}{} { \text { For } R x \text { -initiated tests, these values ares are sent in the corresponalng } } \\ { \left. \text { fstart } R x \text { Init } D \text { to C point test req } \right\} \text { and } \left\{ \text { Start } R x \text { Init } D \text { to to eyt } \right. } \end{array}$ sweep req} sideband messages as an inform. The receiver uses these values for checking errors against the threshold. Default = 0 (all errors are counted).</td>
</tr>
</table>

## 9.5.3.30 Current Lane Map Module 0 (Offset 1060h)

<table>
<caption>Table 9-55. Current Lane Map Module 0 Register</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>$6 3 : 0$</td>
<td>RW</td>
<td>Current Rx Lane map (CLM) for Module-0: If a bit is 1 it indicates the corresponding physical Lane is operational. For Standard package modules, bits 63:16 of this register are not applicable. For UCIe-A x32 implementations (i.e., APMW bit in UCIe Link Capability register is set), bits 63:32 of this register are not applicable. Default Value is all 0s.</td>
</tr>
</table>

## 9.5.3.31 Current Lane Map Module 1 (Offset 1068h)

<table>
<caption>Table 9-56. Current Lane Map Module 1 Register</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>$6 3 : 0$</td>
<td>RW</td>
<td>Current Rx Lane map (CLM) for Module-1: If a bit is 1 it indicates the corresponding physical Lane is operational. For Standard package modules, bits 63:16 of this register are not applicable. For UCIe-A x32 implementations (i.e., APMW bit in UCIe Link Capability register is set), bits 63:32 of this register are not applicable. Default Value is all Os. This register is reserved if Module 1 is not present</td>
</tr>
</table>

## 9.5.3.32 Current Lane Map Module 2 (Offset 1070h)

<table>
<caption>Table 9-57. Current Lane Map Module 2 Register</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>$6 3 : 0$</td>
<td>RW/RsvdP</td>
<td>Current Rx Lane map (CLM) for Module-2: If a bit is 1 it indicates the corresponding physical Lane is operational. For Standard package modules, bits 63:16 of this register are not applicable. For UCIe-A x32 implementations (i.e., APMW bit in UCIe Link Capability register is set), bits 63:32 of this register are not applicable. Default Value is all 0s. This register is reserved if Module 2 is not present</td>
</tr>
</table>

## 9.5.3.33 Current Lane Map Module 3 (Offset 1078h)

<table>
<caption>Table 9-58. Current Lane Map Module 3 Register</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td>63:0</td>
<td>RW/RsvdP</td>
<td>Current Rx Lane map (CLM) for Module-3: If a bit is 1 it indicates the corresponding physical Lane is operational. For Standard package modules, bits 63:16 of this register are not applicable. For UCIe-A x32 implementations (i.e., APMW bit in UCIe Link Capability register is set), bits 63:32 of this register are not applicable. Default Value is all 0s. This register is reserved if Module 3 is not present</td>
</tr>
</table>

## 9.5.3.34 Error Log 0 (Offset 1080h)

This register is replicated per module. Offsets 1080h to 108Ch are used in 4B offset increments for
multi-module scenarios.

<table>
<caption>Table 9-59. Error Log 0 Register</caption>
<tr>
<th>Bit</th>
<th>Attribute</th>
<th>Description</th>
</tr>
<tr>
<td rowspan="2">7:0</td>
<td rowspan="2">ROS</td>
<td>State N: Captures the current Link training state machine status. State Encodings are given by:</td>
</tr>
<tr>
<td>00h RESET 0Eh MBTRAIN.VALTRAINVREF 01h SBINIT 0Fh MBTRAIN.DATATRAINCENTER1 02h MBINIT.PARAM 10h MBTRAIN.DATATRAINVREF 11h MBTRAIN.RXDESKEW $\begin{array}{} { \text { O3h MBINIT.CAL } } \\ { \text { O4h MBINIT.REPAIRCLK } } \end{array}$ 12h MBTRAIN.DATATRAINCENTER2 05h MBINIT.REPAIRVAL 13h MBTRAIN.LINKSPEED 06h MBINIT.REVERSALMB 14h MBTRAIN.REPAIR 07h MBINIT.REPAIRMB 15h PHYRETRAIN 08h MBTRAIN.VALVREF 16h LINKINIT $1 7 h \quad A C T I V E$ $\begin{array}{} \text { O9h MBTRAIN.DATAVREF } \\ \text { OAh MBTRAIN.SPEEDIDL } \end{array}$ 18h TRAINERROR $\begin{array}{} { \text { OBh MBTRAIN.TXSELFCAL } } \\ { \text { OCh MBTRAIN.RXSELFCAL } } \end{array}$ $\begin{array}{} { \text { 19n L1/L2 } } \\ { \text { All other encodings are reservec } } \end{array}$ 0Dh MBTRAIN.VALTRAINCENTER Default is 0</td>
</tr>
<tr>
<td>8</td>
<td>ROS</td>
<td>Lane Reversal: 1b indicates Lane Reversal within the module. Default is 0</td>
</tr>
<tr>
<td>9</td>
<td>ROS</td>
<td>Width Degrade: 1b indicates Module width Degrade. Applicable to Standard package only. Default is 0.</td>
</tr>
<tr>
<td>$1 5 : 1 0$</td>
<td>$R s v d Z$</td>
<td>Reserved</td>
</tr>
<tr>
<td>$2 3 : 1 6$</td>
<td>ROS</td>
<td>State (N-1): Captures the state before State N was entered for Link training state machine. State encodings are the same as State N field. Default is 0</td>
</tr>
<tr>
<td>$3 1 : 2 4$</td>
<td>$R O S$</td>
<td>State (N-2): Captures the state before State (N-1) was entered for Link training state machine. State encodings are the same as State N field. Default is 0</td>
</tr>
</table>

