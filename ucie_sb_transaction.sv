// UCIe Sideband Transaction Class - Refactored with extern methods
// Contains all packet fields and methods for sideband protocol transactions

//=============================================================================
// CLASS: sideband_transaction
//
// DESCRIPTION:
//   UCIe sideband transaction item containing all packet fields and methods
//   for creating, manipulating, and validating sideband protocol transactions.
//   Supports all 19 UCIe opcodes with proper parity calculation and field
//   validation according to UCIe specification.
//
// FEATURES:
//   - Complete UCIe sideband packet format support
//   - Automatic parity calculation (CP and DP)
//   - Address alignment validation
//   - Byte enable validation for 32-bit operations
//   - Support for all packet types (Register Access, Completion, Message)
//   - UCIe Table 7-4 compliant srcid/dstid constraints
//
// AUTHOR: UCIe Sideband UVM Agent
// VERSION: 1.0
//=============================================================================

class ucie_sb_transaction extends uvm_sequence_item;
  
  //=============================================================================
  // CLASS FIELDS
  //=============================================================================
  
  // Header fields
  rand ucie_sb_opcode_e opcode;
  rand bit [2:0]         srcid;
  rand bit [2:0]         dstid;
  rand bit [4:0]         tag;
  rand bit [7:0]         be;        // Byte enables
  rand bit               ep;        // Error poison
  rand bit               cr;        // Credit return
  rand bit [23:0]        addr;      // Address (for register access)
  rand bit [15:0]        status;    // Status (for completions)
  
  // Message-specific fields (for messages without data)
  rand bit [7:0]         msgcode;   // Message Code (for messages)
  rand bit [15:0]        msginfo;   // Message Info (for messages)
  rand bit [7:0]         msgsubcode; // Message Subcode (for messages)
  
  // Data payload
  rand bit [63:0]        data;
  
  // Control bits
  bit                    cp;        // Control parity
  bit                    dp;        // Data parity
  
  // Derived information
  packet_type_e          pkt_type;
  bit                    has_data;
  bit                    is_64bit;
  bit                    is_clock_pattern; // Special clock pattern transaction
  
  //=============================================================================
  // UVM FACTORY REGISTRATION
  //=============================================================================
  
  `uvm_object_utils_begin(ucie_sb_transaction)
    `uvm_field_enum(ucie_sb_opcode_e, opcode, UVM_ALL_ON)
    `uvm_field_int(srcid, UVM_ALL_ON)
    `uvm_field_int(dstid, UVM_ALL_ON)
    `uvm_field_int(tag, UVM_ALL_ON)
    `uvm_field_int(be, UVM_ALL_ON)
    `uvm_field_int(ep, UVM_ALL_ON)
    `uvm_field_int(cr, UVM_ALL_ON)
    `uvm_field_int(addr, UVM_ALL_ON)
    `uvm_field_int(status, UVM_ALL_ON)
    `uvm_field_int(msgcode, UVM_ALL_ON)
    `uvm_field_int(msginfo, UVM_ALL_ON)
    `uvm_field_int(msgsubcode, UVM_ALL_ON)
    `uvm_field_int(data, UVM_ALL_ON)
    `uvm_field_int(cp, UVM_ALL_ON)
    `uvm_field_int(dp, UVM_ALL_ON)
    `uvm_field_enum(packet_type_e, pkt_type, UVM_ALL_ON)
    `uvm_field_int(has_data, UVM_ALL_ON)
    `uvm_field_int(is_64bit, UVM_ALL_ON)
    `uvm_field_int(is_clock_pattern, UVM_ALL_ON)
  `uvm_object_utils_end

  //=============================================================================
  // CONSTRUCTOR
  //=============================================================================

  //-----------------------------------------------------------------------------
  // FUNCTION: new
  // Creates a new sideband transaction object
  //
  // PARAMETERS:
  //   name - Object name for UVM hierarchy
  //-----------------------------------------------------------------------------
  function new(string name = "ucie_sb_transaction");
    super.new(name);
  endfunction

  //=============================================================================
  // EXTERN FUNCTION DECLARATIONS
  //=============================================================================
  
  //-----------------------------------------------------------------------------
  // FUNCTION: post_randomize
  // Called automatically after randomization to update derived fields
  // Updates packet info and calculates parity bits
  //-----------------------------------------------------------------------------
  extern function void post_randomize();
  
  //-----------------------------------------------------------------------------
  // FUNCTION: update_packet_info
  // Updates derived packet information based on opcode
  // Sets pkt_type, has_data, and is_64bit fields
  //-----------------------------------------------------------------------------
  extern function void update_packet_info();
  
  //-----------------------------------------------------------------------------
  // FUNCTION: calculate_parity
  // Calculates control parity (CP) and data parity (DP) per UCIe specification
  // CP = XOR of all control fields, DP = XOR of data if present
  //-----------------------------------------------------------------------------
  extern function void calculate_parity();
  
  //-----------------------------------------------------------------------------
  // FUNCTION: get_header
  // Packs transaction fields into 64-bit header packet format
  // 
  // RETURNS: 64-bit header packet ready for transmission
  //-----------------------------------------------------------------------------
  extern function bit [63:0] get_header();
  
  //-----------------------------------------------------------------------------
  // FUNCTION: get_message_header
  // Packs message fields into 64-bit header packet for messages without data
  // 
  // RETURNS: 64-bit message header packet ready for transmission
  //-----------------------------------------------------------------------------
  extern function bit [63:0] get_message_header();
  
  //-----------------------------------------------------------------------------
  // FUNCTION: get_clock_pattern_header
  // Returns the special clock pattern header (Phase0=0x55555555, Phase1=0x55555555)
  // 
  // RETURNS: 64-bit clock pattern packet
  //-----------------------------------------------------------------------------
  extern function bit [63:0] get_clock_pattern_header();
  
  //-----------------------------------------------------------------------------
  // FUNCTION: is_valid_clock_pattern
  // Validates that this is a proper clock pattern transaction (no data payload)
  // 
  // RETURNS: 1 if valid clock pattern, 0 otherwise
  //-----------------------------------------------------------------------------
  extern function bit is_valid_clock_pattern();
  
  //-----------------------------------------------------------------------------
  // FUNCTION: get_register_access_header
  // Packs register access/completion fields into 64-bit header packet
  // 
  // RETURNS: 64-bit register access header packet ready for transmission
  //-----------------------------------------------------------------------------
  extern function bit [63:0] get_register_access_header();
  
  //-----------------------------------------------------------------------------
  // FUNCTION: get_srcid_name
  // Returns human-readable name for source ID
  //
  // RETURNS: String representation of srcid (e.g., "D2D_ADAPTER")
  //-----------------------------------------------------------------------------
  extern function string get_srcid_name();
  
  //-----------------------------------------------------------------------------
  // FUNCTION: get_dstid_name
  // Returns human-readable name for destination ID
  //
  // RETURNS: String representation of dstid (e.g., "LOCAL_DIE")
  //-----------------------------------------------------------------------------
  extern function string get_dstid_name();
  
  //-----------------------------------------------------------------------------
  // FUNCTION: is_remote_die_packet
  // Checks if packet is destined for remote die
  //
  // RETURNS: 1 if remote die packet, 0 if local die
  //-----------------------------------------------------------------------------
  extern function bit is_remote_die_packet();
  
  //-----------------------------------------------------------------------------
  // FUNCTION: is_poison_set
  // Checks if error poison bit is set
  //
  // RETURNS: 1 if poison bit set, 0 otherwise
  //-----------------------------------------------------------------------------
  extern function bit is_poison_set();
  
  //-----------------------------------------------------------------------------
  // FUNCTION: has_credit_return
  // Checks if credit return bit is set
  //
  // RETURNS: 1 if credit return set, 0 otherwise
  //-----------------------------------------------------------------------------
  extern function bit has_credit_return();
  
  //-----------------------------------------------------------------------------
  // FUNCTION: convert2string
  // Converts transaction to formatted string for debugging/logging
  //
  // RETURNS: Multi-line formatted string with all transaction details
  //-----------------------------------------------------------------------------
  extern function string convert2string();

  //=============================================================================
  // CONSTRAINTS (Keep inline for readability)
  //=============================================================================

  // UCIe specification compliant constraints
  constraint srcid_c { 
    srcid inside {
      3'b001,  // D2D Adapter
      3'b010,  // Physical Layer  
      3'b011   // Management Port Gateway
    };
  }
  
  constraint dstid_c {
    if (pkt_type == PKT_REG_ACCESS) {
      if (is_remote_die_packet()) {
        dstid inside {3'b000, 3'b001, 3'b010, 3'b011};
      } else {
        dstid == 3'b000;
      }
    }
    if (pkt_type == PKT_COMPLETION) {
      dstid == srcid;  // Completions return to requester
    }
  }
  
  // Address alignment constraints
  constraint addr_alignment_c {
    if (is_64bit) {
      addr[2:0] == 3'b000;  // 64-bit aligned
    } else {
      addr[1:0] == 2'b00;   // 32-bit aligned
    }
  }
  
  // Byte enable constraints
  constraint be_c {
    if (!is_64bit) {
      be[7:4] == 4'b0000;   // Upper BE reserved for 32-bit
    }
  }
  
  // Message constraints for messages without data
  constraint message_c {
    if (pkt_type == PKT_MESSAGE && !has_data && !is_clock_pattern) {
      msgcode inside {MSG_SBINIT_OUT_OF_RESET, MSG_SBINIT_DONE_REQ, MSG_SBINIT_DONE_RESP};
      
      // Constrain msgsubcode based on msgcode
      if (msgcode == MSG_SBINIT_OUT_OF_RESET) {
        msgsubcode == SUBCODE_SBINIT_OUT_OF_RESET;
      }
      if (msgcode == MSG_SBINIT_DONE_REQ) {
        msgsubcode == SUBCODE_SBINIT_DONE_REQ;
      }
      if (msgcode == MSG_SBINIT_DONE_RESP) {
        msgsubcode == SUBCODE_SBINIT_DONE_RESP;
      }
      
      // MsgInfo constraints based on message type
      if (msgcode == MSG_SBINIT_OUT_OF_RESET) {
        msginfo[15:4] == 12'h000;  // Reserved bits
        msginfo[3:0] inside {4'h0, 4'h1, 4'h2, 4'h3, 4'h4, 4'h5, 4'h6, 4'h7, 4'h8, 4'h9, 4'hA, 4'hB, 4'hC, 4'hD, 4'hE, 4'hF}; // Result field
      } else {
        msginfo == 16'h0000;  // Other messages have 0000h
      }
    }
  }
  
  // Clock pattern constraints
  constraint clock_pattern_c {
    if (is_clock_pattern) {
      opcode == CLOCK_PATTERN;
    }
    if (opcode == CLOCK_PATTERN) {
      is_clock_pattern == 1;
    }
  }

endclass : ucie_sb_transaction

//=============================================================================
// IMPLEMENTATION SECTION
//=============================================================================

//-----------------------------------------------------------------------------
// FUNCTION: post_randomize
// Called automatically after randomization to update derived fields
//-----------------------------------------------------------------------------
function void ucie_sb_transaction::post_randomize();
  update_packet_info();
  calculate_parity();
  `uvm_info("TRANSACTION", {"Post-randomize: ", convert2string()}, UVM_HIGH)
endfunction

//-----------------------------------------------------------------------------
// FUNCTION: update_packet_info
// Updates derived packet information based on opcode
//-----------------------------------------------------------------------------
function void ucie_sb_transaction::update_packet_info();
  // Determine packet type and data characteristics based on opcode
  case (opcode)
    // 32-bit Register Access Operations
    MEM_READ_32B, DMS_READ_32B, CFG_READ_32B: begin
      pkt_type = PKT_REG_ACCESS;
      has_data = 0;
      is_64bit = 0;
      is_clock_pattern = 0;
    end
    
    MEM_WRITE_32B, DMS_WRITE_32B, CFG_WRITE_32B: begin
      pkt_type = PKT_REG_ACCESS;
      has_data = 1;
      is_64bit = 0;
      is_clock_pattern = 0;
    end
    
    // 64-bit Register Access Operations
    MEM_READ_64B, DMS_READ_64B, CFG_READ_64B: begin
      pkt_type = PKT_REG_ACCESS;
      has_data = 0;
      is_64bit = 1;
      is_clock_pattern = 0;
    end
    
    MEM_WRITE_64B, DMS_WRITE_64B, CFG_WRITE_64B: begin
      pkt_type = PKT_REG_ACCESS;
      has_data = 1;
      is_64bit = 1;
      is_clock_pattern = 0;
    end
    
    // Completion Operations
    COMPLETION_NO_DATA: begin
      pkt_type = PKT_COMPLETION;
      has_data = 0;
      is_64bit = 0;
      is_clock_pattern = 0;
    end
    
    COMPLETION_32B: begin
      pkt_type = PKT_COMPLETION;
      has_data = 1;
      is_64bit = 0;
      is_clock_pattern = 0;
    end
    
    COMPLETION_64B: begin
      pkt_type = PKT_COMPLETION;
      has_data = 1;
      is_64bit = 1;
      is_clock_pattern = 0;
    end
    
    // Message Operations
    MESSAGE_NO_DATA, MGMT_MSG_NO_DATA: begin
      pkt_type = PKT_MESSAGE;
      has_data = 0;
      is_64bit = 0;
      is_clock_pattern = 0;
    end
    
    MESSAGE_64B, MGMT_MSG_DATA: begin
      pkt_type = PKT_MESSAGE;
      has_data = 1;
      is_64bit = 1;
      is_clock_pattern = 0;
    end
    
    // Clock Pattern Operation
    CLOCK_PATTERN: begin
      pkt_type = PKT_CLOCK_PATTERN;
      has_data = 0;        // Clock pattern has NO data payload
      is_64bit = 0;        // Clock pattern header only
      is_clock_pattern = 1;
    end
    
    default: begin
      `uvm_error("TRANSACTION", $sformatf("Unknown opcode: %s", opcode.name()))
      pkt_type = PKT_REG_ACCESS;
      has_data = 0;
      is_64bit = 0;
      is_clock_pattern = 0;
    end
  endcase
  
  // Clock pattern has no data payload - it's just the header pattern
  
  `uvm_info("TRANSACTION", $sformatf("Updated packet info: type=%s, has_data=%0b, is_64bit=%0b", 
            pkt_type.name(), has_data, is_64bit), UVM_DEBUG)
endfunction

//-----------------------------------------------------------------------------
// FUNCTION: calculate_parity
// Calculates control parity (CP) and data parity (DP) per UCIe specification
//-----------------------------------------------------------------------------
function void ucie_sb_transaction::calculate_parity();
  // Control parity (CP) - XOR of all control fields based on packet type
  if (is_clock_pattern) begin
    // Clock pattern has fixed parity
    cp = 1'b0;
    dp = 1'b0;
  end else if (pkt_type == PKT_MESSAGE && !has_data) begin
    // Message without data parity calculation
    cp = ^{opcode, srcid, dstid, msgcode, msginfo, msgsubcode};
  end else if (pkt_type == PKT_COMPLETION) begin
    // Completion parity calculation (Figure 7-2)
    cp = ^{opcode, srcid, dstid, tag, be, ep, cr, status[2:0]};
  end else begin
    // Register access request parity calculation (Figure 7-1)
    cp = ^{opcode, srcid, dstid, tag, be, ep, cr, addr[23:0]};
  end
  
  // Data parity (DP) - XOR of data if present
  if (has_data) begin
    dp = is_64bit ? ^data : ^data[31:0];
  end else begin
    dp = 1'b0;
  end
  
  `uvm_info("TRANSACTION", $sformatf("Calculated parity: CP=%0b, DP=%0b", cp, dp), UVM_DEBUG)
endfunction

//-----------------------------------------------------------------------------
// FUNCTION: get_header
// Packs transaction fields into 64-bit header packet format
//-----------------------------------------------------------------------------
function bit [63:0] ucie_sb_transaction::get_header();
  // Route to appropriate header generation based on packet type
  if (is_clock_pattern) begin
    return get_clock_pattern_header();
  end else if (pkt_type == PKT_MESSAGE && !has_data) begin
    return get_message_header();
  end else begin
    // Standard register access and completion header format
    return get_register_access_header();
  end
endfunction

//-----------------------------------------------------------------------------
// FUNCTION: get_srcid_name
// Returns human-readable name for source ID
//-----------------------------------------------------------------------------
function string ucie_sb_transaction::get_srcid_name();
  case (srcid)
    3'b001: return "D2D_ADAPTER";
    3'b010: return "PHYSICAL_LAYER";
    3'b011: return "MGMT_PORT_GATEWAY";
    default: return $sformatf("UNKNOWN_SRCID_%0b", srcid);
  endcase
endfunction

//-----------------------------------------------------------------------------
// FUNCTION: get_dstid_name
// Returns human-readable name for destination ID
//-----------------------------------------------------------------------------
function string ucie_sb_transaction::get_dstid_name();
  case (dstid)
    3'b000: return "LOCAL_DIE";
    3'b001: return "REMOTE_DIE_1";
    3'b010: return "REMOTE_DIE_2"; 
    3'b011: return "REMOTE_DIE_3";
    default: return $sformatf("UNKNOWN_DSTID_%0b", dstid);
  endcase
endfunction

//-----------------------------------------------------------------------------
// FUNCTION: is_remote_die_packet
// Checks if packet is destined for remote die
//-----------------------------------------------------------------------------
function bit ucie_sb_transaction::is_remote_die_packet();
  return (dstid != 3'b000);
endfunction

//-----------------------------------------------------------------------------
// FUNCTION: is_poison_set
// Checks if error poison bit is set
//-----------------------------------------------------------------------------
function bit ucie_sb_transaction::is_poison_set();
  return ep;
endfunction

//-----------------------------------------------------------------------------
// FUNCTION: has_credit_return
// Checks if credit return bit is set
//-----------------------------------------------------------------------------
function bit ucie_sb_transaction::has_credit_return();
  return cr;
endfunction

//-----------------------------------------------------------------------------
// FUNCTION: convert2string
// Converts transaction to formatted string for debugging/logging
//-----------------------------------------------------------------------------
function string ucie_sb_transaction::convert2string();
  string s;
  s = $sformatf("\n=== UCIe Sideband Transaction ===");
  s = {s, $sformatf("\n  Opcode    : %s (0x%02h)", opcode.name(), opcode)};
  s = {s, $sformatf("\n  Type      : %s", pkt_type.name())};
  s = {s, $sformatf("\n  Source    : %s (0x%01h)", get_srcid_name(), srcid)};
  s = {s, $sformatf("\n  Dest      : %s (0x%01h)", get_dstid_name(), dstid)};
  s = {s, $sformatf("\n  Tag       : 0x%02h", tag)};
  s = {s, $sformatf("\n  Address   : 0x%06h", addr)};
  s = {s, $sformatf("\n  BE        : 0x%02h", be)};
  s = {s, $sformatf("\n  EP        : %0b", ep)};
  s = {s, $sformatf("\n  CR        : %0b", cr)};
  s = {s, $sformatf("\n  CP        : %0b", cp)};
  s = {s, $sformatf("\n  DP        : %0b", dp)};
  if (has_data) begin
    s = {s, $sformatf("\n  Data      : 0x%016h (%s)", data, is_64bit ? "64-bit" : "32-bit")};
  end else begin
    s = {s, $sformatf("\n  Data      : No data")};
  end
  s = {s, $sformatf("\n  Has Data  : %0b", has_data)};
  s = {s, $sformatf("\n  Is 64-bit : %0b", is_64bit)};
  s = {s, $sformatf("\n  Clock Pattern: %0b", is_clock_pattern)};
  if (pkt_type == PKT_MESSAGE && !has_data) begin
    s = {s, $sformatf("\n  MsgCode   : 0x%02h", msgcode)};
    s = {s, $sformatf("\n  MsgInfo   : 0x%04h", msginfo)};
    s = {s, $sformatf("\n  MsgSubcode: 0x%02h", msgsubcode)};
  end
  s = {s, $sformatf("\n================================")};
  return s;
endfunction

//-----------------------------------------------------------------------------
// FUNCTION: get_message_header
// Packs message fields into 64-bit header packet for messages without data
//-----------------------------------------------------------------------------
function bit [63:0] ucie_sb_transaction::get_message_header();
  bit [31:0] phase0, phase1;
  
  // Phase 0 (Bits 31 to 0) - Figure 7-3 format for Messages without Data
  // phase0[31:29] srcid + phase0[28:27] rsvd + phase0[26:22] rsvd + 
  // phase0[21:14] msgcode[7:0] + phase0[13:5] rsvd + phase0[4:0] opcode[4:0]
  phase0 = {srcid,           // [31:29]
            2'b00,           // [28:27] reserved
            5'b00000,        // [26:22] reserved 
            msgcode,         // [21:14] msgcode[7:0]
            9'b000000000,    // [13:5] reserved
            opcode};         // [4:0] opcode[4:0]
  
  // Phase 1 (Bits 31 to 0) - Figure 7-3 format for Messages without Data  
  // phase1[31] dp + phase1[30] cp + phase1[29:27] rsvd + phase1[26:24] dstid +
  // phase1[23:8] MsgInfo[15:0] + phase1[7:0] MsgSubcode[7:0]
  phase1 = {dp,              // [31] dp
            cp,              // [30] cp
            3'b000,          // [29:27] reserved
            dstid,           // [26:24] dstid
            msginfo,         // [23:8] MsgInfo[15:0]
            msgsubcode};     // [7:0] MsgSubcode[7:0]
  
  `uvm_info("TRANSACTION", $sformatf("Generated message header: phase0=0x%08h, phase1=0x%08h", phase0, phase1), UVM_DEBUG)
  
  return {phase1, phase0};
endfunction

//-----------------------------------------------------------------------------
// FUNCTION: get_clock_pattern_header
// Returns the header for clock pattern transaction (data payload contains the pattern)
//-----------------------------------------------------------------------------
function bit [63:0] ucie_sb_transaction::get_clock_pattern_header();
  bit [31:0] phase0, phase1;
  
  // Clock pattern: the header itself IS the pattern
  // Phase0 = 32'h5555_5555 (alternating 1010... pattern)
  // Phase1 = 32'h5555_5555 (alternating 1010... pattern)
  phase0 = CLOCK_PATTERN_PHASE0;  // 32'h5555_5555
  phase1 = CLOCK_PATTERN_PHASE1;  // 32'h5555_5555
  
  `uvm_info("TRANSACTION", $sformatf("Generated clock pattern header: phase0=0x%08h, phase1=0x%08h", phase0, phase1), UVM_DEBUG)
  
  return {phase1, phase0};
endfunction

//-----------------------------------------------------------------------------
// FUNCTION: is_valid_clock_pattern
// Validates that this is a proper clock pattern transaction (no data payload)
//-----------------------------------------------------------------------------
function bit ucie_sb_transaction::is_valid_clock_pattern();
  bit [63:0] expected_header;
  
  if (!is_clock_pattern) begin
    return 0; // Not a clock pattern transaction
  end
  
  // For clock pattern, we validate the header pattern, not data (since there's no data)
  expected_header = {CLOCK_PATTERN_PHASE1, CLOCK_PATTERN_PHASE0};
  
  // Clock pattern is valid if opcode is CLOCK_PATTERN and has no data
  if (opcode == CLOCK_PATTERN && !has_data) begin
    `uvm_info("TRANSACTION", "Clock pattern validation PASSED: correct opcode and no data", UVM_DEBUG)
    return 1;
  end else begin
    `uvm_error("TRANSACTION", $sformatf("Clock pattern validation FAILED: opcode=%s, has_data=%0b", 
               opcode.name(), has_data))
    return 0;
  end
endfunction

//-----------------------------------------------------------------------------
// FUNCTION: get_register_access_header
// Packs register access/completion fields into 64-bit header packet per Figure 7-1/7-2
//-----------------------------------------------------------------------------
function bit [63:0] ucie_sb_transaction::get_register_access_header();
  bit [31:0] phase0, phase1;
  
  if (pkt_type == PKT_COMPLETION) begin
    // Figure 7-2: Format for Register Access Completions
    // Phase 0: phase0[31:29] srcid + phase0[28:27] rsvd + phase0[26:22] tag[4:0] +
    // phase0[21:14] be[7:0] + phase0[13:6] rsvd + phase0[5] ep + phase0[4:0] opcode[4:0]
    phase0 = {srcid,           // [31:29] srcid
              2'b00,           // [28:27] reserved
              tag,             // [26:22] tag[4:0]
              be,              // [21:14] be[7:0]
              8'b00000000,     // [13:6] reserved
              ep,              // [5] ep
              opcode};         // [4:0] opcode[4:0]
    
    // Phase 1: phase1[31] dp + phase1[30] cp + phase1[29] cr + phase1[28:27] rsvd +
    // phase1[26:24] dstid + phase1[23:3] rsvd + phase1[2:0] Status
    phase1 = {dp,              // [31] dp
              cp,              // [30] cp
              cr,              // [29] cr
              2'b00,           // [28:27] reserved
              dstid,           // [26:24] dstid
              21'b000000000000000000000, // [23:3] reserved
              status[2:0]};    // [2:0] Status
              
    `uvm_info("TRANSACTION", $sformatf("Generated completion header: phase0=0x%08h, phase1=0x%08h", phase0, phase1), UVM_DEBUG)
  end else begin
    // Figure 7-1: Format for Register Access Request
    // Phase 0: phase0[31:29] srcid + phase0[28:27] rsvd + phase0[26:22] tag[4:0] +
    // phase0[21:14] be[7:0] + phase0[13:6] rsvd + phase0[5] ep + phase0[4:0] opcode[4:0]
    phase0 = {srcid,           // [31:29] srcid
              2'b00,           // [28:27] reserved
              tag,             // [26:22] tag[4:0]
              be,              // [21:14] be[7:0]
              8'b00000000,     // [13:6] reserved
              ep,              // [5] ep
              opcode};         // [4:0] opcode[4:0]
    
    // Phase 1: phase1[31] dp + phase1[30] cp + phase1[29] cr + phase1[28:27] rsvd +
    // phase1[26:24] dstid + phase1[23:0] addr[23:0]
    phase1 = {dp,              // [31] dp
              cp,              // [30] cp
              cr,              // [29] cr
              2'b00,           // [28:27] reserved
              dstid,           // [26:24] dstid
              addr[23:0]};     // [23:0] addr[23:0]
              
    `uvm_info("TRANSACTION", $sformatf("Generated register access header: phase0=0x%08h, phase1=0x%08h", phase0, phase1), UVM_DEBUG)
  end
  
  return {phase1, phase0};
endfunction