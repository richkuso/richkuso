// UCIe Sideband Transaction Class - Refactored with extern methods
// This example shows improved code organization using extern declarations

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
  rand bit [63:0]        data;      // Data payload
  
  // Control bits
  bit                    cp;        // Control parity
  bit                    dp;        // Data parity
  
  // Derived information
  packet_type_e          pkt_type;
  bit                    has_data;
  bit                    is_64bit;
  
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
    `uvm_field_int(data, UVM_ALL_ON)
    `uvm_field_int(cp, UVM_ALL_ON)
    `uvm_field_int(dp, UVM_ALL_ON)
    `uvm_field_enum(packet_type_e, pkt_type, UVM_ALL_ON)
    `uvm_field_int(has_data, UVM_ALL_ON)
    `uvm_field_int(is_64bit, UVM_ALL_ON)
  `uvm_object_utils_end

  //=============================================================================
  // CONSTRUCTOR
  //=============================================================================
  
  function new(string name = "ucie_sb_transaction");
    super.new(name);
  endfunction

  //=============================================================================
  // EXTERN FUNCTION/TASK DECLARATIONS
  //=============================================================================
  
  // Core transaction methods
  extern function void post_randomize();
  extern function void update_packet_info();
  extern function void calculate_parity();
  
  // Packet generation methods
  extern function bit [63:0] get_header();
  
  // Helper/utility methods
  extern function string get_srcid_name();
  extern function string get_dstid_name();
  extern function bit is_remote_die_packet();
  extern function bit is_poison_set();
  extern function bit has_credit_return();
  
  // Debug/display methods
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

endclass : ucie_sb_transaction

//=============================================================================
// IMPLEMENTATION SECTION
//=============================================================================

// Core transaction methods
function void ucie_sb_transaction::post_randomize();
  update_packet_info();
  calculate_parity();
  `uvm_info("TRANSACTION", {"Post-randomize: ", convert2string()}, UVM_HIGH)
endfunction

function void ucie_sb_transaction::update_packet_info();
  // Determine packet type and data characteristics based on opcode
  case (opcode)
    // 32-bit Register Access Operations
    MEM_READ_32B, DMS_READ_32B, CFG_READ_32B: begin
      pkt_type = PKT_REG_ACCESS;
      has_data = 0;
      is_64bit = 0;
    end
    
    MEM_WRITE_32B, DMS_WRITE_32B, CFG_WRITE_32B: begin
      pkt_type = PKT_REG_ACCESS;
      has_data = 1;
      is_64bit = 0;
    end
    
    // 64-bit Register Access Operations
    MEM_READ_64B, DMS_READ_64B, CFG_READ_64B: begin
      pkt_type = PKT_REG_ACCESS;
      has_data = 0;
      is_64bit = 1;
    end
    
    MEM_WRITE_64B, DMS_WRITE_64B, CFG_WRITE_64B: begin
      pkt_type = PKT_REG_ACCESS;
      has_data = 1;
      is_64bit = 1;
    end
    
    // Completion Operations
    COMPLETION_NO_DATA: begin
      pkt_type = PKT_COMPLETION;
      has_data = 0;
      is_64bit = 0;
    end
    
    COMPLETION_32B: begin
      pkt_type = PKT_COMPLETION;
      has_data = 1;
      is_64bit = 0;
    end
    
    COMPLETION_64B: begin
      pkt_type = PKT_COMPLETION;
      has_data = 1;
      is_64bit = 1;
    end
    
    // Message Operations
    MESSAGE_NO_DATA, MGMT_MSG_NO_DATA: begin
      pkt_type = PKT_MESSAGE;
      has_data = 0;
      is_64bit = 0;
    end
    
    MESSAGE_64B, MGMT_MSG_DATA: begin
      pkt_type = PKT_MESSAGE;
      has_data = 1;
      is_64bit = 1;
    end
    
    default: begin
      `uvm_error("TRANSACTION", $sformatf("Unknown opcode: %s", opcode.name()))
      pkt_type = PKT_REG_ACCESS;
      has_data = 0;
      is_64bit = 0;
    end
  endcase
  
  `uvm_info("TRANSACTION", $sformatf("Updated packet info: type=%s, has_data=%0b, is_64bit=%0b", 
            pkt_type.name(), has_data, is_64bit), UVM_DEBUG)
endfunction

function void ucie_sb_transaction::calculate_parity();
  // Control parity (CP) - XOR of all control fields
  cp = ^{opcode, srcid, dstid, tag, be, ep, cr, addr[15:0]};
  
  // Data parity (DP) - XOR of data if present
  if (has_data) begin
    dp = is_64bit ? ^data : ^data[31:0];
  end else begin
    dp = 1'b0;
  end
  
  `uvm_info("TRANSACTION", $sformatf("Calculated parity: CP=%0b, DP=%0b", cp, dp), UVM_DEBUG)
endfunction

// Packet generation methods
function bit [63:0] ucie_sb_transaction::get_header();
  bit [31:0] phase0, phase1;
  
  // Phase 0: opcode[4:0] + reserved[1:0] + ep + reserved[2:0] + be[7:0] + tag[4:0] + reserved[1:0] + srcid[2:0]
  phase0 = {srcid, 2'b00, tag, be, 3'b000, ep, opcode, 2'b00};
  
  // Phase 1: addr[15:0] + reserved[5:0] + dstid[2:0] + reserved[3:0] + cr + cp + dp
  phase1 = {dp, cp, cr, 4'b0000, dstid, 6'b000000, addr[15:0]};
  
  `uvm_info("TRANSACTION", $sformatf("Generated header: phase0=0x%08h, phase1=0x%08h", phase0, phase1), UVM_DEBUG)
  
  return {phase1, phase0};
endfunction

// Helper/utility methods
function string ucie_sb_transaction::get_srcid_name();
  case (srcid)
    3'b001: return "D2D_ADAPTER";
    3'b010: return "PHYSICAL_LAYER";
    3'b011: return "MGMT_PORT_GATEWAY";
    default: return $sformatf("UNKNOWN_SRCID_%0b", srcid);
  endcase
endfunction

function string ucie_sb_transaction::get_dstid_name();
  case (dstid)
    3'b000: return "LOCAL_DIE";
    3'b001: return "REMOTE_DIE_1";
    3'b010: return "REMOTE_DIE_2"; 
    3'b011: return "REMOTE_DIE_3";
    default: return $sformatf("UNKNOWN_DSTID_%0b", dstid);
  endcase
endfunction

function bit ucie_sb_transaction::is_remote_die_packet();
  return (dstid != 3'b000);
endfunction

function bit ucie_sb_transaction::is_poison_set();
  return ep;
endfunction

function bit ucie_sb_transaction::has_credit_return();
  return cr;
endfunction

// Debug/display methods
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
  s = {s, $sformatf("\n================================")};
  return s;
endfunction