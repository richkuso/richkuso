// UCIe Sideband Transaction Class
// Contains all packet fields and methods for sideband protocol transactions

class sideband_transaction extends uvm_sequence_item;
  // Header fields
  rand sideband_opcode_e opcode;
  rand bit [2:0]         srcid;
  rand bit [2:0]         dstid;
  rand bit [4:0]         tag;
  rand bit [7:0]         be;        // Byte enables
  rand bit               ep;        // Error poison
  rand bit               cr;        // Credit return
  rand bit [23:0]        addr;      // Address (for register access)
  rand bit [15:0]        status;    // Status (for completions)
  
  // Data payload
  rand bit [63:0]        data;
  
  // Control bits
  bit                    cp;        // Control parity
  bit                    dp;        // Data parity
  
  // Derived information
  packet_type_e          pkt_type;
  bit                    has_data;
  bit                    is_64bit;
  
  `uvm_object_utils_begin(sideband_transaction)
    `uvm_field_enum(sideband_opcode_e, opcode, UVM_ALL_ON)
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

  function new(string name = "sideband_transaction");
    super.new(name);
  endfunction

  // UCIe specification compliant constraints
  constraint valid_opcode_c {
    opcode inside {
      MEM_READ_32B, MEM_WRITE_32B, DMS_READ_32B, DMS_WRITE_32B, CFG_READ_32B, CFG_WRITE_32B,
      MEM_READ_64B, MEM_WRITE_64B, DMS_READ_64B, DMS_WRITE_64B, CFG_READ_64B, CFG_WRITE_64B,
      COMPLETION_NO_DATA, COMPLETION_32B, COMPLETION_64B,
      MESSAGE_NO_DATA, MESSAGE_64B, MGMT_MSG_NO_DATA, MGMT_MSG_DATA
    };
  }
  
  // UCIe Table 7-4: srcid encodings
  constraint srcid_c { 
    srcid inside {
      3'b001,  // D2D Adapter
      3'b010,  // Physical Layer
      3'b011   // Management Port Gateway
    };
  }
  
  // UCIe Table 7-4: dstid encodings based on packet type
  constraint dstid_c {
    // For Register Access requests: dstid[1:0] is Reserved, dstid[2] indicates remote die
    if (pkt_type == PKT_REG_ACCESS && opcode inside {MEM_READ_32B, MEM_READ_64B, DMS_READ_32B, DMS_READ_64B, CFG_READ_32B, CFG_READ_64B, MEM_WRITE_32B, MEM_WRITE_64B, DMS_WRITE_32B, DMS_WRITE_64B, CFG_WRITE_32B, CFG_WRITE_64B}) {
      dstid[1:0] == 2'b00;  // Reserved for register access requests
      dstid[2] inside {1'b0, 1'b1};  // 0=local, 1=remote die
    }
    // For Remote die terminated Register Access Completions
    else if (pkt_type == PKT_COMPLETION && dstid[2] == 1'b1) {
      dstid[1:0] == 2'b01;  // D2D Adapter
    }
    // For Remote die terminated messages
    else if (pkt_type inside {PKT_MESSAGE, PKT_MGMT} && dstid[2] == 1'b1) {
      dstid[1:0] inside {
        2'b01,  // D2D Adapter message
        2'b10,  // Physical Layer message
        2'b11   // Management Port Gateway message
      };
    }
    // For local messages/completions
    else {
      dstid inside {[0:7]};  // Allow any encoding for local
    }
  }
  
  constraint tag_c { tag inside {[0:31]}; }
  
  // Address alignment constraints
  constraint addr_alignment_c {
    if (is_64bit) addr[2:0] == 3'b000;
    else if (opcode inside {MEM_READ_32B, MEM_WRITE_32B, DMS_READ_32B, DMS_WRITE_32B, CFG_READ_32B, CFG_WRITE_32B})
      addr[1:0] == 2'b00;
  }
  
  // Byte enable constraints
  constraint be_c {
    if (opcode inside {MEM_READ_32B, MEM_WRITE_32B, DMS_READ_32B, DMS_WRITE_32B, CFG_READ_32B, CFG_WRITE_32B})
      be[7:4] == 4'b0000;
  }

  // Post-randomize to set derived fields
  function void post_randomize();
    update_packet_info();
    calculate_parity();
  endfunction

  // Update packet type and data information based on opcode
  function void update_packet_info();
    case (opcode)
      MEM_READ_32B, MEM_WRITE_32B, DMS_READ_32B, DMS_WRITE_32B, CFG_READ_32B, CFG_WRITE_32B,
      MEM_READ_64B, MEM_WRITE_64B, DMS_READ_64B, DMS_WRITE_64B, CFG_READ_64B, CFG_WRITE_64B: begin
        pkt_type = PKT_REG_ACCESS;
        has_data = (opcode inside {MEM_WRITE_32B, DMS_WRITE_32B, CFG_WRITE_32B, MEM_WRITE_64B, DMS_WRITE_64B, CFG_WRITE_64B});
        is_64bit = (opcode inside {MEM_READ_64B, MEM_WRITE_64B, DMS_READ_64B, DMS_WRITE_64B, CFG_READ_64B, CFG_WRITE_64B});
      end
      COMPLETION_NO_DATA, COMPLETION_32B, COMPLETION_64B: begin
        pkt_type = PKT_COMPLETION;
        has_data = (opcode != COMPLETION_NO_DATA);
        is_64bit = (opcode == COMPLETION_64B);
      end
      MESSAGE_NO_DATA, MESSAGE_64B: begin
        pkt_type = PKT_MESSAGE;
        has_data = (opcode == MESSAGE_64B);
        is_64bit = (opcode == MESSAGE_64B);
      end
      MGMT_MSG_NO_DATA, MGMT_MSG_DATA: begin
        pkt_type = PKT_MGMT;
        has_data = (opcode == MGMT_MSG_DATA);
        is_64bit = (opcode == MGMT_MSG_DATA);
      end
      default: begin
        pkt_type = PKT_REG_ACCESS;
        has_data = 1'b0;
        is_64bit = 1'b0;
      end
    endcase
  endfunction

  // Calculate parity bits
  function void calculate_parity();
    bit [63:0] header_bits;
    
    // Pack header for parity calculation (excluding CP and DP)
    header_bits = {srcid, 2'b00, tag, be, 3'b000, ep, opcode, 
                   1'b0, 1'b0, cr, 4'b0000, dstid, 
                   (pkt_type == PKT_COMPLETION) ? status : addr[15:0]};
    
    // Calculate control parity (even parity of header bits excluding DP)
    cp = ^header_bits;
    
    // Calculate data parity (even parity of data payload)
    if (has_data) begin
      if (is_64bit)
        dp = ^data;
      else
        dp = ^data[31:0];
    end else begin
      dp = 1'b0;
    end
  endfunction

  // Convert to 64-bit header format
  function bit [63:0] get_header();
    bit [63:0] header;
    bit [31:0] phase0, phase1;
    
    // Phase 0: srcid[31:28], rsvd[27:26], tag[25:21], be[20:13], rsvd[12:8], ep[7], opcode[6:2], rsvd[1:0]
    phase0 = {srcid, 2'b00, tag, be, 3'b000, ep, opcode, 2'b00};
    
    // Phase 1: dp[31], cp[30], cr[29], rsvd[28:25], dstid[24:22], rsvd[21:16], addr/status[15:0]
    phase1 = {dp, cp, cr, 4'b0000, dstid, 6'b000000, 
              (pkt_type == PKT_COMPLETION) ? status : addr[15:0]};
    
    header = {phase1, phase0};
    return header;
  endfunction

  // Helper functions for UCIe srcid/dstid interpretation
  function string get_srcid_name();
    case (srcid)
      3'b001: return "D2D_ADAPTER";
      3'b010: return "PHYSICAL_LAYER";
      3'b011: return "MGMT_PORT_GATEWAY";
      default: return "RESERVED";
    endcase
  endfunction
  
  function string get_dstid_name();
    string remote_str = dstid[2] ? "REMOTE_" : "LOCAL_";
    
    if (pkt_type == PKT_REG_ACCESS) begin
      return {remote_str, "REG_ACCESS"};
    end else if (pkt_type == PKT_COMPLETION && dstid[2]) begin
      case (dstid[1:0])
        2'b01: return {remote_str, "D2D_ADAPTER"};
        default: return {remote_str, "RESERVED"};
      endcase
    end else if (pkt_type inside {PKT_MESSAGE, PKT_MGMT} && dstid[2]) begin
      case (dstid[1:0])
        2'b01: return {remote_str, "D2D_ADAPTER_MSG"};
        2'b10: return {remote_str, "PHY_LAYER_MSG"};
        2'b11: return {remote_str, "MGMT_PORT_MSG"};
        default: return {remote_str, "RESERVED_MSG"};
      endcase
    end else begin
      return $sformatf("LOCAL_0x%0h", dstid);
    end
  endfunction
  
  function bit is_remote_die_packet();
    return dstid[2];
  endfunction
  
  function bit is_poison_set();
    return ep;
  endfunction
  
  function bit has_credit_return();
    return cr;
  endfunction
  
  // Enhanced convert to string for debug with UCIe field interpretation
  function string convert2string();
    string s;
    s = $sformatf("SIDEBAND_TXN: opcode=%s, src=%s(0x%0h), dst=%s(0x%0h), tag=%0d", 
                  opcode.name(), get_srcid_name(), srcid, get_dstid_name(), dstid, tag);
    
    if (pkt_type == PKT_REG_ACCESS) begin
      s = {s, $sformatf(", addr=0x%06h, be=0x%02h", addr, be)};
      if (ep) s = {s, ", POISON"};
    end
    
    if (pkt_type == PKT_COMPLETION) begin
      s = {s, $sformatf(", status=0x%04h", status)};
      if (ep) s = {s, ", POISON"};
    end
    
    if (cr) s = {s, ", CREDIT_RETURN"};
    
    if (has_data) begin
      s = {s, $sformatf(", data=0x%0h", is_64bit ? data : data[31:0])};
    end
    
    s = {s, $sformatf(", cp=%0b, dp=%0b", cp, dp)};
    
    return s;
  endfunction
endclass