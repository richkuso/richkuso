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

  // Constraints
  constraint valid_opcode_c {
    opcode inside {
      MEM_READ_32B, MEM_WRITE_32B, DMS_READ_32B, DMS_WRITE_32B, CFG_READ_32B, CFG_WRITE_32B,
      MEM_READ_64B, MEM_WRITE_64B, DMS_READ_64B, DMS_WRITE_64B, CFG_READ_64B, CFG_WRITE_64B,
      COMPLETION_NO_DATA, COMPLETION_32B, COMPLETION_64B,
      MESSAGE_NO_DATA, MESSAGE_64B, MGMT_MSG_NO_DATA, MGMT_MSG_DATA
    };
  }
  
  constraint srcid_c { srcid inside {[0:7]}; }
  constraint dstid_c { dstid inside {[0:7]}; }
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

  // Convert to string for debug
  function string convert2string();
    string s;
    s = $sformatf("SIDEBAND_TXN: opcode=%s, srcid=%0d, dstid=%0d, tag=%0d", 
                  opcode.name(), srcid, dstid, tag);
    if (pkt_type == PKT_REG_ACCESS)
      s = {s, $sformatf(", addr=0x%0h, be=0x%0h", addr, be)};
    if (pkt_type == PKT_COMPLETION)
      s = {s, $sformatf(", status=0x%0h", status)};
    if (has_data)
      s = {s, $sformatf(", data=0x%0h", is_64bit ? data : data[31:0])};
    return s;
  endfunction
endclass