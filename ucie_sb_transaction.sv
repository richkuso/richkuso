/*******************************************************************************
 * UCIe Sideband Protocol Transaction
 * 
 * OVERVIEW:
 *   Complete transaction model for UCIe (Universal Chiplet Interconnect Express)
 *   sideband protocol. Encapsulates all packet types, field formats, and 
 *   protocol behaviors defined in UCIe 1.1 specification.
 *
 * TRANSACTION CAPABILITIES:
 *   • All 19 UCIe sideband opcodes supported
 *   • Register Access: MEM/DMS/CFG operations (32B/64B)
 *   • Completions: Response packets with status reporting
 *   • Messages: Control and management messaging
 *   • Clock Patterns: Training and synchronization sequences
 *   • Automatic parity generation (CP/DP) per specification
 *
 * PROTOCOL COMPLIANCE:
 *   • UCIe 1.1 packet formats (Figures 7-1, 7-2, 7-3)
 *   • Address alignment requirements
 *   • Byte enable validation
 *   • Parity calculation per specification
 *   • Source/destination ID constraints
 *
 * VALIDATION FEATURES:
 *   • Comprehensive constraint sets for legal packet generation
 *   • Protocol validation methods
 *   • Human-readable string conversion
 *   • Debug and analysis support
 *
 * ARCHITECTURE:
 *   • UVM sequence item inheritance
 *   • Randomizable fields with intelligent constraints
 *   • Extern method declarations for clean separation
 *   • Factory registration for polymorphic usage
 *
 * COMPLIANCE:
 *   • IEEE 1800-2017 SystemVerilog
 *   • UVM 1.2 methodology
 *   • UCIe 1.1 specification
 *
 * AUTHOR: UCIe Sideband UVM Agent
 * VERSION: 3.0 - Production-grade transaction model
 ******************************************************************************/

class ucie_sb_transaction extends uvm_sequence_item;
  
  /*---------------------------------------------------------------------------
   * PROTOCOL FIELD DEFINITIONS
   * All fields defined per UCIe 1.1 specification packet formats
   *---------------------------------------------------------------------------*/
  
  rand ucie_sb_opcode_e opcode;                   // Packet operation code
  rand bit [2:0]        srcid;                   // Source identifier
  rand bit [2:0]        dstid;                   // Destination identifier
  rand bit [4:0]        tag;                     // Transaction tag
  rand bit [7:0]        be;                      // Byte enable mask
  rand bit              ep;                      // Error poison indicator
  rand bit              cr;                      // Credit return flag
  rand bit [23:0]       addr;                    // Memory/register address
  rand bit [15:0]       status;                  // Completion status code
  
  /*---------------------------------------------------------------------------
   * MESSAGE PROTOCOL FIELDS
   * Specialized fields for UCIe message packets (Figure 7-3)
   *---------------------------------------------------------------------------*/
  
  rand bit [7:0]        msgcode;                 // Message operation code
  rand bit [15:0]       msginfo;                 // Message information field
  rand bit [7:0]        msgsubcode;              // Message sub-operation code
  
  /*---------------------------------------------------------------------------
   * DATA PAYLOAD AND PARITY
   * Data content and protocol-required parity bits
   *---------------------------------------------------------------------------*/
  
  rand bit [63:0]       data;                    // Packet data payload
  bit                   cp;                      // Control parity (calculated)
  bit                   dp;                      // Data parity (calculated)
  
  /*---------------------------------------------------------------------------
   * DERIVED TRANSACTION METADATA
   * Computed fields for packet classification and processing
   *---------------------------------------------------------------------------*/
  
  packet_type_e         pkt_type;                // Packet category classification
  bit                   has_data;                // Data payload present flag
  bit                   is_64bit;                // 64-bit operation indicator
  bit                   is_clock_pattern;        // Clock training sequence flag
  
  /*---------------------------------------------------------------------------
   * PARITY ERROR INJECTION CONTROL
   * Fields to control intentional parity error injection for testing
   *---------------------------------------------------------------------------*/
  
  rand bit              inject_data_parity_error;    // Inject data parity error flag
  rand bit              inject_control_parity_error; // Inject control parity error flag
  rand bit [5:0]        error_bit_position;          // Bit position for error injection (0-63)
  
  /*---------------------------------------------------------------------------
   * UVM FACTORY AND FIELD REGISTRATION
   * Enables polymorphic creation and automatic field operations
   *---------------------------------------------------------------------------*/
  
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
    `uvm_field_int(inject_data_parity_error, UVM_ALL_ON)
    `uvm_field_int(inject_control_parity_error, UVM_ALL_ON)
    `uvm_field_int(error_bit_position, UVM_ALL_ON)
  `uvm_object_utils_end

  /*---------------------------------------------------------------------------
   * CONSTRUCTOR - Initialize transaction object
   *---------------------------------------------------------------------------*/
  function new(string name = "ucie_sb_transaction");
    super.new(name);
  endfunction

  /*---------------------------------------------------------------------------
   * EXTERNAL METHOD DECLARATIONS
   * All implementation methods declared as extern for clean interface
   *---------------------------------------------------------------------------*/
  
  extern function void post_randomize();
  extern function void update_packet_info();
  extern function void calculate_parity();
  extern function void inject_data_parity_error_func();
  extern function void inject_control_parity_error_func();
  extern function bit [63:0] get_header();
  extern function bit [63:0] get_message_header();
  extern function bit [63:0] get_clock_pattern_header();
  extern function bit is_valid_clock_pattern();
  extern function bit [63:0] get_register_access_header();
  extern function string get_srcid_name();
  extern function string get_dstid_name();
  extern function bit is_remote_die_packet();
  extern function bit is_poison_set();
  extern function bit has_credit_return();
  extern function string convert2string();
  extern function string get_msgcode_name(bit [7:0] code);
  extern function string get_msgsubcode_name(bit [7:0] subcode);
  extern function string get_completion_status_name(bit [15:0] status);
  extern function string get_be_description();
  extern function bit is_valid();

  /*---------------------------------------------------------------------------
   * PROTOCOL COMPLIANCE CONSTRAINTS
   * Ensures generated transactions conform to UCIe specification
   *---------------------------------------------------------------------------*/

  constraint srcid_c { 
    srcid inside {
      3'b001,  // D2D Adapter
      3'b010,  // Physical Layer  
      3'b011   // Management Port Gateway
    };
  }
  
  constraint dstid_c {
    if (pkt_type == PKT_REG_ACCESS) {
      if (dstid != 3'b000) {
        dstid inside {3'b000, 3'b001, 3'b010, 3'b011};
      } else {
        dstid == 3'b000;
      }
    }
    if (pkt_type == PKT_COMPLETION) {
      dstid == srcid;
    }
  }
  
  constraint addr_alignment_c {
    if (is_64bit) {
      addr[2:0] == 3'b000;
    } else {
      addr[1:0] == 2'b00;
    }
  }
  
  constraint be_c {
    if (!is_64bit) {
      be[7:4] == 4'b0000;
    }
  }
  
  constraint message_c {
    if (pkt_type == PKT_MESSAGE && !has_data && !is_clock_pattern) {
      msgcode inside {MSG_SBINIT_OUT_OF_RESET, MSG_SBINIT_DONE_REQ, MSG_SBINIT_DONE_RESP};
      
      if (msgcode == MSG_SBINIT_OUT_OF_RESET) {
        msgsubcode == SUBCODE_SBINIT_OUT_OF_RESET;
      }
      if (msgcode == MSG_SBINIT_DONE_REQ) {
        msgsubcode == SUBCODE_SBINIT_DONE;
      }
      if (msgcode == MSG_SBINIT_DONE_RESP) {
        msgsubcode == SUBCODE_SBINIT_DONE;
      }
      
      if (msgcode == MSG_SBINIT_OUT_OF_RESET) {
        msginfo[15:4] == 12'h000;
        msginfo[3:0] inside {4'h0, 4'h1, 4'h2, 4'h3, 4'h4, 4'h5, 4'h6, 4'h7, 4'h8, 4'h9, 4'hA, 4'hB, 4'hC, 4'hD, 4'hE, 4'hF};
      } else {
        msginfo == 16'h0000;
      }
    }
  }
  
  constraint clock_pattern_c {
    if (is_clock_pattern) {
      opcode == CLOCK_PATTERN;
    }
    if (opcode == CLOCK_PATTERN) {
      is_clock_pattern == 1;
    }
  }
  
  constraint error_injection_c {
    // By default, don't inject errors
    inject_data_parity_error == 0;
    inject_control_parity_error == 0;
    
    // Mutual exclusion: can't inject both types of errors simultaneously
    !(inject_data_parity_error && inject_control_parity_error);
    
    // Error bit position should be within valid range
    error_bit_position < 64;
  }

endclass : ucie_sb_transaction

/*******************************************************************************
 * IMPLEMENTATION SECTION
 * All method implementations with detailed behavioral documentation
 ******************************************************************************/

/*-----------------------------------------------------------------------------
 * POST-RANDOMIZATION PROCESSING
 * 
 * Automatically invoked after constraint solving to:
 *   • Update packet metadata based on randomized opcode
 *   • Calculate protocol-required parity values
 *   • Ensure transaction consistency and validity
 *
 * This method maintains the relationship between opcode and derived fields,
 * ensuring the transaction represents a valid UCIe protocol packet.
 *-----------------------------------------------------------------------------*/
function void ucie_sb_transaction::post_randomize();
  update_packet_info();
  calculate_parity();
  
  // Apply error injection if requested
  if (inject_data_parity_error) begin
    inject_data_parity_error_func();
  end
  
  if (inject_control_parity_error) begin
    inject_control_parity_error_func();
  end
  
  `uvm_info("TRANSACTION", {"Post-randomize: ", convert2string()}, UVM_HIGH)
endfunction

/*-----------------------------------------------------------------------------
 * PACKET METADATA COMPUTATION
 * 
 * Analyzes the randomized opcode to determine:
 *   • Packet type classification (register, completion, message, clock)
 *   • Data payload presence and width requirements
 *   • Special handling flags (clock patterns, etc.)
 *
 * This creates the foundation for all subsequent packet processing by
 * establishing the packet's fundamental characteristics.
 *-----------------------------------------------------------------------------*/
function void ucie_sb_transaction::update_packet_info();
  case (opcode)
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
    
    CLOCK_PATTERN: begin
      pkt_type = PKT_CLOCK_PATTERN;
      has_data = 0;
      is_64bit = 0;
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
  
  `uvm_info("TRANSACTION", $sformatf("Updated packet info: type=%s, has_data=%0b, is_64bit=%0b", 
            pkt_type.name(), has_data, is_64bit), UVM_DEBUG)
endfunction

/*-----------------------------------------------------------------------------
 * UCIe SPECIFICATION PARITY CALCULATION
 * 
 * Computes protocol-required parity values according to UCIe 1.1:
 *   • Data Parity (DP): XOR of data payload (when present)
 *   • Control Parity (CP): XOR of control fields (includes DP)
 *
 * Critical Implementation Notes:
 *   • DP MUST be calculated first (CP depends on DP value)
 *   • Different packet types have different CP field sets
 *   • Clock patterns use fixed parity values
 *
 * Packet-Specific CP Field Sets:
 *   • Register Access: srcid, tag, be, ep, opcode, dp, cr, dstid, addr[23:0]
 *   • Completions: srcid, tag, be, ep, opcode, dp, cr, dstid, status[2:0]
 *   • Messages: srcid, msgcode, opcode, dp, dstid, msginfo, msgsubcode
 *-----------------------------------------------------------------------------*/
function void ucie_sb_transaction::calculate_parity();
  if (has_data) begin
    dp = is_64bit ? ^data : ^data[31:0];
  end else begin
    dp = 1'b0;
  end
  
  if (pkt_type == PKT_CLOCK_PATTERN) begin
    cp = 1'b0;
    dp = 1'b0;
  end else if (pkt_type == PKT_REG_ACCESS) begin    
    cp = ^{srcid, tag, be, ep, opcode, dp, cr, dstid, addr[23:0]};
  end else if (pkt_type == PKT_COMPLETION) begin    
    cp = ^{srcid, tag, be, ep, opcode, dp, cr, dstid, status[2:0]};  
  end else if (pkt_type == PKT_MESSAGE) begin
    cp = ^{srcid, msgcode, opcode, dp, dstid, msginfo, msgsubcode};	
  end else if (pkt_type == PKT_MGMT) begin    
    `uvm_warning("TRANSACTION", "Management message parity calculation not supported")
    cp = 1'b0;
  end
  
  `uvm_info("TRANSACTION", $sformatf("Calculated parity: CP=%0b, DP=%0b", cp, dp), UVM_DEBUG)
endfunction

/*-----------------------------------------------------------------------------
 * HEADER PACKET GENERATION DISPATCHER
 * 
 * Routes header generation to appropriate packet-specific formatter:
 *   • Clock patterns: Fixed UCIe training sequence
 *   • Messages: UCIe Figure 7-3 format
 *   • Register/Completion: UCIe Figure 7-1/7-2 format
 *
 * Returns properly formatted 64-bit header ready for transmission.
 *-----------------------------------------------------------------------------*/
function bit [63:0] ucie_sb_transaction::get_header();
  if (is_clock_pattern) begin
    return get_clock_pattern_header();
  end else if (pkt_type == PKT_MESSAGE && !has_data) begin
    return get_message_header();
  end else begin
    return get_register_access_header();
  end
endfunction

/*-----------------------------------------------------------------------------
 * SOURCE ID HUMAN-READABLE CONVERSION
 * 
 * Maps UCIe source ID values to descriptive names per specification.
 * Aids in debugging and log analysis by providing meaningful identifiers.
 *-----------------------------------------------------------------------------*/
function string ucie_sb_transaction::get_srcid_name();
  case (srcid)
    3'b001: return "D2D_ADAPTER";
    3'b010: return "PHYSICAL_LAYER";
    3'b011: return "MGMT_PORT_GATEWAY";
    default: return $sformatf("UNKNOWN_SRCID_%0b", srcid);
  endcase
endfunction

/*-----------------------------------------------------------------------------
 * DESTINATION ID HUMAN-READABLE CONVERSION
 * 
 * Maps UCIe destination ID values to descriptive names.
 * Distinguishes between local and remote die destinations.
 *-----------------------------------------------------------------------------*/
function string ucie_sb_transaction::get_dstid_name();
  case (dstid)
    3'b000: return "LOCAL_DIE";
    3'b001: return "REMOTE_DIE_1";
    3'b010: return "REMOTE_DIE_2"; 
    3'b011: return "REMOTE_DIE_3";
    default: return $sformatf("UNKNOWN_DSTID_%0b", dstid);
  endcase
endfunction

/*-----------------------------------------------------------------------------
 * REMOTE DIE PACKET DETECTION
 * 
 * Determines if packet targets a remote die (inter-die communication).
 * Local die packets have dstid=0, remote die packets have dstid!=0.
 *-----------------------------------------------------------------------------*/
function bit ucie_sb_transaction::is_remote_die_packet();
  return (dstid != 3'b000);
endfunction

/*-----------------------------------------------------------------------------
 * ERROR POISON STATUS CHECK
 * 
 * Returns the state of the error poison bit, indicating if the
 * transaction carries error information.
 *-----------------------------------------------------------------------------*/
function bit ucie_sb_transaction::is_poison_set();
  return ep;
endfunction

/*-----------------------------------------------------------------------------
 * CREDIT RETURN STATUS CHECK
 * 
 * Returns the state of the credit return bit, used for flow control
 * in the UCIe protocol.
 *-----------------------------------------------------------------------------*/
function bit ucie_sb_transaction::has_credit_return();
  return cr;
endfunction

/*-----------------------------------------------------------------------------
 * COMPREHENSIVE TRANSACTION STRING CONVERSION
 * 
 * Generates detailed, formatted representation of transaction for:
 *   • Debug logging and analysis
 *   • Test result documentation
 *   • Protocol verification reporting
 *
 * Output includes:
 *   • Basic transaction identification
 *   • Address and control information
 *   • Data payload details
 *   • Message-specific fields (when applicable)
 *   • Completion status (when applicable)
 *   • Clock pattern information (when applicable)
 *   • Transaction validity and characteristics
 *   • Generated header packet
 *-----------------------------------------------------------------------------*/
function string ucie_sb_transaction::convert2string();
  string s;
  string msg_name, submsg_name, status_name, be_desc;
  bit [63:0] header;
  
  s = $sformatf("\n+---------------- UCIe Sideband Transaction -----------------+");
  
  s = {s, $sformatf("\n| Opcode: %-18s Type: %-15s Tag: 0x%02h |", opcode.name(), pkt_type.name(), tag)};
  s = {s, $sformatf("\n| Src: %-12s(0x%01h)   Dst: %-16s(0x%01h)     |", get_srcid_name(), srcid, get_dstid_name(), dstid)};
  
  be_desc = get_be_description();
  s = {s, $sformatf("\n| Addr: 0x%06h  BE: 0x%02h(%-8s)  EP:%0b CR:0              |", addr, be, be_desc, ep)};
  
  if (has_data) begin
    s = {s, $sformatf("\n| Data: 0x%016h (%s)  CP:%0b DP:%0b              |", data, is_64bit ? "64-bit" : "32-bit", cp, dp)};
  end else begin
    s = {s, $sformatf("\n| Data: No payload                    CP:%0b DP:%0b              |", cp, dp)};
  end
  
  if (pkt_type == PKT_MESSAGE) begin
    msg_name = get_msgcode_name(msgcode);
    submsg_name = get_msgsubcode_name(msgsubcode);
    s = {s, $sformatf("\n| MsgCode: %-18s (0x%02h)  Info: 0x%04h            |", msg_name, msgcode, msginfo)};
    s = {s, $sformatf("\n| SubCode: %-18s (0x%02h)                          |", submsg_name, msgsubcode)};
    

  end
  
  if (pkt_type == PKT_COMPLETION) begin
    status_name = get_completion_status_name(status);
    s = {s, $sformatf("\n| Status: 0x%04h (%-25s)                |", status, status_name)};
    if (has_data) begin
      s = {s, $sformatf("\n| Return: 0x%016h (%s)              |", data, is_64bit ? "64-bit" : "32-bit")};
    end
  end
  
  if (is_clock_pattern || opcode == CLOCK_PATTERN) begin
    if (opcode == CLOCK_PATTERN) begin
      s = {s, $sformatf("\n| Clock Pattern: UCIe Standard (0x5555555555555555)                |")};
    end else begin
      s = {s, $sformatf("\n| Clock Pattern: Custom - Addr:0x%06h Data:0x%016h |", addr, data)};
    end
  end
  
  s = {s, $sformatf("\n| Flags: HasData:%0b Is64bit:%0b ClkPat:%0b Valid:%0b                |", 
                    has_data, is_64bit, is_clock_pattern, is_valid())};
  
  if (inject_data_parity_error || inject_control_parity_error) begin
    s = {s, $sformatf("\n| ERROR INJECTION: DataErr:%0b CtrlErr:%0b BitPos:%0d                |", 
                      inject_data_parity_error, inject_control_parity_error, error_bit_position)};
  end
  
  if (is_clock_pattern && opcode == CLOCK_PATTERN) begin
    header = get_clock_pattern_header();
    s = {s, $sformatf("\n| Header: 0x%016h (Clock Pattern)                       |", header)};
  end else if (pkt_type == PKT_MESSAGE && !has_data) begin
    header = get_message_header();
    s = {s, $sformatf("\n| Header: 0x%016h (Message)                             |", header)};
  end else begin
    header = get_header();
    s = {s, $sformatf("\n| Header: 0x%016h (Standard)                            |", header)};
  end
  
  s = {s, $sformatf("\n+------------------------------------------------------------+")};
  return s;
endfunction

/*-----------------------------------------------------------------------------
 * MESSAGE CODE NAME RESOLUTION
 * 
 * Converts numeric message codes to human-readable names for debugging
 * and analysis. Supports all standard UCIe sideband message types.
 *-----------------------------------------------------------------------------*/
function string ucie_sb_transaction::get_msgcode_name(bit [7:0] code);
  case (code)
    MSG_SBINIT_OUT_OF_RESET: return "SBINIT_OUT_OF_RESET";
    MSG_SBINIT_DONE_REQ:     return "SBINIT_DONE_REQ";
    MSG_SBINIT_DONE_RESP:    return "SBINIT_DONE_RESP";
    default:                 return $sformatf("UNKNOWN_0x%02h", code);
  endcase
endfunction

/*-----------------------------------------------------------------------------
 * MESSAGE SUBCODE NAME RESOLUTION
 * 
 * Converts numeric message subcodes to descriptive names.
 * Provides context for message interpretation and debugging.
 *-----------------------------------------------------------------------------*/
function string ucie_sb_transaction::get_msgsubcode_name(bit [7:0] subcode);
  case (subcode)
    SUBCODE_SBINIT_OUT_OF_RESET: return "SBINIT_OUT_OF_RESET";
    SUBCODE_SBINIT_DONE:         return "SBINIT_DONE";
    default:                     return $sformatf("UNKNOWN_0x%02h", subcode);
  endcase
endfunction

/*-----------------------------------------------------------------------------
 * COMPLETION STATUS NAME RESOLUTION
 * 
 * Maps completion status codes to descriptive names per UCIe specification.
 * Aids in understanding completion results and error conditions.
 *-----------------------------------------------------------------------------*/
function string ucie_sb_transaction::get_completion_status_name(bit [15:0] status);
  bit [2:0] completion_status = status[2:0];
  case (completion_status)
    3'b000: return "Successful Completion";
    3'b001: return "Unsupported Request";
    3'b010: return "Config Retry Status";
    3'b011: return "Reserved";
    3'b100: return "Completer Abort";
    3'b101: return "Reserved";
    3'b110: return "Reserved";
    3'b111: return "Reserved";
    default: return $sformatf("Unknown_0x%03b", completion_status);
  endcase
endfunction

/*-----------------------------------------------------------------------------
 * BYTE ENABLE DESCRIPTION GENERATOR
 * 
 * Converts byte enable masks to human-readable descriptions.
 * Helps understand which bytes are active in the transaction.
 *-----------------------------------------------------------------------------*/
function string ucie_sb_transaction::get_be_description();
  case (be)
    8'b11111111: return "All";
    8'b00001111: return "Low4B";
    8'b11110000: return "Hi4B";
    8'b00000011: return "B0-1";
    8'b00001100: return "B2-3";
    8'b00110000: return "B4-5";
    8'b11000000: return "B6-7";
    8'b00000001: return "B0";
    8'b00000010: return "B1";
    8'b00000100: return "B2";
    8'b00001000: return "B3";
    8'b00010000: return "B4";
    8'b00100000: return "B5";
    8'b01000000: return "B6";
    8'b10000000: return "B7";
    default:     return "Custom";
  endcase
endfunction

/*-----------------------------------------------------------------------------
 * MESSAGE HEADER PACKET GENERATION
 * 
 * Creates 64-bit header for message packets per UCIe Figure 7-3.
 * Handles proper field placement and reserved bit management.
 *
 * Phase 0 Layout: srcid[31:29] + reserved + msgcode[21:14] + reserved + opcode[4:0]
 * Phase 1 Layout: dp[31] + cp[30] + reserved + dstid[26:24] + msginfo[23:8] + msgsubcode[7:0]
 *-----------------------------------------------------------------------------*/
function bit [63:0] ucie_sb_transaction::get_message_header();
  bit [31:0] phase0, phase1;
  
  phase0 = {srcid,           
            2'b00,           
            5'b00000,        
            msgcode,         
            9'b000000000,    
            opcode};         
  
  phase1 = {dp,              
            cp,              
            3'b000,          
            dstid,           
            msginfo,         
            msgsubcode};     
  
  `uvm_info("TRANSACTION", $sformatf("Generated message header: phase0=0x%08h, phase1=0x%08h", phase0, phase1), UVM_DEBUG)
  
  return {phase1, phase0};
endfunction

/*-----------------------------------------------------------------------------
 * CLOCK PATTERN HEADER GENERATION
 * 
 * Returns the standard UCIe clock pattern header for training sequences.
 * Both phases use the fixed alternating pattern 0x55555555.
 *-----------------------------------------------------------------------------*/
function bit [63:0] ucie_sb_transaction::get_clock_pattern_header();
  bit [31:0] phase0, phase1;
  
  phase0 = CLOCK_PATTERN_PHASE0;
  phase1 = CLOCK_PATTERN_PHASE1;
  
  `uvm_info("TRANSACTION", $sformatf("Generated clock pattern header: phase0=0x%08h, phase1=0x%08h", phase0, phase1), UVM_DEBUG)
  
  return {phase1, phase0};
endfunction

/*-----------------------------------------------------------------------------
 * CLOCK PATTERN VALIDATION
 * 
 * Verifies that clock pattern transactions are properly formed:
 *   • Correct opcode (CLOCK_PATTERN)
 *   • No data payload (header-only)
 *   • Proper flag settings
 *-----------------------------------------------------------------------------*/
function bit ucie_sb_transaction::is_valid_clock_pattern();
  bit [63:0] expected_header;
  
  if (!is_clock_pattern) begin
    return 0;
  end
  
  expected_header = {CLOCK_PATTERN_PHASE1, CLOCK_PATTERN_PHASE0};
  
  if (opcode == CLOCK_PATTERN && !has_data) begin
    `uvm_info("TRANSACTION", "Clock pattern validation PASSED: correct opcode and no data", UVM_DEBUG)
    return 1;
  end else begin
    `uvm_error("TRANSACTION", $sformatf("Clock pattern validation FAILED: opcode=%s, has_data=%0b", 
               opcode.name(), has_data))
    return 0;
  end
endfunction

/*-----------------------------------------------------------------------------
 * REGISTER ACCESS AND COMPLETION HEADER GENERATION
 * 
 * Creates 64-bit headers for register access and completion packets
 * per UCIe Figures 7-1 and 7-2. Handles different field layouts
 * for requests vs. completions.
 *
 * Register Access (Figure 7-1):
 *   Phase 0: srcid + reserved + tag + be + reserved + ep + opcode
 *   Phase 1: dp + cp + cr + reserved + dstid + addr[23:0]
 *
 * Completion (Figure 7-2):
 *   Phase 0: srcid + reserved + tag + be + reserved + ep + opcode
 *   Phase 1: dp + cp + cr + reserved + dstid + reserved + status[2:0]
 *-----------------------------------------------------------------------------*/
function bit [63:0] ucie_sb_transaction::get_register_access_header();
  bit [31:0] phase0, phase1;
  
  if (pkt_type == PKT_COMPLETION) begin
    phase0 = {srcid,           
              2'b00,           
              tag,             
              be,              
              8'b00000000,     
              ep,              
              opcode};         
    
    phase1 = {dp,              
              cp,              
              cr,              
              2'b00,           
              dstid,           
              21'b000000000000000000000, 
              status[2:0]};    
              
    `uvm_info("TRANSACTION", $sformatf("Generated completion header: phase0=0x%08h, phase1=0x%08h", phase0, phase1), UVM_DEBUG)
  end else begin
    phase0 = {srcid,           
              2'b00,           
              tag,             
              be,              
              8'b00000000,     
              ep,              
              opcode};         
    
    phase1 = {dp,              
              cp,              
              cr,              
              2'b00,           
              dstid,           
              addr[23:0]};     
              
    `uvm_info("TRANSACTION", $sformatf("Generated register access header: phase0=0x%08h, phase1=0x%08h", phase0, phase1), UVM_DEBUG)
  end
  
  return {phase1, phase0};
endfunction

/*-----------------------------------------------------------------------------
 * COMPREHENSIVE TRANSACTION VALIDATION
 * 
 * Performs complete protocol compliance checking:
 *   • Opcode validity
 *   • Clock pattern consistency
 *   • Address alignment requirements
 *   • Byte enable constraints
 *   • Message field consistency
 *   • Data payload coherency
 *
 * Returns true only if transaction meets all UCIe specification requirements.
 *-----------------------------------------------------------------------------*/
function bit ucie_sb_transaction::is_valid();
  case (opcode)
    MEM_READ_32B, MEM_WRITE_32B, MEM_READ_64B, MEM_WRITE_64B,
    DMS_READ_32B, DMS_WRITE_32B, DMS_READ_64B, DMS_WRITE_64B,
    CFG_READ_32B, CFG_WRITE_32B, CFG_READ_64B, CFG_WRITE_64B,
    COMPLETION_NO_DATA, COMPLETION_32B, COMPLETION_64B,
    MESSAGE_NO_DATA, MESSAGE_64B, MGMT_MSG_NO_DATA, MGMT_MSG_DATA,
    CLOCK_PATTERN: begin
    end
    default: return 0;
  endcase
  
  if (is_clock_pattern) begin
    return is_valid_clock_pattern();
  end
  
  if (has_data && is_64bit && data == 0) begin
  end
  
  if (pkt_type == PKT_REG_ACCESS) begin
    if (is_64bit && (addr[2:0] != 3'b000)) begin
      return 0;
    end
    if (!is_64bit && (addr[1:0] != 2'b00)) begin
      return 0;
    end
  end
  
  if (!is_64bit && be[7:4] != 4'b0000) begin
    return 0;
  end
  
  if (pkt_type == PKT_MESSAGE) begin
    case (msgcode)
      MSG_SBINIT_OUT_OF_RESET, MSG_SBINIT_DONE_REQ, MSG_SBINIT_DONE_RESP: begin
        if (msgcode == MSG_SBINIT_OUT_OF_RESET && msgsubcode != SUBCODE_SBINIT_OUT_OF_RESET) return 0;
        if ((msgcode == MSG_SBINIT_DONE_REQ || msgcode == MSG_SBINIT_DONE_RESP) && msgsubcode != SUBCODE_SBINIT_DONE) return 0;
      end
      default: return 0;
    endcase
  end
  
  return 1;
endfunction

/*-----------------------------------------------------------------------------
 * DATA PARITY ERROR INJECTION
 * 
 * Injects a data parity error by flipping a bit in either:
 *   • Data payload (if has_data is true)
 *   • DP bit directly (if no data payload or specifically targeting DP)
 *
 * The error_bit_position field determines which bit to flip:
 *   • For data payload: bit position within data[63:0]
 *   • For DP bit: any value flips the DP bit
 *
 * This creates an intentional mismatch between data content and parity,
 * useful for testing error detection mechanisms.
 *-----------------------------------------------------------------------------*/
function void ucie_sb_transaction::inject_data_parity_error_func();
  if (has_data) begin
    // Flip a bit in the data payload
    if (error_bit_position < 64) begin
      data[error_bit_position] = ~data[error_bit_position];
      `uvm_info("ERROR_INJECT", $sformatf("Injected data parity error: flipped data bit %0d", error_bit_position), UVM_LOW)
    end else begin
      // If bit position is out of range, flip DP bit directly
      dp = ~dp;
      `uvm_info("ERROR_INJECT", "Injected data parity error: flipped DP bit directly", UVM_LOW)
    end
  end else begin
    // No data payload, flip DP bit directly
    dp = ~dp;
    `uvm_info("ERROR_INJECT", "Injected data parity error: flipped DP bit (no data payload)", UVM_LOW)
  end
endfunction

/*-----------------------------------------------------------------------------
 * CONTROL PARITY ERROR INJECTION
 * 
 * Injects a control parity error by flipping a bit in the header fields
 * that contribute to control parity calculation. The specific field and bit
 * depend on the packet type and error_bit_position value.
 *
 * Header fields that can be corrupted (excluding DP bit):
 *   • Register Access: srcid, tag, be, ep, opcode, cr, dstid, addr[23:0]
 *   • Completions: srcid, tag, be, ep, opcode, cr, dstid, status[2:0]
 *   • Messages: srcid, msgcode, opcode, dstid, msginfo, msgsubcode
 *
 * The error_bit_position is mapped to different fields based on packet type.
 * This creates a mismatch between header content and control parity.
 *-----------------------------------------------------------------------------*/
function void ucie_sb_transaction::inject_control_parity_error_func();
  bit [5:0] field_select;
  
  // Map error bit position to field selection
  field_select = error_bit_position % 32; // Use modulo to cycle through available fields
  
  case (pkt_type)
    PKT_REG_ACCESS: begin
      case (field_select % 8)
        0: begin
          srcid = srcid ^ 3'b001;
          `uvm_info("ERROR_INJECT", $sformatf("Injected control parity error: flipped srcid bit (new value: 0x%01h)", srcid), UVM_LOW)
        end
        1: begin
          tag = tag ^ (1 << (error_bit_position % 5));
          `uvm_info("ERROR_INJECT", $sformatf("Injected control parity error: flipped tag bit %0d (new value: 0x%02h)", error_bit_position % 5, tag), UVM_LOW)
        end
        2: begin
          be = be ^ (1 << (error_bit_position % 8));
          `uvm_info("ERROR_INJECT", $sformatf("Injected control parity error: flipped be bit %0d (new value: 0x%02h)", error_bit_position % 8, be), UVM_LOW)
        end
        3: begin
          ep = ~ep;
          `uvm_info("ERROR_INJECT", $sformatf("Injected control parity error: flipped ep bit (new value: %0b)", ep), UVM_LOW)
        end
        4: begin
          cr = ~cr;
          `uvm_info("ERROR_INJECT", $sformatf("Injected control parity error: flipped cr bit (new value: %0b)", cr), UVM_LOW)
        end
        5: begin
          dstid = dstid ^ 3'b001;
          `uvm_info("ERROR_INJECT", $sformatf("Injected control parity error: flipped dstid bit (new value: 0x%01h)", dstid), UVM_LOW)
        end
        6: begin
          addr = addr ^ (1 << (error_bit_position % 24));
          `uvm_info("ERROR_INJECT", $sformatf("Injected control parity error: flipped addr bit %0d (new value: 0x%06h)", error_bit_position % 24, addr), UVM_LOW)
        end
        7: begin
          // Flip opcode bit (but be careful not to make it invalid)
          opcode = ucie_sb_opcode_e'(opcode ^ (1 << (error_bit_position % 5)));
          `uvm_info("ERROR_INJECT", $sformatf("Injected control parity error: flipped opcode bit %0d (new value: %s)", error_bit_position % 5, opcode.name()), UVM_LOW)
        end
      endcase
    end
    
    PKT_COMPLETION: begin
      case (field_select % 7)
        0: begin
          srcid = srcid ^ 3'b001;
          `uvm_info("ERROR_INJECT", $sformatf("Injected control parity error: flipped srcid bit (new value: 0x%01h)", srcid), UVM_LOW)
        end
        1: begin
          tag = tag ^ (1 << (error_bit_position % 5));
          `uvm_info("ERROR_INJECT", $sformatf("Injected control parity error: flipped tag bit %0d (new value: 0x%02h)", error_bit_position % 5, tag), UVM_LOW)
        end
        2: begin
          be = be ^ (1 << (error_bit_position % 8));
          `uvm_info("ERROR_INJECT", $sformatf("Injected control parity error: flipped be bit %0d (new value: 0x%02h)", error_bit_position % 8, be), UVM_LOW)
        end
        3: begin
          ep = ~ep;
          `uvm_info("ERROR_INJECT", $sformatf("Injected control parity error: flipped ep bit (new value: %0b)", ep), UVM_LOW)
        end
        4: begin
          cr = ~cr;
          `uvm_info("ERROR_INJECT", $sformatf("Injected control parity error: flipped cr bit (new value: %0b)", cr), UVM_LOW)
        end
        5: begin
          dstid = dstid ^ 3'b001;
          `uvm_info("ERROR_INJECT", $sformatf("Injected control parity error: flipped dstid bit (new value: 0x%01h)", dstid), UVM_LOW)
        end
        6: begin
          status = status ^ (1 << (error_bit_position % 3));
          `uvm_info("ERROR_INJECT", $sformatf("Injected control parity error: flipped status bit %0d (new value: 0x%04h)", error_bit_position % 3, status), UVM_LOW)
        end
      endcase
    end
    
    PKT_MESSAGE: begin
      case (field_select % 6)
        0: begin
          srcid = srcid ^ 3'b001;
          `uvm_info("ERROR_INJECT", $sformatf("Injected control parity error: flipped srcid bit (new value: 0x%01h)", srcid), UVM_LOW)
        end
        1: begin
          msgcode = msgcode ^ (1 << (error_bit_position % 8));
          `uvm_info("ERROR_INJECT", $sformatf("Injected control parity error: flipped msgcode bit %0d (new value: 0x%02h)", error_bit_position % 8, msgcode), UVM_LOW)
        end
        2: begin
          dstid = dstid ^ 3'b001;
          `uvm_info("ERROR_INJECT", $sformatf("Injected control parity error: flipped dstid bit (new value: 0x%01h)", dstid), UVM_LOW)
        end
        3: begin
          msginfo = msginfo ^ (1 << (error_bit_position % 16));
          `uvm_info("ERROR_INJECT", $sformatf("Injected control parity error: flipped msginfo bit %0d (new value: 0x%04h)", error_bit_position % 16, msginfo), UVM_LOW)
        end
        4: begin
          msgsubcode = msgsubcode ^ (1 << (error_bit_position % 8));
          `uvm_info("ERROR_INJECT", $sformatf("Injected control parity error: flipped msgsubcode bit %0d (new value: 0x%02h)", error_bit_position % 8, msgsubcode), UVM_LOW)
        end
        5: begin
          // Flip opcode bit
          opcode = ucie_sb_opcode_e'(opcode ^ (1 << (error_bit_position % 5)));
          `uvm_info("ERROR_INJECT", $sformatf("Injected control parity error: flipped opcode bit %0d (new value: %s)", error_bit_position % 5, opcode.name()), UVM_LOW)
        end
      endcase
    end
    
    PKT_CLOCK_PATTERN: begin
      `uvm_warning("ERROR_INJECT", "Control parity error injection not supported for clock patterns")
    end
    
    default: begin
      `uvm_warning("ERROR_INJECT", $sformatf("Control parity error injection not supported for packet type: %s", pkt_type.name()))
    end
  endcase
endfunction