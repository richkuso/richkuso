// UCIe Sideband Monitor Class - Refactored with extern methods
// Captures serial data from RX path and reconstructs transactions

//=============================================================================
// CLASS: ucie_sb_monitor
//
// DESCRIPTION:
//   UCIe sideband monitor that captures source-synchronous serial data from
//   the RX path and reconstructs complete transactions. Performs protocol
//   validation, parity checking, and statistics collection according to
//   UCIe specification.
//
// FEATURES:
//   - Source-synchronous serial data capture
//   - Header and data packet reconstruction
//   - Automatic parity validation (CP and DP)
//   - UCIe protocol compliance checking
//   - Statistics collection and reporting
//   - Support for all packet types and opcodes
//   - Gap timing validation
//
// AUTHOR: UCIe Sideband UVM Agent
// VERSION: 1.0
//=============================================================================

class ucie_sb_monitor extends uvm_monitor;
  `uvm_component_utils(ucie_sb_monitor)
  
  //=============================================================================
  // CLASS FIELDS
  //=============================================================================
  
  // Interface and ports
  virtual ucie_sb_inf vif;
  uvm_analysis_port #(ucie_sb_transaction) ap;
  
  // Configuration parameters
  real ui_time_ns = 1.25;  // UI time in nanoseconds (800MHz default)
  
  // Statistics
  int packets_captured = 0;
  int bits_captured = 0;
  int protocol_errors = 0;
  
  //=============================================================================
  // CONSTRUCTOR
  //=============================================================================

  //-----------------------------------------------------------------------------
  // FUNCTION: new
  // Creates a new sideband monitor component
  //
  // PARAMETERS:
  //   name   - Component name for UVM hierarchy
  //   parent - Parent component reference
  //-----------------------------------------------------------------------------
  function new(string name = "ucie_sb_monitor", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  //=============================================================================
  // EXTERN FUNCTION/TASK DECLARATIONS
  //=============================================================================
  
  //-----------------------------------------------------------------------------
  // FUNCTION: build_phase
  // UVM build phase - gets interface and creates analysis port
  //
  // PARAMETERS:
  //   phase - UVM phase object
  //-----------------------------------------------------------------------------
  extern virtual function void build_phase(uvm_phase phase);
  
  //-----------------------------------------------------------------------------
  // TASK: run_phase
  // UVM run phase - main monitor loop for capturing transactions
  //
  // PARAMETERS:
  //   phase - UVM phase object
  //-----------------------------------------------------------------------------
  extern virtual task run_phase(uvm_phase phase);
  
  //-----------------------------------------------------------------------------
  // FUNCTION: report_phase
  // UVM report phase - prints statistics
  //
  // PARAMETERS:
  //   phase - UVM phase object
  //-----------------------------------------------------------------------------
  extern virtual function void report_phase(uvm_phase phase);
  
  //-----------------------------------------------------------------------------
  // TASK: wait_for_packet_start
  // Waits for start of packet transmission (posedge clock only)
  // Data can be high or low based on opcode - only clock edge matters
  //-----------------------------------------------------------------------------
  extern virtual task wait_for_packet_start();
  
  //-----------------------------------------------------------------------------
  // TASK: wait_for_packet_gap
  // Waits for minimum gap between packets (32 UI with both CLK and DATA low)
  // During gap: SBRX_CLK and SBRX_DATA both stay low, no clock toggling
  //-----------------------------------------------------------------------------
  extern virtual task wait_for_packet_gap();
  
  //-----------------------------------------------------------------------------
  // FUNCTION: capture_serial_packet
  // Captures a 64-bit serial packet from RX interface sampling on negedge clock
  // Uses negedge sampling for proper source-synchronous data recovery
  // Waits for half clock cycle delay to complete 64-bit transmission (clock gated)
  //
  // RETURNS: 64-bit captured packet
  //-----------------------------------------------------------------------------
  extern virtual task capture_serial_packet(output bit [63:0] packet);
  
  //-----------------------------------------------------------------------------
  // FUNCTION: decode_header
  // Decodes 64-bit header packet into transaction object
  //
  // PARAMETERS:
  //   header - 64-bit header packet to decode
  //
  // RETURNS: Decoded transaction object (null if decode fails)
  //-----------------------------------------------------------------------------
  extern virtual function ucie_sb_transaction decode_header(bit [63:0] header);
  
  //-----------------------------------------------------------------------------
  // FUNCTION: check_transaction_validity
  // Validates captured transaction against UCIe specification
  //
  // PARAMETERS:
  //   trans - Transaction to validate
  //-----------------------------------------------------------------------------
  extern virtual function void check_transaction_validity(ucie_sb_transaction trans);
  

  
  //-----------------------------------------------------------------------------
  // FUNCTION: update_statistics
  // Updates monitor statistics with captured transaction
  //
  // PARAMETERS:
  //   trans - Captured transaction for statistics
  //-----------------------------------------------------------------------------
  extern virtual function void update_statistics(ucie_sb_transaction trans);
  
  //-----------------------------------------------------------------------------
  // FUNCTION: print_statistics
  // Prints current monitor statistics to log
  //-----------------------------------------------------------------------------
  extern virtual function void print_statistics();
  
  //-----------------------------------------------------------------------------
  // FUNCTION: set_ui_time
  // Sets the UI time for gap detection based on clock frequency
  //
  // PARAMETERS:
  //   ui_ns - UI time in nanoseconds (e.g., 1.25 for 800MHz)
  //-----------------------------------------------------------------------------
  extern virtual function void set_ui_time(real ui_ns);

endclass : ucie_sb_monitor

//=============================================================================
// IMPLEMENTATION SECTION
//=============================================================================

//-----------------------------------------------------------------------------
// FUNCTION: build_phase
// UVM build phase - gets interface and creates analysis port
//-----------------------------------------------------------------------------
function void ucie_sb_monitor::build_phase(uvm_phase phase);
  super.build_phase(phase);
  
  // Get virtual interface
  if (!uvm_config_db#(virtual ucie_sb_inf)::get(this, "", "vif", vif))
    `uvm_fatal("MONITOR", "Virtual interface not found")
  
  // Create analysis port
  ap = new("ap", this);
  
  // Get UI time configuration
  if (!uvm_config_db#(real)::get(this, "", "ui_time_ns", ui_time_ns))
    `uvm_warning("MONITOR", $sformatf("UI time not found in config, using default: %.2fns", ui_time_ns))
  else
    `uvm_info("MONITOR", $sformatf("UI time configured: %.2fns", ui_time_ns), UVM_LOW)
  
  `uvm_info("MONITOR", "Sideband monitor built successfully", UVM_LOW)
endfunction

//-----------------------------------------------------------------------------
// TASK: run_phase
// UVM run phase - main monitor loop for capturing transactions
//-----------------------------------------------------------------------------
task ucie_sb_monitor::run_phase(uvm_phase phase);
  ucie_sb_transaction trans;
  bit [63:0] header_packet;
  bit [63:0] data_packet;
  
  `uvm_info("MONITOR", "Starting sideband monitor run phase", UVM_LOW)
  
  forever begin
    // Wait for reset to be released
    wait (!vif.sb_reset);
    
    // Wait for start of packet transmission
    wait_for_packet_start();
    
    // Capture the header packet
    capture_serial_packet(header_packet);
    `uvm_info("MONITOR", $sformatf("Captured header packet: 0x%016h", header_packet), UVM_HIGH)
    
    // Decode header into transaction
    trans = decode_header(header_packet);
    
    if (trans != null) begin
      // Wait for gap after header
      wait_for_packet_gap();
      
      // Capture data packet if transaction indicates data present
      if (trans.has_data) begin
        // Wait for start of data packet
        wait_for_packet_start();
        
        // Capture data packet
        capture_serial_packet(data_packet);
        `uvm_info("MONITOR", $sformatf("Captured data packet: 0x%016h", data_packet), UVM_HIGH)
        
        // Extract data based on transaction width
        if (trans.is_64bit) begin
          trans.data = data_packet;
        end else begin
          trans.data = {32'h0, data_packet[31:0]};
        end
        
        // Wait for gap after data
        wait_for_packet_gap();
      end
      
      // Validate the complete transaction (skip for clock patterns)
      if (!trans.is_clock_pattern) begin
        check_transaction_validity(trans);
      end else begin
        // Clock patterns have their own validation
        if (!trans.is_valid_clock_pattern()) begin
          `uvm_error("MONITOR", "Clock pattern transaction has invalid data pattern")
          protocol_errors++;
        end else begin
          `uvm_info("MONITOR", "Clock pattern validation PASSED", UVM_HIGH)
        end
      end
      
      // Update statistics
      update_statistics(trans);
      
      // Send transaction to analysis port
      ap.write(trans);
      `uvm_info("MONITOR", {"Monitored transaction: ", trans.convert2string()}, UVM_MEDIUM)
    end else begin
      `uvm_error("MONITOR", $sformatf("Failed to decode header packet: 0x%016h", header_packet))
      protocol_errors++;
    end
  end
endtask

//-----------------------------------------------------------------------------
// FUNCTION: report_phase
// UVM report phase - prints statistics
//-----------------------------------------------------------------------------
function void ucie_sb_monitor::report_phase(uvm_phase phase);
  super.report_phase(phase);
  print_statistics();
endfunction

//-----------------------------------------------------------------------------
// TASK: wait_for_packet_start
// Waits for start of packet transmission (posedge clock only)  
// Data can be high or low based on opcode - only clock edge matters
//-----------------------------------------------------------------------------
task ucie_sb_monitor::wait_for_packet_start();
  // Wait for positive edge of RX clock - this indicates packet transmission start
  @(posedge vif.SBRX_CLK);
  
  `uvm_info("MONITOR", "Packet start detected on posedge SBRX_CLK", UVM_DEBUG)
endtask

//-----------------------------------------------------------------------------
// TASK: wait_for_packet_gap
// Waits for minimum gap between packets (32 UI with both CLK and DATA low)
// During gap: SBRX_CLK and SBRX_DATA both stay low, no clock toggling
// Enhanced with reset handling, timeout protection, and better error reporting
// High precision monitoring: checks every 0.2ns for accurate gap detection
//-----------------------------------------------------------------------------
task ucie_sb_monitor::wait_for_packet_gap();
  time gap_start_time;
  time current_time;
  time gap_duration;
  time timeout_time;
  int ui_count;
  int short_gap_count = 0;
  bit gap_valid = 0;
  
  // Calculate timeout (max reasonable gap: 1000 UI)
  timeout_time = 1000 * ui_time_ns * 1ns;
  
  `uvm_info("MONITOR", $sformatf("Waiting for packet gap (32 UI minimum, UI=%.2fns, timeout=%0t, precision=0.2ns)", 
                                 ui_time_ns, timeout_time), UVM_DEBUG)
  
  // Wait for both clock and data to go low (start of gap) with reset check
  while (vif.SBRX_CLK !== 1'b0 || vif.SBRX_DATA !== 1'b0) begin
    if (vif.sb_reset) begin
      `uvm_info("MONITOR", "Reset detected while waiting for gap start - aborting gap wait", UVM_DEBUG)
      return;
    end
    #0.2ns; // Higher precision delay to avoid infinite loop
  end
  
  gap_start_time = $time;
  `uvm_info("MONITOR", $sformatf("Gap started at time %0t", gap_start_time), UVM_DEBUG)
  
  // Monitor the gap duration - both signals must stay low
  while (!gap_valid) begin
    // Check for reset during gap monitoring
    if (vif.sb_reset) begin
      `uvm_info("MONITOR", "Reset detected during gap monitoring - aborting gap wait", UVM_DEBUG)
      return;
    end
    
    #0.2ns; // Check every 0.2 nanoseconds for higher precision
    current_time = $time;
    gap_duration = current_time - gap_start_time;
    ui_count = int'(gap_duration / (ui_time_ns * 1ns));
    
    // Timeout protection
    if (gap_duration > timeout_time) begin
      `uvm_warning("MONITOR", $sformatf("Gap timeout: %0d UI (timeout at 1000 UI) - assuming valid gap", ui_count))
      gap_valid = 1;
      break;
    end
    
    // Check if either signal goes high (gap ends)
    if (vif.SBRX_CLK === 1'b1 || vif.SBRX_DATA === 1'b1) begin
      if (ui_count >= 32) begin
        `uvm_info("MONITOR", $sformatf("Valid gap detected: %0d UI (%0t)", ui_count, gap_duration), UVM_DEBUG)
        gap_valid = 1;
      end else begin
        short_gap_count++;
        `uvm_warning("MONITOR", $sformatf("Gap too short: %0d UI (minimum 32 UI required) - attempt %0d", 
                                          ui_count, short_gap_count))
        
        // Limit retries to prevent infinite loops
        if (short_gap_count >= 5) begin
          `uvm_error("MONITOR", $sformatf("Too many short gaps (%0d attempts) - forcing gap acceptance", short_gap_count))
          protocol_errors++;
          gap_valid = 1;
          break;
        end
        
                 // Gap was too short, wait for signals to go low again and restart
         while (vif.SBRX_CLK !== 1'b0 || vif.SBRX_DATA !== 1'b0) begin
           if (vif.sb_reset) begin
             `uvm_info("MONITOR", "Reset detected during gap restart - aborting gap wait", UVM_DEBUG)
             return;
           end
           #0.2ns;
         end
        gap_start_time = $time;
        `uvm_info("MONITOR", $sformatf("Gap restarted due to insufficient duration (attempt %0d)", short_gap_count), UVM_DEBUG)
      end
    end
    
    // Periodic progress logging for very long gaps (reduced frequency)
    if (ui_count > 32 && (ui_count % 64 == 0)) begin
      `uvm_info("MONITOR", $sformatf("Long gap in progress: %0d UI", ui_count), UVM_HIGH)
    end
  end
  
  `uvm_info("MONITOR", $sformatf("Packet gap complete: %0d UI duration%s", ui_count, 
                                 short_gap_count > 0 ? $sformatf(" (after %0d short gap retries)", short_gap_count) : ""), 
                                 UVM_DEBUG)
endtask

//-----------------------------------------------------------------------------
// TASK: capture_serial_packet
// Captures a 64-bit serial packet from RX interface sampling on negedge clock
// Waits for half clock cycle delay to complete 64-bit transmission (clock gated)
//-----------------------------------------------------------------------------
task ucie_sb_monitor::capture_serial_packet(output bit [63:0] packet);
  
  `uvm_info("MONITOR", "Starting packet capture on negedge SBRX_CLK", UVM_DEBUG)
  
  for (int i = 0; i < 64; i++) begin
    @(negedge vif.SBRX_CLK);  // Sample data on negative edge for source-sync
    packet[i] = vif.SBRX_DATA;
    `uvm_info("MONITOR", $sformatf("Captured bit[%0d] = %0b", i, packet[i]), UVM_HIGH)
  end
  
  // Wait for half clock cycle to complete the 64-bit transmission
  // After 64 negedges, clock will be gated - need half UI delay to finish bit 63
  #(ui_time_ns * 0.5 * 1ns);
  
  `uvm_info("MONITOR", $sformatf("Packet capture complete: 0x%016h (64-bit transmission finished after half-cycle delay)", packet), UVM_DEBUG)
endtask

//-----------------------------------------------------------------------------
// FUNCTION: decode_header
// Decodes 64-bit header packet into transaction object
//-----------------------------------------------------------------------------
function ucie_sb_transaction ucie_sb_monitor::decode_header(bit [63:0] header);
  ucie_sb_transaction trans;
  bit [31:0] phase0, phase1;
  ucie_sb_opcode_e detected_opcode;
  
  // Split header into phases
  phase0 = header[31:0];
  phase1 = header[63:32];
  
  // Create new transaction
  trans = ucie_sb_transaction::type_id::create("monitored_trans");
  
  // Extract opcode first to determine packet format
  detected_opcode = ucie_sb_opcode_e'(phase0[4:0]);
  trans.opcode = detected_opcode;
  
  // Check if this is a UCIe standard clock pattern by matching the fixed pattern
  if (header == {CLOCK_PATTERN_PHASE1, CLOCK_PATTERN_PHASE0}) begin
    trans.opcode = CLOCK_PATTERN;
    trans.is_clock_pattern = 1;
    `uvm_info("MONITOR", "Detected UCIe standard clock pattern (0x5555555555555555)", UVM_MEDIUM)
  end
  // Check if opcode indicates clock pattern but pattern doesn't match (error condition)
  else if (detected_opcode == CLOCK_PATTERN) begin
    trans.is_clock_pattern = 1;
    `uvm_warning("MONITOR", $sformatf("CLOCK_PATTERN opcode detected but header pattern mismatch: 0x%016h (expected 0x5555555555555555)", header))
  end
  // Check if this is a message without data format
  else if (detected_opcode == MESSAGE_NO_DATA || detected_opcode == MGMT_MSG_NO_DATA) begin
    // Message without data format (Figure 7-3)
    // Phase 0: phase0[31:29] srcid + phase0[28:27] rsvd + phase0[26:22] rsvd + 
    // phase0[21:14] msgcode[7:0] + phase0[13:5] rsvd + phase0[4:0] opcode[4:0]
    trans.srcid = phase0[31:29];       // [31:29] srcid
    trans.msgcode = phase0[21:14];     // [21:14] msgcode[7:0]
    
    // Phase 1: phase1[31] dp + phase1[30] cp + phase1[29:27] rsvd + phase1[26:24] dstid +
    // phase1[23:8] MsgInfo[15:0] + phase1[7:0] MsgSubcode[7:0]
    trans.dp = phase1[31];             // [31] dp
    trans.cp = phase1[30];             // [30] cp
    trans.dstid = phase1[26:24];       // [26:24] dstid
    trans.msginfo = phase1[23:8];      // [23:8] MsgInfo[15:0]
    trans.msgsubcode = phase1[7:0];    // [7:0] MsgSubcode[7:0]
    
    `uvm_info("MONITOR", $sformatf("Decoded message: msgcode=0x%02h, msginfo=0x%04h, msgsubcode=0x%02h", 
              trans.msgcode, trans.msginfo, trans.msgsubcode), UVM_MEDIUM)
  end
  else begin
    // Standard register access/completion format (Figure 7-1/7-2)
    // Phase 0: phase0[31:29] srcid + phase0[28:27] rsvd + phase0[26:22] tag[4:0] +
    // phase0[21:14] be[7:0] + phase0[13:6] rsvd + phase0[5] ep + phase0[4:0] opcode[4:0]
    trans.srcid = phase0[31:29];       // [31:29] srcid
    trans.tag = phase0[26:22];         // [26:22] tag[4:0]
    trans.be = phase0[21:14];          // [21:14] be[7:0]
    trans.ep = phase0[5];              // [5] ep
    
    // Phase 1 fields depend on packet type
    trans.dp = phase1[31];             // [31] dp
    trans.cp = phase1[30];             // [30] cp
    trans.cr = phase1[29];             // [29] cr
    trans.dstid = phase1[26:24];       // [26:24] dstid
    
    // Check if this is a completion (has status field)
    if (detected_opcode == COMPLETION_NO_DATA || detected_opcode == COMPLETION_32B || detected_opcode == COMPLETION_64B) begin
      // Figure 7-2: Completion format
      // phase1[23:3] rsvd + phase1[2:0] Status
      trans.status = {13'h0000, phase1[2:0]}; // [2:0] Status, extend to 16-bit
      trans.addr = 24'h000000; // No address in completions
    end else begin
      // Figure 7-1: Register access request format
      // phase1[23:0] addr[23:0]
      trans.addr = phase1[23:0];       // [23:0] addr[23:0]
      trans.status = 16'h0000;         // No status in requests
    end
  end
  
  // Update packet information based on opcode
  trans.update_packet_info();
  
  `uvm_info("MONITOR", $sformatf("Decoded transaction: opcode=%s, src=0x%h, dst=0x%h", 
            trans.opcode.name(), trans.srcid, trans.dstid), UVM_DEBUG)
  
  return trans;
endfunction

//-----------------------------------------------------------------------------
// FUNCTION: check_transaction_validity
// Validates captured transaction against UCIe specification
//-----------------------------------------------------------------------------
function void ucie_sb_monitor::check_transaction_validity(ucie_sb_transaction trans);
  // Check parity
  bit expected_cp, expected_dp;
  
  // Calculate expected control parity
  expected_cp = ^{trans.opcode, trans.srcid, trans.dstid, trans.tag, trans.be, trans.ep, trans.cr, trans.addr[15:0]};
  
  if (trans.cp != expected_cp) begin
    `uvm_error("MONITOR", $sformatf("Control parity mismatch: expected=%0b, actual=%0b", expected_cp, trans.cp))
    protocol_errors++;
  end
  
  // Calculate expected data parity if data present
  if (trans.has_data) begin
    expected_dp = trans.is_64bit ? ^trans.data : ^trans.data[31:0];
    if (trans.dp != expected_dp) begin
      `uvm_error("MONITOR", $sformatf("Data parity mismatch: expected=%0b, actual=%0b", expected_dp, trans.dp))
      protocol_errors++;
    end
  end
  
  // Check UCIe specification compliance
  if (trans.srcid == 3'b000) begin
    `uvm_error("MONITOR", "Invalid srcid=0 (reserved in UCIe specification)")
    protocol_errors++;
  end
  
  // Check address alignment
  if (trans.is_64bit && (trans.addr[2:0] != 3'b000)) begin
    `uvm_error("MONITOR", $sformatf("64-bit transaction address 0x%06h not 64-bit aligned", trans.addr))
    protocol_errors++;
  end
  
  if (!trans.is_64bit && (trans.addr[1:0] != 2'b00)) begin
    `uvm_error("MONITOR", $sformatf("32-bit transaction address 0x%06h not 32-bit aligned", trans.addr))
    protocol_errors++;
  end
  
  // Check byte enables for 32-bit transactions
  if (!trans.is_64bit && (trans.be[7:4] != 4'b0000)) begin
    `uvm_error("MONITOR", $sformatf("32-bit transaction has invalid BE[7:4]=0x%h (should be 0)", trans.be[7:4]))
    protocol_errors++;
  end
  
  // Note: Clock pattern validation is handled separately in run_phase
endfunction



//-----------------------------------------------------------------------------
// FUNCTION: update_statistics
// Updates monitor statistics with captured transaction
//-----------------------------------------------------------------------------
function void ucie_sb_monitor::update_statistics(ucie_sb_transaction trans);
  packets_captured++;
  bits_captured += 64; // Header packet
  
  if (trans.has_data) begin
    bits_captured += 64; // Data packet
  end
  
  `uvm_info("MONITOR", $sformatf("Statistics: %0d packets, %0d bits captured", 
            packets_captured, bits_captured), UVM_DEBUG)
endfunction

//-----------------------------------------------------------------------------
// FUNCTION: print_statistics
// Prints current monitor statistics to log
//-----------------------------------------------------------------------------
function void ucie_sb_monitor::print_statistics();
  `uvm_info("MONITOR", "=== Monitor Statistics ===", UVM_LOW)
  `uvm_info("MONITOR", $sformatf("Packets captured: %0d", packets_captured), UVM_LOW)
  `uvm_info("MONITOR", $sformatf("Bits captured: %0d", bits_captured), UVM_LOW)
  `uvm_info("MONITOR", $sformatf("Protocol errors: %0d", protocol_errors), UVM_LOW)
  if (packets_captured > 0) begin
    `uvm_info("MONITOR", $sformatf("Average bits per packet: %.1f", real'(bits_captured)/real'(packets_captured)), UVM_LOW)
    `uvm_info("MONITOR", $sformatf("Error rate: %.2f%%", real'(protocol_errors)/real'(packets_captured)*100.0), UVM_LOW)
  end
  `uvm_info("MONITOR", "=========================", UVM_LOW)
endfunction

//-----------------------------------------------------------------------------
// FUNCTION: set_ui_time
// Sets the UI time for gap detection based on clock frequency
//-----------------------------------------------------------------------------
function void ucie_sb_monitor::set_ui_time(real ui_ns);
  ui_time_ns = ui_ns;
  `uvm_info("MONITOR", $sformatf("UI time set to %.2fns (%.1fMHz equivalent)", ui_ns, 1000.0/ui_ns), UVM_LOW)
endfunction