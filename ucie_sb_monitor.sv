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
  virtual ucie_sb_interface vif;
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
  //
  // RETURNS: 64-bit captured packet
  //-----------------------------------------------------------------------------
  extern virtual function bit [63:0] capture_serial_packet();
  
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
  // FUNCTION: get_rx_clk_state
  // Returns current state of RX clock signal
  //
  // RETURNS: Current SBRX_CLK value
  //-----------------------------------------------------------------------------
  extern virtual function bit get_rx_clk_state();
  
  //-----------------------------------------------------------------------------
  // FUNCTION: get_rx_data_state
  // Returns current state of RX data signal
  //
  // RETURNS: Current SBRX_DATA value
  //-----------------------------------------------------------------------------
  extern virtual function bit get_rx_data_state();
  
  //-----------------------------------------------------------------------------
  // TASK: wait_rx_cycles
  // Waits for specified number of RX clock cycles
  //
  // PARAMETERS:
  //   num_cycles - Number of cycles to wait
  //-----------------------------------------------------------------------------
  extern virtual task wait_rx_cycles(int num_cycles);
  
  //-----------------------------------------------------------------------------
  // FUNCTION: is_rx_idle
  // Checks if RX interface is in idle state
  //
  // RETURNS: 1 if idle (data low), 0 if active
  //-----------------------------------------------------------------------------
  extern virtual function bit is_rx_idle();
  
  //-----------------------------------------------------------------------------
  // TASK: wait_for_rx_idle
  // Waits for RX interface to become idle
  //-----------------------------------------------------------------------------
  extern virtual task wait_for_rx_idle();
  
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
virtual function void ucie_sb_monitor::build_phase(uvm_phase phase);
  super.build_phase(phase);
  
  // Get virtual interface
  if (!uvm_config_db#(virtual ucie_sb_interface)::get(this, "", "vif", vif))
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
virtual task ucie_sb_monitor::run_phase(uvm_phase phase);
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
    header_packet = capture_serial_packet();
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
        data_packet = capture_serial_packet();
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
      
      // Validate the complete transaction
      check_transaction_validity(trans);
      
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
virtual function void ucie_sb_monitor::report_phase(uvm_phase phase);
  super.report_phase(phase);
  print_statistics();
endfunction

//-----------------------------------------------------------------------------
// TASK: wait_for_packet_start
// Waits for start of packet transmission (posedge clock only)
// Data can be high or low based on opcode - only clock edge matters
//-----------------------------------------------------------------------------
virtual task ucie_sb_monitor::wait_for_packet_start();
  // Wait for positive edge of RX clock - this indicates packet transmission start
  @(posedge vif.SBRX_CLK);
  
  `uvm_info("MONITOR", "Packet start detected on posedge SBRX_CLK", UVM_DEBUG)
endtask

//-----------------------------------------------------------------------------
// TASK: wait_for_packet_gap
// Waits for minimum gap between packets (32 UI with both CLK and DATA low)
// During gap: SBRX_CLK and SBRX_DATA both stay low, no clock toggling
//-----------------------------------------------------------------------------
virtual task ucie_sb_monitor::wait_for_packet_gap();
  time gap_start_time;
  time current_time;
  time gap_duration;
  int ui_count;
  
  `uvm_info("MONITOR", $sformatf("Waiting for packet gap (32 UI minimum, UI=%.2fns)", ui_time_ns), UVM_DEBUG)
  
  // Wait for both clock and data to go low (start of gap)
  while (vif.SBRX_CLK !== 1'b0 || vif.SBRX_DATA !== 1'b0) begin
    #1ns; // Small delay to avoid infinite loop
  end
  
  gap_start_time = $time;
  `uvm_info("MONITOR", $sformatf("Gap started at time %0t", gap_start_time), UVM_DEBUG)
  
  // Monitor the gap duration - both signals must stay low
  forever begin
    #1ns; // Check every nanosecond
    current_time = $time;
    gap_duration = current_time - gap_start_time;
    ui_count = int'(gap_duration / (ui_time_ns * 1ns));
    
    // Check if either signal goes high (gap ends)
    if (vif.SBRX_CLK === 1'b1 || vif.SBRX_DATA === 1'b1) begin
      if (ui_count >= 32) begin
        `uvm_info("MONITOR", $sformatf("Valid gap detected: %0d UI (%0t)", ui_count, gap_duration), UVM_DEBUG)
        break;
      end else begin
        `uvm_warning("MONITOR", $sformatf("Gap too short: %0d UI (minimum 32 UI required)", ui_count))
        // Gap was too short, wait for signals to go low again and restart
        while (vif.SBRX_CLK !== 1'b0 || vif.SBRX_DATA !== 1'b0) begin
          #1ns;
        end
        gap_start_time = $time;
        `uvm_info("MONITOR", "Gap restarted due to insufficient duration", UVM_DEBUG)
      end
    end
    
    // Optional: Log progress for very long gaps
    if (ui_count > 0 && (ui_count % 16 == 0)) begin
      `uvm_info("MONITOR", $sformatf("Gap progress: %0d UI", ui_count), UVM_HIGH)
    end
  end
  
  `uvm_info("MONITOR", $sformatf("Packet gap complete: %0d UI duration", ui_count), UVM_DEBUG)
endtask

//-----------------------------------------------------------------------------
// FUNCTION: capture_serial_packet
// Captures a 64-bit serial packet from RX interface sampling on negedge clock
//-----------------------------------------------------------------------------
virtual function bit [63:0] ucie_sb_monitor::capture_serial_packet();
  bit [63:0] packet;
  
  `uvm_info("MONITOR", "Starting packet capture on negedge SBRX_CLK", UVM_DEBUG)
  
  for (int i = 0; i < 64; i++) begin
    @(negedge vif.SBRX_CLK);  // Sample data on negative edge for source-sync
    packet[i] = vif.SBRX_DATA;
    `uvm_info("MONITOR", $sformatf("Captured bit[%0d] = %0b", i, packet[i]), UVM_HIGH)
  end
  
  `uvm_info("MONITOR", $sformatf("Packet capture complete: 0x%016h", packet), UVM_DEBUG)
  return packet;
endfunction

//-----------------------------------------------------------------------------
// FUNCTION: decode_header
// Decodes 64-bit header packet into transaction object
//-----------------------------------------------------------------------------
virtual function ucie_sb_transaction ucie_sb_monitor::decode_header(bit [63:0] header);
  ucie_sb_transaction trans;
  bit [31:0] phase0, phase1;
  
  // Split header into phases
  phase0 = header[31:0];
  phase1 = header[63:32];
  
  // Create new transaction
  trans = ucie_sb_transaction::type_id::create("monitored_trans");
  
  // Extract opcode first to determine packet format
  ucie_sb_opcode_e detected_opcode = ucie_sb_opcode_e'(phase0[4:0]);
  trans.opcode = detected_opcode;
  
  // Check if this is a clock pattern by matching the fixed pattern
  if (header == {CLOCK_PATTERN_PHASE1, CLOCK_PATTERN_PHASE0}) begin
    trans.opcode = CLOCK_PATTERN;
    trans.is_clock_pattern = 1;
    `uvm_info("MONITOR", "Detected clock pattern transaction", UVM_MEDIUM)
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
virtual function void ucie_sb_monitor::check_transaction_validity(ucie_sb_transaction trans);
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
  
  // Check clock pattern validity
  if (trans.is_clock_pattern) begin
    if (!trans.is_valid_clock_pattern()) begin
      `uvm_error("MONITOR", "Clock pattern transaction has invalid data pattern")
      protocol_errors++;
    end else begin
      `uvm_info("MONITOR", "Clock pattern validation PASSED", UVM_HIGH)
    end
  end
endfunction

//-----------------------------------------------------------------------------
// FUNCTION: get_rx_clk_state
// Returns current state of RX clock signal
//-----------------------------------------------------------------------------
virtual function bit ucie_sb_monitor::get_rx_clk_state();
  return vif.SBRX_CLK;
endfunction

//-----------------------------------------------------------------------------
// FUNCTION: get_rx_data_state
// Returns current state of RX data signal
//-----------------------------------------------------------------------------
virtual function bit ucie_sb_monitor::get_rx_data_state();
  return vif.SBRX_DATA;
endfunction

//-----------------------------------------------------------------------------
// TASK: wait_rx_cycles
// Waits for specified number of RX clock cycles (posedge)
//-----------------------------------------------------------------------------
virtual task ucie_sb_monitor::wait_rx_cycles(int num_cycles);
  `uvm_info("MONITOR", $sformatf("Waiting for %0d RX clock cycles", num_cycles), UVM_DEBUG)
  repeat(num_cycles) @(posedge vif.SBRX_CLK);
  `uvm_info("MONITOR", $sformatf("Completed %0d RX clock cycles", num_cycles), UVM_DEBUG)
endtask

//-----------------------------------------------------------------------------
// FUNCTION: is_rx_idle
// Checks if RX interface is in idle state
//-----------------------------------------------------------------------------
virtual function bit ucie_sb_monitor::is_rx_idle();
  return (vif.SBRX_DATA == 1'b0);
endfunction

//-----------------------------------------------------------------------------
// TASK: wait_for_rx_idle
// Waits for RX interface to become idle (data low on posedge clock)
//-----------------------------------------------------------------------------
virtual task ucie_sb_monitor::wait_for_rx_idle();
  `uvm_info("MONITOR", "Waiting for RX interface to become idle", UVM_DEBUG)
  
  while (vif.SBRX_DATA !== 1'b0) begin
    @(posedge vif.SBRX_CLK);
  end
  
  `uvm_info("MONITOR", "RX interface is now idle", UVM_DEBUG)
endtask

//-----------------------------------------------------------------------------
// FUNCTION: update_statistics
// Updates monitor statistics with captured transaction
//-----------------------------------------------------------------------------
virtual function void ucie_sb_monitor::update_statistics(ucie_sb_transaction trans);
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
virtual function void ucie_sb_monitor::print_statistics();
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
virtual function void ucie_sb_monitor::set_ui_time(real ui_ns);
  ui_time_ns = ui_ns;
  `uvm_info("MONITOR", $sformatf("UI time set to %.2fns (%.1fMHz equivalent)", ui_ns, 1000.0/ui_ns), UVM_LOW)
endfunction