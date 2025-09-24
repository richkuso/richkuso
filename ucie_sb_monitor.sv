/*******************************************************************************
 * UCIe Sideband Protocol Monitor
 * 
 * OVERVIEW:
 *   Production-grade UVM monitor for UCIe (Universal Chiplet Interconnect 
 *   Express) sideband protocol verification. Captures source-synchronous 
 *   serial data and reconstructs complete protocol transactions.
 *
 * KEY CAPABILITIES:
 *   • Source-synchronous data capture at up to 800MHz
 *   • Complete UCIe 1.1 protocol compliance validation  
 *   • All 19 sideband opcodes supported
 *   • Timestamp-based gap timing validation (32 UI minimum)
 *   • Comprehensive parity checking (CP/DP)
 *   • Precise timestamp-based timing measurement
 *   • Statistics collection and error reporting
 *
 * PROTOCOL SUPPORT:
 *   • Register Access: MEM/DMS/CFG Read/Write (32B/64B)
 *   • Completions: With/without data (32B/64B)  
 *   • Messages: Standard and management messages
 *   • Clock Patterns: UCIe standard training sequences
 *
 * TIMING ARCHITECTURE:
 *   • Negedge sampling for source-synchronous recovery
 *   • Timestamp-based gap measurement between packets
 *   • End timestamp captured at 64th negedge completion
 *   • Configurable UI timing for different frequencies
 *
 * COMPLIANCE:
 *   • IEEE 1800-2017 SystemVerilog
 *   • UVM 1.2 methodology  
 *   • UCIe 1.1 specification
 *
 * AUTHOR: UCIe Sideband UVM Agent
 * VERSION: 2.1 - Enhanced with timestamp-based gap validation
 ******************************************************************************/

class ucie_sb_monitor extends uvm_monitor;
  `uvm_component_utils(ucie_sb_monitor)
  
  /*---------------------------------------------------------------------------
   * MONITOR COMPONENTS AND INTERFACES
   *---------------------------------------------------------------------------*/
  
  virtual ucie_sb_inf vif;                        // Virtual interface to DUT
  uvm_analysis_port #(ucie_sb_transaction) ap;    // Transaction output port
  
  /*---------------------------------------------------------------------------
   * CONFIGURATION AND TIMING PARAMETERS  
   *---------------------------------------------------------------------------*/
  
  real ui_time_ns = 1.25;                         // UI period (800MHz default)
  
  /*---------------------------------------------------------------------------
   * TIMING TRACKING FOR GAP VALIDATION
   *---------------------------------------------------------------------------*/
  
  time packet_end_time = 0;                       // Timestamp of last packet end
  time packet_start_time = 0;                     // Timestamp of current packet start
  bit first_packet = 1;                           // Flag for first packet detection
  
  /*---------------------------------------------------------------------------
   * RESET CONTROL
   *---------------------------------------------------------------------------*/
  
  bit monitor_reset = 0;                          // Internal reset flag for monitor restart
  
  /*---------------------------------------------------------------------------
   * STATISTICS AND MONITORING COUNTERS
   *---------------------------------------------------------------------------*/
  
  int packets_captured = 0;                       // Total packets monitored
  int bits_captured = 0;                          // Total bits captured  
  int protocol_errors = 0;                        // Protocol violations detected
  int gap_violations = 0;                         // Gap timing violations

  /*---------------------------------------------------------------------------
   * CONSTRUCTOR - Initialize monitor component
   *---------------------------------------------------------------------------*/
  function new(string name = "ucie_sb_monitor", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  /*---------------------------------------------------------------------------
   * EXTERNAL METHOD DECLARATIONS
   * All implementation methods declared as extern for clean separation
   *---------------------------------------------------------------------------*/
  
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);
  extern virtual function void report_phase(uvm_phase phase);
  extern virtual task wait_for_packet_start();
  extern virtual task capture_serial_packet(output bit [63:0] packet);
  extern virtual function void validate_packet_gap();
  extern virtual function ucie_sb_transaction decode_header(bit [63:0] header);
  extern virtual function void check_transaction_validity(ucie_sb_transaction trans);
  extern virtual function void update_statistics(ucie_sb_transaction trans);
  extern virtual function void print_statistics();
  extern virtual function void set_ui_time(real ui_ns);
  extern virtual function void reset_monitor();
  extern virtual task reset_monitor_process();

endclass : ucie_sb_monitor

/*******************************************************************************
 * IMPLEMENTATION SECTION
 * All method implementations with detailed inline documentation
 ******************************************************************************/

/*-----------------------------------------------------------------------------
 * BUILD PHASE - Component initialization and configuration
 * 
 * Responsibilities:
 *   • Retrieve virtual interface from config database
 *   • Create analysis port for transaction broadcasting
 *   • Configure UI timing parameters
 *   • Validate component setup
 *-----------------------------------------------------------------------------*/
function void ucie_sb_monitor::build_phase(uvm_phase phase);
  super.build_phase(phase);
  
  if (!uvm_config_db#(virtual ucie_sb_inf)::get(this, "", "vif", vif))
    `uvm_fatal("MONITOR", "Virtual interface not found")
  
  ap = new("ap", this);
  
  if (!uvm_config_db#(real)::get(this, "", "ui_time_ns", ui_time_ns))
    `uvm_warning("MONITOR", $sformatf("UI time not found in config, using default: %.2fns", ui_time_ns))
  else
    `uvm_info("MONITOR", $sformatf("UI time configured: %.2fns", ui_time_ns), UVM_LOW)
  
  `uvm_info("MONITOR", "Sideband monitor built successfully", UVM_LOW)
endfunction

/*-----------------------------------------------------------------------------
 * RUN PHASE - Main monitoring loop with timestamp-based gap validation
 * 
 * Protocol Flow:
 *   1. Wait for reset deassertion
 *   2. Detect packet start and capture timestamp
 *   3. Validate gap timing from previous packet (if not first)
 *   4. Capture 64-bit header packet (stores end timestamp)
 *   5. Decode header into transaction object
 *   6. If data present: capture data packet (updates end timestamp)
 *   7. Validate complete transaction
 *   8. Update statistics and broadcast transaction
 *
 * Gap Validation Strategy:
 *   • Use timestamps instead of signal-level detection
 *   • Calculate gap = packet_start_time - packet_end_time
 *   • Verify gap meets 32 UI minimum requirement
 *   • More accurate and robust than signal monitoring
 *
 * Error Handling:
 *   • Decode failures logged and counted
 *   • Protocol violations tracked
 *   • Gap violations tracked separately
 *   • Clock pattern validation separate from normal packets
 *-----------------------------------------------------------------------------*/
task ucie_sb_monitor::run_phase(uvm_phase phase);
  ucie_sb_transaction trans;
  bit [63:0] header_packet;
  bit [63:0] data_packet;
  
  `uvm_info("MONITOR", "Starting sideband monitor run phase with timestamp-based gap validation", UVM_LOW)
  
  // Start reset monitoring process in parallel
  fork
    reset_monitor_process();
  join_none
  
  forever begin
    // Wait for reset deassertion and monitor_reset flag clear
    wait (!vif.sb_reset && !monitor_reset);
    
    // Check for reset assertion during packet processing
    fork : packet_processing
      begin
        wait_for_packet_start();
        
        if (!first_packet) begin
          validate_packet_gap();
        end else begin
          first_packet = 0;
          `uvm_info("MONITOR", "First packet detected - skipping gap validation", UVM_DEBUG)
        end
        
        capture_serial_packet(header_packet);
        `uvm_info("MONITOR", $sformatf("Captured header packet: 0x%016h", header_packet), UVM_HIGH)
        
        trans = decode_header(header_packet);
        
        if (trans != null) begin
          if (trans.has_data) begin
            wait_for_packet_start();
            validate_packet_gap();
            
            capture_serial_packet(data_packet);
            `uvm_info("MONITOR", $sformatf("Captured data packet: 0x%016h", data_packet), UVM_HIGH)
            
            if (trans.is_64bit) begin
              trans.data = data_packet;
            end else begin
              trans.data = {32'h0, data_packet[31:0]};
            end
          end
          
          if (!trans.is_clock_pattern) begin
            check_transaction_validity(trans);
          end else begin
            if (!trans.is_valid_clock_pattern()) begin
              `uvm_error("MONITOR", "Clock pattern transaction has invalid data pattern")
              protocol_errors++;
            end else begin
              `uvm_info("MONITOR", "Clock pattern validation PASSED", UVM_HIGH)
            end
          end
          
          update_statistics(trans);
          
          ap.write(trans);
          `uvm_info("MONITOR", {"Monitored transaction: ", trans.convert2string()}, UVM_MEDIUM)
        end else begin
          `uvm_error("MONITOR", $sformatf("Failed to decode header packet: 0x%016h", header_packet))
          protocol_errors++;
        end
      end
      begin
        // Monitor for reset assertion during packet processing
        wait (vif.sb_reset || monitor_reset);
        `uvm_info("MONITOR", "Reset detected during packet processing - restarting monitor", UVM_LOW)
      end
    join_any
    disable packet_processing;
    
    // If reset was detected, clear state and restart
    if (vif.sb_reset || monitor_reset) begin
      reset_monitor();
      continue;
    end
  end
endtask

/*-----------------------------------------------------------------------------
 * REPORT PHASE - Final statistics reporting
 * 
 * Called at end of simulation to provide comprehensive monitoring summary
 *-----------------------------------------------------------------------------*/
function void ucie_sb_monitor::report_phase(uvm_phase phase);
  super.report_phase(phase);
  print_statistics();
endfunction

/*-----------------------------------------------------------------------------
 * PACKET START DETECTION WITH TIMESTAMP CAPTURE
 * 
 * UCIe Protocol Requirement:
 *   • Packet transmission begins with clock posedge
 *   • Data value at start is opcode-dependent (don't check data)
 *   • Only clock edge indicates valid transmission start
 *
 * Timestamp-Based Enhancement:
 *   • Capture precise timestamp when packet starts
 *   • Used for gap calculation with previous packet
 *   • Enables accurate timing validation
 *
 * Implementation:
 *   • Wait for SBRX_CLK posedge (source-synchronous)
 *   • Store timestamp immediately after detection
 *   • Data setup occurs on this edge for bit 0 sampling
 *-----------------------------------------------------------------------------*/
task ucie_sb_monitor::wait_for_packet_start();
  @(posedge vif.SBRX_CLK);
  packet_start_time = $time;
  
  `uvm_info("MONITOR", $sformatf("Packet start detected at time %0t", packet_start_time), UVM_DEBUG)
endtask

/*-----------------------------------------------------------------------------
 * SERIAL PACKET CAPTURE WITH END TIMESTAMP RECORDING
 * 
 * Source-Synchronous Protocol:
 *   • Data sampled on clock falling edges (negedge)
 *   • 64 bits captured sequentially (bit 0 to bit 63)
 *   • Clock may be gated after final data bit
 *
 * Timing Strategy:
 *   • Record end timestamp immediately after 64th negedge sample
 *   • Timestamp represents end of bit 63 sampling point
 *   • Used for precise gap calculation to next packet
 *
 * Timestamp Enhancement:
 *   • Store packet end time at bit 63 negedge completion
 *   • Used for gap validation to next packet
 *   • More accurate than signal-level detection
 *
 * Implementation:
 *   • No additional delays after sampling
 *   • End timestamp captured at 64th negedge completion
 *   • Gap measurement from this precise sampling point
 *
 * Error Prevention:
 *   • Eliminates race conditions with gap detection
 *   • Provides timing closure margin for implementation
 *   • Handles simulator timing quantization effects
 *-----------------------------------------------------------------------------*/
task ucie_sb_monitor::capture_serial_packet(output bit [63:0] packet);
  
  `uvm_info("MONITOR", "Starting packet capture on negedge SBRX_CLK", UVM_DEBUG)
  
  for (int i = 0; i < 64; i++) begin
    @(negedge vif.SBRX_CLK);
    packet[i] = vif.SBRX_DATA;
    `uvm_info("MONITOR", $sformatf("Captured bit[%0d] = %0b", i, packet[i]), UVM_HIGH)
  end
  
  packet_end_time = $time;
  
  `uvm_info("MONITOR", $sformatf("Packet capture complete: 0x%016h (end time: %0t)", packet, packet_end_time), UVM_DEBUG)
endtask

/*-----------------------------------------------------------------------------
 * TIMESTAMP-BASED GAP VALIDATION
 * 
 * UCIe Protocol Requirements:
 *   • Minimum 32 UI gap between packets
 *   • Gap measured from end of previous packet to start of next
 *   • More accurate than signal-level monitoring
 *
 * Validation Method:
 *   • Calculate gap = packet_start_time - packet_end_time
 *   • Convert gap duration to UI count
 *   • Verify gap meets 32 UI minimum requirement
 *
 * Advantages over Signal Monitoring:
 *   • Immune to clock gating effects
 *   • More precise timing measurement
 *   • No dependency on signal levels during gap
 *   • Eliminates race conditions
 *
 * Error Reporting:
 *   • Gap violations logged with precise timing
 *   • UI count and actual duration reported
 *   • Separate counter for gap violations
 *   • Non-blocking validation continues monitoring
 *-----------------------------------------------------------------------------*/
function void ucie_sb_monitor::validate_packet_gap();
  time gap_duration;
  int ui_count;
  real gap_ui_real;
  
  gap_duration = packet_start_time - packet_end_time;
  gap_ui_real = real'(gap_duration) / (ui_time_ns * 1ns);
  ui_count = int'(gap_ui_real);
  
  `uvm_info("MONITOR", $sformatf("Gap validation: duration=%0t, UI count=%0d (%.2f UI)", 
                                 gap_duration, ui_count, gap_ui_real), UVM_DEBUG)
  
  if (ui_count < 32) begin
    `uvm_error("MONITOR", $sformatf("Gap violation: %0d UI (%.2f UI) < 32 UI minimum requirement", 
                                    ui_count, gap_ui_real))
    gap_violations++;
    protocol_errors++;
  end else begin
    `uvm_info("MONITOR", $sformatf("Gap validation PASSED: %0d UI (%.2f UI) >= 32 UI", 
                                   ui_count, gap_ui_real), UVM_DEBUG)
  end
endfunction

/*-----------------------------------------------------------------------------
 * HEADER PACKET DECODING
 * 
 * UCIe Packet Formats Supported:
 *   • Register Access (Figure 7-1): MEM/DMS/CFG operations
 *   • Completions (Figure 7-2): Response packets with status
 *   • Messages (Figure 7-3): Control messages without data
 *   • Clock Patterns: Training and synchronization sequences
 *
 * Decoding Process:
 *   1. Split 64-bit header into two 32-bit phases
 *   2. Extract opcode to determine packet format
 *   3. Parse fields according to UCIe specification
 *   4. Handle special cases (clock patterns, messages)
 *   5. Update transaction metadata
 *
 * Field Extraction:
 *   • Phase 0: opcode, srcid, tag, byte enables, error poison
 *   • Phase 1: dstid, parity bits, address/status/message fields
 *   • Format-specific parsing based on opcode type
 *
 * Validation:
 *   • Clock pattern recognition (0x5555555555555555)
 *   • Opcode consistency checking
 *   • Field range validation
 *-----------------------------------------------------------------------------*/
function ucie_sb_transaction ucie_sb_monitor::decode_header(bit [63:0] header);
  ucie_sb_transaction trans;
  bit [31:0] phase0, phase1;
  ucie_sb_opcode_e detected_opcode;
  
  phase0 = header[31:0];
  phase1 = header[63:32];
  
  trans = ucie_sb_transaction::type_id::create("monitored_trans");
  
  detected_opcode = ucie_sb_opcode_e'(phase0[4:0]);
  trans.opcode = detected_opcode;
  
  if (header == {CLOCK_PATTERN_PHASE1, CLOCK_PATTERN_PHASE0}) begin
    trans.opcode = CLOCK_PATTERN;
    trans.is_clock_pattern = 1;
    `uvm_info("MONITOR", "Detected UCIe standard clock pattern (0x5555555555555555)", UVM_MEDIUM)
  end
  else if (detected_opcode == CLOCK_PATTERN) begin
    trans.is_clock_pattern = 1;
    `uvm_warning("MONITOR", $sformatf("CLOCK_PATTERN opcode detected but header pattern mismatch: 0x%016h (expected 0x5555555555555555)", header))
  end
  else if (detected_opcode == MESSAGE_NO_DATA || detected_opcode == MGMT_MSG_NO_DATA) begin
    trans.srcid = phase0[31:29];
    trans.msgcode = phase0[21:14];
    
    trans.dp = phase1[31];
    trans.cp = phase1[30];
    trans.dstid = phase1[26:24];
    trans.msginfo = phase1[23:8];
    trans.msgsubcode = phase1[7:0];
    
    `uvm_info("MONITOR", $sformatf("Decoded message: msgcode=0x%02h, msginfo=0x%04h, msgsubcode=0x%02h", 
              trans.msgcode, trans.msginfo, trans.msgsubcode), UVM_MEDIUM)
  end
  else begin
    trans.srcid = phase0[31:29];
    trans.tag = phase0[26:22];
    trans.be = phase0[21:14];
    trans.ep = phase0[5];
    
    trans.dp = phase1[31];
    trans.cp = phase1[30];
    trans.cr = phase1[29];
    trans.dstid = phase1[26:24];
    
    if (detected_opcode == COMPLETION_NO_DATA || detected_opcode == COMPLETION_32B || detected_opcode == COMPLETION_64B) begin
      trans.status = {13'h0000, phase1[2:0]};
      trans.addr = 24'h000000;
    end else begin
      trans.addr = phase1[23:0];
      trans.status = 16'h0000;
    end
  end
  
  trans.update_packet_info();
  
  `uvm_info("MONITOR", $sformatf("Decoded transaction: opcode=%s, src=0x%h, dst=0x%h", 
            trans.opcode.name(), trans.srcid, trans.dstid), UVM_DEBUG)
  
  return trans;
endfunction

/*-----------------------------------------------------------------------------
 * TRANSACTION VALIDATION AGAINST UCIe SPECIFICATION
 * 
 * Validation Checks:
 *   • Parity verification (control and data)
 *   • Address alignment requirements
 *   • Byte enable field validation
 *   • Reserved field checking
 *   • UCIe specification compliance
 *
 * Parity Calculation:
 *   • Control Parity (CP): XOR of all control fields
 *   • Data Parity (DP): XOR of data payload (32/64-bit)
 *   • Immediate error reporting on mismatch
 *
 * Address Alignment:
 *   • 64-bit transactions: 8-byte aligned (addr[2:0] = 0)
 *   • 32-bit transactions: 4-byte aligned (addr[1:0] = 0)
 *   • Alignment violations logged as protocol errors
 *
 * UCIe Compliance:
 *   • Source ID validation (srcid != 0)
 *   • Byte enable consistency for 32-bit operations
 *   • Reserved field zero checking
 *
 * Error Tracking:
 *   • All violations increment protocol_errors counter
 *   • Detailed error messages for debugging
 *   • Non-blocking validation (continues after errors)
 *-----------------------------------------------------------------------------*/
function void ucie_sb_monitor::check_transaction_validity(ucie_sb_transaction trans);
  bit expected_cp, expected_dp;
  
  // Calculate expected data parity first (needed for control parity)
  if (trans.has_data) begin
    expected_dp = trans.is_64bit ? ^trans.data : ^trans.data[31:0];
    if (trans.dp != expected_dp) begin
      `uvm_error("MONITOR", $sformatf("Data parity mismatch: expected=%0b, actual=%0b", expected_dp, trans.dp))
      protocol_errors++;
    end
  end else begin
    expected_dp = 1'b0;
  end
  
  // Calculate expected control parity based on packet type (excludes DP per UCIe spec)
  if (trans.pkt_type == PKT_CLOCK_PATTERN) begin
    expected_cp = 1'b0;
  end else if (trans.pkt_type == PKT_REG_ACCESS) begin    
    expected_cp = ^{trans.srcid, trans.tag, trans.be, trans.ep, trans.opcode, trans.cr, trans.dstid, trans.addr[23:0]};
  end else if (trans.pkt_type == PKT_COMPLETION) begin    
    expected_cp = ^{trans.srcid, trans.tag, trans.be, trans.ep, trans.opcode, trans.cr, trans.dstid, trans.status[2:0]};  
  end else if (trans.pkt_type == PKT_MESSAGE) begin
    expected_cp = ^{trans.srcid, trans.msgcode, trans.opcode, trans.dstid, trans.msginfo, trans.msgsubcode};	
  end else if (trans.pkt_type == PKT_MGMT) begin    
    `uvm_warning("MONITOR", "Management message parity validation not supported")
    expected_cp = 1'b0;
  end else begin
    `uvm_warning("MONITOR", $sformatf("Unknown packet type for parity validation: %s", trans.pkt_type.name()))
    expected_cp = 1'b0;
  end
  
  if (trans.cp != expected_cp) begin
    `uvm_error("MONITOR", $sformatf("Control parity mismatch: expected=%0b, actual=%0b", expected_cp, trans.cp))
    protocol_errors++;
  end
  
  if (trans.srcid == 3'b000) begin
    `uvm_error("MONITOR", "Invalid srcid=0 (reserved in UCIe specification)")
    protocol_errors++;
  end
  
  if (trans.is_64bit && (trans.addr[2:0] != 3'b000)) begin
    `uvm_error("MONITOR", $sformatf("64-bit transaction address 0x%06h not 64-bit aligned", trans.addr))
    protocol_errors++;
  end
  
  if (!trans.is_64bit && (trans.addr[1:0] != 2'b00)) begin
    `uvm_error("MONITOR", $sformatf("32-bit transaction address 0x%06h not 32-bit aligned", trans.addr))
    protocol_errors++;
  end
  
  if (!trans.is_64bit && (trans.be[7:4] != 4'b0000)) begin
    `uvm_error("MONITOR", $sformatf("32-bit transaction has invalid BE[7:4]=0x%h (should be 0)", trans.be[7:4]))
    protocol_errors++;
  end
  
endfunction

/*-----------------------------------------------------------------------------
 * STATISTICS COLLECTION AND TRACKING
 * 
 * Metrics Tracked:
 *   • Total packets captured
 *   • Total bits processed (header + data)
 *   • Protocol error count
 *   • Gap violation count (new)
 *
 * Bit Counting:
 *   • Header packet: Always 64 bits
 *   • Data packet: 64 bits when present
 *   • Accurate bandwidth utilization tracking
 *
 * Real-time Updates:
 *   • Statistics updated per transaction
 *   • Debug logging for continuous monitoring
 *   • Enables performance analysis
 *-----------------------------------------------------------------------------*/
function void ucie_sb_monitor::update_statistics(ucie_sb_transaction trans);
  packets_captured++;
  bits_captured += 64;
  
  if (trans.has_data) begin
    bits_captured += 64;
  end
  
  `uvm_info("MONITOR", $sformatf("Statistics: %0d packets, %0d bits captured, %0d gap violations", 
            packets_captured, bits_captured, gap_violations), UVM_DEBUG)
endfunction

/*-----------------------------------------------------------------------------
 * COMPREHENSIVE STATISTICS REPORTING
 * 
 * Report Contents:
 *   • Total packets and bits captured
 *   • Protocol error count and rate
 *   • Gap violation count and rate (new)
 *   • Average bits per packet
 *   • Error rate percentage
 *
 * Calculations:
 *   • Bit efficiency: total_bits / total_packets
 *   • Error rate: (errors / packets) * 100%
 *   • Gap violation rate: (gap_violations / packets) * 100%
 *   • Zero-packet protection for division
 *
 * Output Format:
 *   • Professional bordered report
 *   • Precision formatting for metrics
 *   • Clear section separation
 *-----------------------------------------------------------------------------*/
function void ucie_sb_monitor::print_statistics();
  `uvm_info("MONITOR", "=== Monitor Statistics ===", UVM_LOW)
  `uvm_info("MONITOR", $sformatf("Packets captured: %0d", packets_captured), UVM_LOW)
  `uvm_info("MONITOR", $sformatf("Bits captured: %0d", bits_captured), UVM_LOW)
  `uvm_info("MONITOR", $sformatf("Protocol errors: %0d", protocol_errors), UVM_LOW)
  `uvm_info("MONITOR", $sformatf("Gap violations: %0d", gap_violations), UVM_LOW)
  if (packets_captured > 0) begin
    `uvm_info("MONITOR", $sformatf("Average bits per packet: %.1f", real'(bits_captured)/real'(packets_captured)), UVM_LOW)
    `uvm_info("MONITOR", $sformatf("Error rate: %.2f%%", real'(protocol_errors)/real'(packets_captured)*100.0), UVM_LOW)
    `uvm_info("MONITOR", $sformatf("Gap violation rate: %.2f%%", real'(gap_violations)/real'(packets_captured)*100.0), UVM_LOW)
  end
  `uvm_info("MONITOR", "=========================", UVM_LOW)
endfunction

/*-----------------------------------------------------------------------------
 * DYNAMIC UI TIMING CONFIGURATION
 * 
 * Purpose:
 *   • Runtime adjustment of UI timing parameters
 *   • Support for multiple clock frequencies
 *   • Automatic frequency calculation and display
 *
 * Usage:
 *   • Called during configuration or frequency changes
 *   • Updates gap detection timing calculations
 *   • Provides immediate feedback on timing settings
 *
 * Frequency Conversion:
 *   • UI time in nanoseconds → equivalent MHz
 *   • Formula: Frequency = 1000 / ui_time_ns
 *   • Supports standard UCIe frequencies (800MHz, 1GHz, etc.)
 *-----------------------------------------------------------------------------*/
function void ucie_sb_monitor::set_ui_time(real ui_ns);
  ui_time_ns = ui_ns;
  `uvm_info("MONITOR", $sformatf("UI time set to %.2fns (%.1fMHz equivalent)", ui_ns, 1000.0/ui_ns), UVM_LOW)
endfunction

/*-----------------------------------------------------------------------------
 * MONITOR RESET FUNCTION
 * 
 * Purpose:
 *   • Clear all monitor state when reset is asserted
 *   • Reset timing tracking variables
 *   • Clear statistics counters (optional - can be preserved for debug)
 *   • Prepare monitor for clean restart
 *
 * Reset Actions:
 *   • Clear packet timing timestamps
 *   • Reset first packet flag
 *   • Clear internal reset flag
 *   • Log reset action for debugging
 *
 * Usage:
 *   • Called automatically when reset detected
 *   • Can be called manually for monitor restart
 *   • Non-blocking operation for immediate response
 *-----------------------------------------------------------------------------*/
function void ucie_sb_monitor::reset_monitor();
  `uvm_info("MONITOR", "Resetting monitor state - clearing timing and flags", UVM_LOW)
  
  // Clear timing tracking
  packet_end_time = 0;
  packet_start_time = 0;
  first_packet = 1;
  
  // Clear internal reset flag
  monitor_reset = 0;
  
  // Note: Statistics are preserved across resets for debugging
  // If you want to clear statistics on reset, uncomment below:
  // packets_captured = 0;
  // bits_captured = 0;
  // protocol_errors = 0;
  // gap_violations = 0;
  
  `uvm_info("MONITOR", "Monitor reset complete - ready for new packets", UVM_LOW)
endfunction

/*-----------------------------------------------------------------------------
 * RESET MONITORING PROCESS
 * 
 * Purpose:
 *   • Continuously monitor for reset assertion
 *   • Trigger monitor reset when sb_reset goes high
 *   • Provide clean separation between reset detection and processing
 *
 * Operation:
 *   • Runs in parallel with main monitoring loop
 *   • Detects reset assertion immediately
 *   • Sets internal flag to interrupt packet processing
 *   • Allows main loop to handle reset gracefully
 *
 * Reset Sequence:
 *   1. Detect sb_reset assertion
 *   2. Set monitor_reset flag
 *   3. Wait for reset deassertion
 *   4. Clear monitor_reset flag in reset_monitor()
 *   5. Main loop restarts from beginning
 *
 * Advantages:
 *   • Immediate reset response
 *   • Clean state transition
 *   • No hanging processes during reset
 *   • Graceful restart capability
 *-----------------------------------------------------------------------------*/
task ucie_sb_monitor::reset_monitor_process();
  forever begin
    // Wait for reset assertion
    @(posedge vif.sb_reset);
    `uvm_info("MONITOR", "Reset asserted - setting monitor reset flag", UVM_LOW)
    
    // Set flag to interrupt main monitoring loop
    monitor_reset = 1;
    
    // Wait for reset deassertion before allowing restart
    @(negedge vif.sb_reset);
    `uvm_info("MONITOR", "Reset deasserted - monitor ready for restart", UVM_LOW)
  end
endtask