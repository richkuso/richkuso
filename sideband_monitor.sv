// UCIe Sideband Monitor Class - Refactored with extern methods
// Captures serial data from RX path and reconstructs transactions

//=============================================================================
// CLASS: sideband_monitor
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

class sideband_monitor extends uvm_monitor;
  `uvm_component_utils(sideband_monitor)
  
  //=============================================================================
  // CLASS FIELDS
  //=============================================================================
  
  // Interface and ports
  virtual sideband_interface vif;
  uvm_analysis_port #(sideband_transaction) ap;
  
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
  function new(string name = "sideband_monitor", uvm_component parent = null);
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
  // Waits for start of packet transmission (data goes high on posedge clock)
  // Uses posedge SBRX_CLK for proper source-synchronous timing alignment
  //-----------------------------------------------------------------------------
  extern virtual task wait_for_packet_start();
  
  //-----------------------------------------------------------------------------
  // TASK: wait_for_packet_gap
  // Waits for minimum gap between packets (32 cycles low)
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
  extern virtual function sideband_transaction decode_header(bit [63:0] header);
  
  //-----------------------------------------------------------------------------
  // FUNCTION: check_transaction_validity
  // Validates captured transaction against UCIe specification
  //
  // PARAMETERS:
  //   trans - Transaction to validate
  //-----------------------------------------------------------------------------
  extern virtual function void check_transaction_validity(sideband_transaction trans);
  
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
  extern virtual function void update_statistics(sideband_transaction trans);
  
  //-----------------------------------------------------------------------------
  // FUNCTION: print_statistics
  // Prints current monitor statistics to log
  //-----------------------------------------------------------------------------
  extern virtual function void print_statistics();

endclass : sideband_monitor

//=============================================================================
// IMPLEMENTATION SECTION
//=============================================================================

//-----------------------------------------------------------------------------
// FUNCTION: build_phase
// UVM build phase - gets interface and creates analysis port
//-----------------------------------------------------------------------------
virtual function void sideband_monitor::build_phase(uvm_phase phase);
  super.build_phase(phase);
  
  // Get virtual interface
  if (!uvm_config_db#(virtual sideband_interface)::get(this, "", "vif", vif))
    `uvm_fatal("MONITOR", "Virtual interface not found")
  
  // Create analysis port
  ap = new("ap", this);
  
  `uvm_info("MONITOR", "Sideband monitor built successfully", UVM_LOW)
endfunction

//-----------------------------------------------------------------------------
// TASK: run_phase
// UVM run phase - main monitor loop for capturing transactions
//-----------------------------------------------------------------------------
virtual task sideband_monitor::run_phase(uvm_phase phase);
  sideband_transaction trans;
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
virtual function void sideband_monitor::report_phase(uvm_phase phase);
  super.report_phase(phase);
  print_statistics();
endfunction

//-----------------------------------------------------------------------------
// TASK: wait_for_packet_start
// Waits for start of packet transmission (data goes high on posedge clock)
//-----------------------------------------------------------------------------
virtual task sideband_monitor::wait_for_packet_start();
  // Wait for data to go high on positive edge of RX clock
  do begin
    @(posedge vif.SBRX_CLK);
  end while (vif.SBRX_DATA == 1'b0);
  
  `uvm_info("MONITOR", "Packet start detected on posedge SBRX_CLK", UVM_DEBUG)
endtask

//-----------------------------------------------------------------------------
// TASK: wait_for_packet_gap
// Waits for minimum gap between packets (32 cycles low on posedge clock)
//-----------------------------------------------------------------------------
virtual task sideband_monitor::wait_for_packet_gap();
  int low_count = 0;
  
  `uvm_info("MONITOR", "Waiting for packet gap (32 cycles minimum)", UVM_DEBUG)
  
  while (low_count < 32) begin
    @(posedge vif.SBRX_CLK);  // Check gap on positive edge
    if (vif.SBRX_DATA == 1'b0) begin
      low_count++;
      `uvm_info("MONITOR", $sformatf("Gap count: %0d/32", low_count), UVM_HIGH)
    end else begin
      low_count = 0;  // Reset if data goes high
      `uvm_info("MONITOR", "Gap reset - data went high", UVM_HIGH)
    end
  end
  
  `uvm_info("MONITOR", "Packet gap detected (32 cycles complete)", UVM_DEBUG)
endtask

//-----------------------------------------------------------------------------
// FUNCTION: capture_serial_packet
// Captures a 64-bit serial packet from RX interface sampling on negedge clock
//-----------------------------------------------------------------------------
virtual function bit [63:0] sideband_monitor::capture_serial_packet();
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
virtual function sideband_transaction sideband_monitor::decode_header(bit [63:0] header);
  sideband_transaction trans;
  bit [31:0] phase0, phase1;
  
  // Split header into phases
  phase0 = header[31:0];
  phase1 = header[63:32];
  
  // Create new transaction
  trans = sideband_transaction::type_id::create("monitored_trans");
  
  // Extract fields from phase0
  trans.srcid = phase0[31:29];
  // phase0[28:27] reserved
  trans.tag = phase0[26:22];
  trans.be = phase0[21:14];
  // phase0[13:11] reserved
  trans.ep = phase0[10];
  trans.opcode = sideband_opcode_e'(phase0[9:5]);
  // phase0[4:0] reserved
  
  // Extract fields from phase1
  trans.dp = phase1[31];
  trans.cp = phase1[30];
  trans.cr = phase1[29];
  // phase1[28:25] reserved
  trans.dstid = phase1[24:22];
  // phase1[21:16] reserved
  trans.addr = {8'h00, phase1[15:0]}; // Extend to 24-bit address
  
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
virtual function void sideband_monitor::check_transaction_validity(sideband_transaction trans);
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
endfunction

//-----------------------------------------------------------------------------
// FUNCTION: get_rx_clk_state
// Returns current state of RX clock signal
//-----------------------------------------------------------------------------
virtual function bit sideband_monitor::get_rx_clk_state();
  return vif.SBRX_CLK;
endfunction

//-----------------------------------------------------------------------------
// FUNCTION: get_rx_data_state
// Returns current state of RX data signal
//-----------------------------------------------------------------------------
virtual function bit sideband_monitor::get_rx_data_state();
  return vif.SBRX_DATA;
endfunction

//-----------------------------------------------------------------------------
// TASK: wait_rx_cycles
// Waits for specified number of RX clock cycles (posedge)
//-----------------------------------------------------------------------------
virtual task sideband_monitor::wait_rx_cycles(int num_cycles);
  `uvm_info("MONITOR", $sformatf("Waiting for %0d RX clock cycles", num_cycles), UVM_DEBUG)
  repeat(num_cycles) @(posedge vif.SBRX_CLK);
  `uvm_info("MONITOR", $sformatf("Completed %0d RX clock cycles", num_cycles), UVM_DEBUG)
endtask

//-----------------------------------------------------------------------------
// FUNCTION: is_rx_idle
// Checks if RX interface is in idle state
//-----------------------------------------------------------------------------
virtual function bit sideband_monitor::is_rx_idle();
  return (vif.SBRX_DATA == 1'b0);
endfunction

//-----------------------------------------------------------------------------
// TASK: wait_for_rx_idle
// Waits for RX interface to become idle (data low on posedge clock)
//-----------------------------------------------------------------------------
virtual task sideband_monitor::wait_for_rx_idle();
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
virtual function void sideband_monitor::update_statistics(sideband_transaction trans);
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
virtual function void sideband_monitor::print_statistics();
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