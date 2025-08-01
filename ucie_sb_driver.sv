// UCIe Sideband Driver Class - Refactored with extern methods
// Converts UVM transactions to serial bit stream on TX path

//=============================================================================
// DRIVER CONFIGURATION CLASS
//=============================================================================

//=============================================================================
// CLASS: ucie_sb_driver_config
//
// DESCRIPTION:
//   Configuration class for the UCIe sideband driver containing timing
//   parameters, protocol settings, and feature enables. Supports 800MHz
//   source-synchronous operation with configurable duty cycle and gap timing.
//
// FEATURES:
//   - Configurable clock frequency and timing parameters
//   - Protocol compliance checking controls
//   - Statistics collection enable/disable
//   - Helper functions for common configurations
//
// AUTHOR: UCIe Sideband UVM Agent
// VERSION: 1.0
//=============================================================================

class ucie_sb_driver_config extends uvm_object;
  `uvm_object_utils(ucie_sb_driver_config)
  
  //=============================================================================
  // CONFIGURATION FIELDS
  //=============================================================================
  
  // Clock timing parameters
  real clock_period = 1.25;       // ns (800MHz default)
  real clock_high_time = 0.625;   // ns (50% duty cycle)
  real clock_low_time = 0.625;    // ns (50% duty cycle)
  
  // Protocol parameters
  int min_gap_cycles = 32;        // Minimum gap between packets
  bit enable_protocol_checking = 1;
  bit enable_statistics = 1;
  
  // Timing parameters
  real setup_time = 0.1;          // ns - data setup time before clock edge
  real hold_time = 0.1;           // ns - data hold time after clock edge
  real gap_time = 0.0;            // ns - additional time during gaps
  
  //=============================================================================
  // CONSTRUCTOR
  //=============================================================================
  
  //-----------------------------------------------------------------------------
  // FUNCTION: new
  // Creates a new driver configuration object with default 800MHz settings
  //
  // PARAMETERS:
  //   name - Object name for UVM hierarchy
  //-----------------------------------------------------------------------------
  function new(string name = "ucie_sb_driver_config");
    super.new(name);
  endfunction
  
  //=============================================================================
  // EXTERN FUNCTION DECLARATIONS
  //=============================================================================
  
  //-----------------------------------------------------------------------------
  // FUNCTION: set_frequency
  // Sets clock frequency and updates timing parameters accordingly
  //
  // PARAMETERS:
  //   freq_hz - Desired frequency in Hz (e.g., 800e6 for 800MHz)
  //-----------------------------------------------------------------------------
  extern function void set_frequency(real freq_hz);
  
  //-----------------------------------------------------------------------------
  // FUNCTION: set_duty_cycle
  // Sets clock duty cycle while maintaining same period
  //
  // PARAMETERS:
  //   duty_percent - Duty cycle percentage (e.g., 50.0 for 50%)
  //-----------------------------------------------------------------------------
  extern function void set_duty_cycle(real duty_percent);

endclass : ucie_sb_driver_config

//=============================================================================
// MAIN DRIVER CLASS
//=============================================================================

//=============================================================================
// CLASS: sideband_driver
//
// DESCRIPTION:
//   UCIe sideband driver that converts UVM transactions into source-synchronous
//   serial bit streams on the TX path. Supports 800MHz operation with proper
//   gap timing, parity calculation, and protocol validation according to
//   UCIe specification.
//
// FEATURES:
//   - Source-synchronous clock and data generation
//   - 800MHz default operation with configurable timing
//   - Automatic parity calculation and validation
//   - UCIe protocol compliance checking
//   - Statistics collection and reporting
//   - Support for header + data packet transmission
//   - Proper gap timing between packets
//
// AUTHOR: UCIe Sideband UVM Agent
// VERSION: 1.0
//=============================================================================

class ucie_sb_driver extends uvm_driver #(ucie_sb_transaction);
  `uvm_component_utils(ucie_sb_driver)
  
  //=============================================================================
  // CLASS FIELDS
  //=============================================================================
  
  // Configuration and interface
  virtual ucie_sb_interface vif;
  ucie_sb_driver_config cfg;
  
  // Parameters based on UCIe specification
  parameter int MIN_GAP_CYCLES = 32;
  parameter int PACKET_SIZE_BITS = 64;
  
  // Statistics
  int packets_driven = 0;
  int bits_driven = 0;
  int errors_detected = 0;
  time last_packet_time;
  
  //=============================================================================
  // CONSTRUCTOR
  //=============================================================================

  //-----------------------------------------------------------------------------
  // FUNCTION: new
  // Creates a new sideband driver component
  //
  // PARAMETERS:
  //   name   - Component name for UVM hierarchy
  //   parent - Parent component reference
  //-----------------------------------------------------------------------------
  function new(string name = "ucie_sb_driver", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  //=============================================================================
  // EXTERN FUNCTION/TASK DECLARATIONS
  //=============================================================================
  
  //-----------------------------------------------------------------------------
  // FUNCTION: build_phase
  // UVM build phase - gets interface and configuration
  //
  // PARAMETERS:
  //   phase - UVM phase object
  //-----------------------------------------------------------------------------
  extern virtual function void build_phase(uvm_phase phase);
  
  //-----------------------------------------------------------------------------
  // TASK: run_phase
  // UVM run phase - main driver loop for processing transactions
  //
  // PARAMETERS:
  //   phase - UVM phase object
  //-----------------------------------------------------------------------------
  extern virtual task run_phase(uvm_phase phase);
  
  //-----------------------------------------------------------------------------
  // FUNCTION: report_phase
  // UVM report phase - prints statistics if enabled
  //
  // PARAMETERS:
  //   phase - UVM phase object
  //-----------------------------------------------------------------------------
  extern virtual function void report_phase(uvm_phase phase);
  
  //-----------------------------------------------------------------------------
  // TASK: drive_transaction
  // Drives a complete transaction (header + optional data) with gaps
  //
  // PARAMETERS:
  //   trans - UCIe sideband transaction to drive
  //-----------------------------------------------------------------------------
  extern virtual task drive_transaction(ucie_sb_transaction trans);
  
  //-----------------------------------------------------------------------------
  // FUNCTION: drive_packet_with_clock
  // Drives a 64-bit packet with source-synchronous clock generation
  //
  // PARAMETERS:
  //   packet - 64-bit packet to transmit
  //
  // RETURNS: 1 if successful, 0 if failed
  //-----------------------------------------------------------------------------
  extern virtual function bit drive_packet_with_clock(bit [63:0] packet);
  
  //-----------------------------------------------------------------------------
  // TASK: drive_gap
  // Drives idle gap with both clock and data low
  //
  // PARAMETERS:
  //   num_cycles - Number of clock cycles for gap (default: MIN_GAP_CYCLES)
  //-----------------------------------------------------------------------------
  extern virtual task drive_gap(int num_cycles = MIN_GAP_CYCLES);
  
  //-----------------------------------------------------------------------------
  // TASK: wait_for_reset_release
  // Waits for reset to be deasserted before starting operation
  //-----------------------------------------------------------------------------
  extern virtual task wait_for_reset_release();
  
  //-----------------------------------------------------------------------------
  // FUNCTION: validate_transaction
  // Validates transaction against UCIe specification requirements
  //
  // PARAMETERS:
  //   trans - Transaction to validate
  //
  // RETURNS: 1 if valid, 0 if invalid
  //-----------------------------------------------------------------------------
  extern virtual function bit validate_transaction(ucie_sb_transaction trans);
  
  //-----------------------------------------------------------------------------
  // FUNCTION: get_tx_clk_state
  // Returns current state of TX clock signal
  //
  // RETURNS: Current SBTX_CLK value
  //-----------------------------------------------------------------------------
  extern virtual function bit get_tx_clk_state();
  
  //-----------------------------------------------------------------------------
  // FUNCTION: get_tx_data_state
  // Returns current state of TX data signal
  //
  // RETURNS: Current SBTX_DATA value
  //-----------------------------------------------------------------------------
  extern virtual function bit get_tx_data_state();
  
  //-----------------------------------------------------------------------------
  // TASK: drive_debug_pattern
  // Drives a debug pattern for testing purposes
  //
  // PARAMETERS:
  //   pattern - 64-bit debug pattern to drive
  //-----------------------------------------------------------------------------
  extern virtual task drive_debug_pattern(bit [63:0] pattern);
  
  //-----------------------------------------------------------------------------
  // FUNCTION: update_statistics
  // Updates driver statistics with transaction information
  //
  // PARAMETERS:
  //   trans - Transaction to include in statistics
  //-----------------------------------------------------------------------------
  extern virtual function void update_statistics(ucie_sb_transaction trans);
  
  //-----------------------------------------------------------------------------
  // FUNCTION: print_statistics
  // Prints current driver statistics to log
  //-----------------------------------------------------------------------------
  extern virtual function void print_statistics();

endclass : ucie_sb_driver

//=============================================================================
// CONFIGURATION CLASS IMPLEMENTATION
//=============================================================================

//-----------------------------------------------------------------------------
// FUNCTION: set_frequency
// Sets clock frequency and updates timing parameters accordingly
//-----------------------------------------------------------------------------
function void ucie_sb_driver_config::set_frequency(real freq_hz);
  clock_period = (1.0 / freq_hz) * 1e9; // Convert to ns
  clock_high_time = clock_period / 2.0;
  clock_low_time = clock_period / 2.0;
  `uvm_info("CONFIG", $sformatf("Set frequency to %.1f MHz (period=%.3f ns)", freq_hz/1e6, clock_period), UVM_LOW)
endfunction

//-----------------------------------------------------------------------------
// FUNCTION: set_duty_cycle
// Sets clock duty cycle while maintaining same period
//-----------------------------------------------------------------------------
function void ucie_sb_driver_config::set_duty_cycle(real duty_percent);
  clock_high_time = clock_period * (duty_percent / 100.0);
  clock_low_time = clock_period - clock_high_time;
endfunction

//=============================================================================
// DRIVER CLASS IMPLEMENTATION
//=============================================================================

//-----------------------------------------------------------------------------
// FUNCTION: build_phase
// UVM build phase - gets interface and configuration
//-----------------------------------------------------------------------------
virtual function void ucie_sb_driver::build_phase(uvm_phase phase);
  super.build_phase(phase);
  
  // Get virtual interface
  if (!uvm_config_db#(virtual ucie_sb_interface)::get(this, "", "vif", vif))
    `uvm_fatal("DRIVER", "Virtual interface not found")
  
  // Get configuration or create default
  if (!uvm_config_db#(ucie_sb_driver_config)::get(this, "", "cfg", cfg)) begin
    cfg = ucie_sb_driver_config::type_id::create("cfg");
    `uvm_info("DRIVER", "Using default driver configuration", UVM_MEDIUM)
  end
  
  // Validate configuration
  if (cfg.min_gap_cycles < 32) begin
    `uvm_warning("DRIVER", $sformatf("min_gap_cycles=%0d is less than UCIe minimum of 32", cfg.min_gap_cycles))
    cfg.min_gap_cycles = 32;
  end
  
  `uvm_info("DRIVER", $sformatf("Driver configured: %.1f MHz, %0d gap cycles", 
            1000.0/cfg.clock_period, cfg.min_gap_cycles), UVM_LOW)
endfunction

//-----------------------------------------------------------------------------
// TASK: run_phase
// UVM run phase - main driver loop for processing transactions
//-----------------------------------------------------------------------------
virtual task ucie_sb_driver::run_phase(uvm_phase phase);
  ucie_sb_transaction trans;
  
  `uvm_info("DRIVER", "Starting sideband driver run phase", UVM_LOW)
  
  // Wait for reset to be released
  wait_for_reset_release();
  
  // Initialize TX signals to idle state
  vif.SBTX_CLK = 0;
  vif.SBTX_DATA = 0;
  
  `uvm_info("DRIVER", "Sideband driver ready - clock and data will be generated per transaction", UVM_LOW)
  
  forever begin
    // Get next transaction from sequencer
    seq_item_port.get_next_item(trans);
    
    // Validate transaction before driving
    if (validate_transaction(trans)) begin
      drive_transaction(trans);
      update_statistics(trans);
    end else begin
      `uvm_error("DRIVER", {"Invalid transaction: ", trans.convert2string()})
      errors_detected++;
    end
    
    // Signal completion to sequencer
    seq_item_port.item_done();
  end
endtask

//-----------------------------------------------------------------------------
// FUNCTION: report_phase
// UVM report phase - prints statistics if enabled
//-----------------------------------------------------------------------------
virtual function void ucie_sb_driver::report_phase(uvm_phase phase);
  super.report_phase(phase);
  if (cfg.enable_statistics) begin
    print_statistics();
  end
endfunction

//-----------------------------------------------------------------------------
// TASK: drive_transaction
// Drives a complete transaction (header + optional data) with gaps
//-----------------------------------------------------------------------------
virtual task ucie_sb_driver::drive_transaction(ucie_sb_transaction trans);
  bit [63:0] header_packet;
  bit [63:0] data_packet;
  
  if (vif.sb_reset) begin
    `uvm_warning("DRIVER", "Cannot drive transaction during reset")
    return;
  end
  
  `uvm_info("DRIVER", {"Driving transaction: ", trans.convert2string()}, UVM_MEDIUM)
  
  // Calculate and set parity bits
  trans.calculate_parity();
  
  // Pack transaction header into 64-bit packet
  header_packet = trans.get_header();
  
  // Drive the header packet with source-synchronous clock
  if (drive_packet_with_clock(header_packet)) begin
    last_packet_time = $time;
    `uvm_info("DRIVER", $sformatf("Successfully drove header packet: 0x%016h", header_packet), UVM_HIGH)
  end else begin
    `uvm_error("DRIVER", "Failed to drive header packet")
    errors_detected++;
    return;
  end
  
  // Drive gap after header
  drive_gap();
  
  // Drive data packet if transaction has data
  if (trans.has_data) begin
    // Pack data according to transaction width
    if (trans.is_64bit) begin
      data_packet = trans.data;
    end else begin
      // For 32-bit data, pad MSBs with 0
      data_packet = {32'h0, trans.data[31:0]};
    end
    
    `uvm_info("DRIVER", $sformatf("Driving data packet: 0x%016h", data_packet), UVM_HIGH)
    
    // Drive the data packet
    if (drive_packet_with_clock(data_packet)) begin
      `uvm_info("DRIVER", "Successfully drove data packet", UVM_HIGH)
    end else begin
      `uvm_error("DRIVER", "Failed to drive data packet")
      errors_detected++;
      return;
    end
    
    // Drive gap after data
    drive_gap();
  end
endtask

//-----------------------------------------------------------------------------
// FUNCTION: drive_packet_with_clock
// Drives a 64-bit packet with source-synchronous clock generation
//-----------------------------------------------------------------------------
virtual function bit ucie_sb_driver::drive_packet_with_clock(bit [63:0] packet);
  if (vif.sb_reset) begin
    `uvm_warning("DRIVER", "Cannot drive packet during reset")
    return 0;
  end
  
  `uvm_info("DRIVER", $sformatf("Driving 64-bit packet with clock: 0x%016h", packet), UVM_HIGH)
  
  // Drive each bit with source-synchronous clock
  for (int i = 0; i < PACKET_SIZE_BITS; i++) begin
    // Clock low phase
    vif.SBTX_CLK = 1'b0;
    #(cfg.clock_low_time * 1ns);
    
    // Drive data at positive edge of clock
    vif.SBTX_DATA = packet[i];
    vif.SBTX_CLK = 1'b1;
    #(cfg.clock_high_time * 1ns);
  end
  
  // Return clock to idle (low) state
  vif.SBTX_CLK = 1'b0;
  
  return 1;
endfunction

//-----------------------------------------------------------------------------
// TASK: drive_gap
// Drives idle gap with both clock and data low
//-----------------------------------------------------------------------------
virtual task ucie_sb_driver::drive_gap(int num_cycles = MIN_GAP_CYCLES);
  `uvm_info("DRIVER", $sformatf("Driving %0d cycle gap (clock and data low)", num_cycles), UVM_DEBUG)
  
  // During gap: both clock and data are low
  vif.SBTX_CLK = 1'b0;
  vif.SBTX_DATA = 1'b0;
  
  // Hold for the gap duration (minimum 32 clock periods)
  #(num_cycles * cfg.clock_period * 1ns + cfg.gap_time * 1ns);
endtask

//-----------------------------------------------------------------------------
// TASK: wait_for_reset_release
// Waits for reset to be deasserted before starting operation
//-----------------------------------------------------------------------------
virtual task ucie_sb_driver::wait_for_reset_release();
  if (vif.sb_reset) begin
    `uvm_info("DRIVER", "Waiting for reset release...", UVM_MEDIUM)
    wait (!vif.sb_reset);
    `uvm_info("DRIVER", "Reset released", UVM_MEDIUM)
    
    // Small delay after reset release
    #(cfg.clock_period * 10 * 1ns);
  end
endtask

//-----------------------------------------------------------------------------
// FUNCTION: validate_transaction
// Validates transaction against UCIe specification requirements
//-----------------------------------------------------------------------------
virtual function bit ucie_sb_driver::validate_transaction(ucie_sb_transaction trans);
  if (!cfg.enable_protocol_checking) return 1;
  
  // Basic validation checks
  if (trans == null) begin
    `uvm_error("DRIVER", "Transaction is null")
    return 0;
  end
  
  // UCIe specific validation
  if (trans.srcid == 3'b000) begin
    `uvm_error("DRIVER", "srcid=0 is reserved in UCIe specification")
    return 0;
  end
  
  // Address alignment check
  if (trans.is_64bit && (trans.addr[2:0] != 3'b000)) begin
    `uvm_error("DRIVER", $sformatf("64-bit transaction address 0x%06h not 64-bit aligned", trans.addr))
    return 0;
  end
  
  if (!trans.is_64bit && (trans.addr[1:0] != 2'b00)) begin
    `uvm_error("DRIVER", $sformatf("32-bit transaction address 0x%06h not 32-bit aligned", trans.addr))
    return 0;
  end
  
  // Byte enable validation for 32-bit transactions
  if (!trans.is_64bit && (trans.be[7:4] != 4'b0000)) begin
    `uvm_error("DRIVER", $sformatf("32-bit transaction has invalid BE[7:4]=0x%h (should be 0)", trans.be[7:4]))
    return 0;
  end
  
  return 1;
endfunction

//-----------------------------------------------------------------------------
// FUNCTION: get_tx_clk_state
// Returns current state of TX clock signal
//-----------------------------------------------------------------------------
virtual function bit ucie_sb_driver::get_tx_clk_state();
  return vif.SBTX_CLK;
endfunction

//-----------------------------------------------------------------------------
// FUNCTION: get_tx_data_state
// Returns current state of TX data signal
//-----------------------------------------------------------------------------
virtual function bit ucie_sb_driver::get_tx_data_state();
  return vif.SBTX_DATA;
endfunction

//-----------------------------------------------------------------------------
// TASK: drive_debug_pattern
// Drives a debug pattern for testing purposes
//-----------------------------------------------------------------------------
virtual task ucie_sb_driver::drive_debug_pattern(bit [63:0] pattern);
  `uvm_info("DRIVER", $sformatf("Driving debug pattern: 0x%016h", pattern), UVM_LOW)
  drive_packet_with_clock(pattern);
  drive_gap();
endtask

//-----------------------------------------------------------------------------
// FUNCTION: update_statistics
// Updates driver statistics with transaction information
//-----------------------------------------------------------------------------
virtual function void ucie_sb_driver::update_statistics(ucie_sb_transaction trans);
  if (!cfg.enable_statistics) return;
  
  packets_driven++;
  bits_driven += PACKET_SIZE_BITS;
  
  if (trans.has_data) begin
    bits_driven += PACKET_SIZE_BITS; // Data packet
  end
  
  `uvm_info("DRIVER", $sformatf("Statistics: %0d packets, %0d bits driven", 
            packets_driven, bits_driven), UVM_DEBUG)
endfunction

//-----------------------------------------------------------------------------
// FUNCTION: print_statistics
// Prints current driver statistics to log
//-----------------------------------------------------------------------------
virtual function void ucie_sb_driver::print_statistics();
  `uvm_info("DRIVER", "=== Driver Statistics ===", UVM_LOW)
  `uvm_info("DRIVER", $sformatf("Packets driven: %0d", packets_driven), UVM_LOW)
  `uvm_info("DRIVER", $sformatf("Bits driven: %0d", bits_driven), UVM_LOW)
  `uvm_info("DRIVER", $sformatf("Errors detected: %0d", errors_detected), UVM_LOW)
  if (packets_driven > 0) begin
    `uvm_info("DRIVER", $sformatf("Average bits per packet: %.1f", real'(bits_driven)/real'(packets_driven)), UVM_LOW)
  end
  `uvm_info("DRIVER", "========================", UVM_LOW)
endfunction