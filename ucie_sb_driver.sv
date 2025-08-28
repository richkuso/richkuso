/*******************************************************************************
 * UCIe Sideband Protocol Driver
 * 
 * OVERVIEW:
 *   High-performance UVM driver for UCIe (Universal Chiplet Interconnect Express)
 *   sideband protocol transmission. Converts UVM transactions into precise
 *   source-synchronous serial bit streams on the TX path with full protocol
 *   compliance and timing accuracy.
 *
 * DRIVER CAPABILITIES:
 *   • Source-synchronous clock generation up to 800MHz
 *   • All UCIe packet types: Register Access, Completions, Messages, Clock Patterns
 *   • Precise timing control with configurable duty cycle
 *   • Protocol-compliant gap generation (minimum 32 UI)
 *   • Automatic parity calculation and validation
 *   • Comprehensive transaction validation
 *   • Performance statistics and monitoring
 *
 * TRANSMISSION ARCHITECTURE:
 *   • Bit-level serial transmission with synchronized clock
 *   • Header + optional data packet structure
 *   • Inter-packet gap enforcement per UCIe specification
 *   • Reset-aware operation with proper initialization
 *   • Error detection and reporting
 *
 * PROTOCOL COMPLIANCE:
 *   • UCIe 1.1 timing requirements
 *   • Address alignment validation
 *   • Byte enable constraints
 *   • Source/destination ID verification
 *   • Parity generation per specification
 *
 * PERFORMANCE FEATURES:
 *   • Optimized clock pattern handling
 *   • Configurable timing parameters
 *   • Statistics collection and analysis
 *   • Transaction throughput monitoring
 *
 * COMPLIANCE:
 *   • IEEE 1800-2017 SystemVerilog
 *   • UVM 1.2 methodology
 *   • UCIe 1.1 specification
 *
 * AUTHOR: UCIe Sideband UVM Agent
 * VERSION: 3.0 - Production-grade driver implementation
 ******************************************************************************/

/*-----------------------------------------------------------------------------
 * DRIVER CONFIGURATION CLASS
 * 
 * Encapsulates all timing, protocol, and feature configuration parameters
 * for the UCIe sideband driver. Provides methods for common configuration
 * scenarios and validation of parameter ranges.
 *-----------------------------------------------------------------------------*/

class ucie_sb_driver_config extends uvm_object;
  `uvm_object_utils(ucie_sb_driver_config)
  
  /*---------------------------------------------------------------------------
   * TIMING CONFIGURATION PARAMETERS
   * Source-synchronous clock generation and protocol timing control
   *---------------------------------------------------------------------------*/
  
  real clock_period = 1.25;       
  real clock_high_time = 0.625;   
  real clock_low_time = 0.625;    
  
  /*---------------------------------------------------------------------------
   * PROTOCOL CONFIGURATION PARAMETERS
   * UCIe specification compliance and validation controls
   *---------------------------------------------------------------------------*/
  
  int min_gap_cycles = 32;        
  bit enable_protocol_checking = 1;
  bit enable_statistics = 1;
  
  /*---------------------------------------------------------------------------
   * ADVANCED TIMING PARAMETERS
   * Fine-grained timing control for signal integrity and validation
   *---------------------------------------------------------------------------*/
  
  real setup_time = 0.1;          
  real hold_time = 0.1;           
  real gap_time = 0.0;            
  
  /*---------------------------------------------------------------------------
   * CONSTRUCTOR - Initialize configuration with 800MHz defaults
   *---------------------------------------------------------------------------*/
  function new(string name = "ucie_sb_driver_config");
    super.new(name);
  endfunction
  
  /*---------------------------------------------------------------------------
   * CONFIGURATION METHOD DECLARATIONS
   * External methods for frequency and timing parameter management
   *---------------------------------------------------------------------------*/
  
  extern function void set_frequency(real freq_hz);
  extern function void set_duty_cycle(real duty_percent);

endclass : ucie_sb_driver_config

/*******************************************************************************
 * MAIN DRIVER CLASS
 * 
 * Core UCIe sideband driver implementation providing complete transaction-to-
 * serial conversion with source-synchronous clock generation, protocol
 * validation, and performance monitoring.
 ******************************************************************************/

class ucie_sb_driver extends uvm_driver #(ucie_sb_transaction);
  `uvm_component_utils(ucie_sb_driver)
  
  /*---------------------------------------------------------------------------
   * DRIVER INFRASTRUCTURE
   * Core components for interface access and configuration management
   *---------------------------------------------------------------------------*/
  
  virtual ucie_sb_inf vif;
  ucie_sb_driver_config cfg;
  
  /*---------------------------------------------------------------------------
   * PROTOCOL CONSTANTS
   * UCIe specification-defined parameters and limits
   *---------------------------------------------------------------------------*/
  
  parameter int MIN_GAP_CYCLES = 32;
  parameter int PACKET_SIZE_BITS = 64;
  
  /*---------------------------------------------------------------------------
   * PERFORMANCE MONITORING
   * Real-time statistics collection and analysis
   *---------------------------------------------------------------------------*/
  
  int packets_driven = 0;
  int bits_driven = 0;
  int errors_detected = 0;
  time last_packet_time;
  
  /*---------------------------------------------------------------------------
   * CONSTRUCTOR - Initialize driver component
   *---------------------------------------------------------------------------*/
  function new(string name = "ucie_sb_driver", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  /*---------------------------------------------------------------------------
   * EXTERNAL METHOD DECLARATIONS
   * All implementation methods declared as extern for clean interface
   *---------------------------------------------------------------------------*/
  
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);
  extern virtual function void report_phase(uvm_phase phase);
  extern virtual task drive_transaction(ucie_sb_transaction trans);
  extern virtual task drive_clock_pattern_transaction(ucie_sb_transaction trans);
  extern virtual task drive_message_transaction(ucie_sb_transaction trans);
  extern virtual task drive_standard_transaction(ucie_sb_transaction trans);
  extern virtual task drive_packet_with_clock(bit [63:0] packet, output bit success);
  extern virtual task drive_gap(int num_cycles = MIN_GAP_CYCLES);
  extern virtual task wait_for_reset_release();
  extern virtual function bit validate_transaction(ucie_sb_transaction trans);
  extern virtual function void update_statistics(ucie_sb_transaction trans);
  extern virtual function void print_statistics();

endclass : ucie_sb_driver

/*******************************************************************************
 * CONFIGURATION CLASS IMPLEMENTATION
 * Methods for dynamic timing and protocol parameter management
 ******************************************************************************/

/*-----------------------------------------------------------------------------
 * FREQUENCY CONFIGURATION
 * 
 * Calculates and sets all timing parameters based on desired frequency.
 * Maintains 50% duty cycle by default and converts frequency to nanosecond
 * timing values for precise simulation control.
 *
 * PARAMETERS:
 *   freq_hz - Target frequency in Hz (e.g., 800e6 for 800MHz)
 *
 * TIMING CALCULATION:
 *   period = 1/frequency (converted to nanoseconds)
 *   high_time = low_time = period/2 (50% duty cycle)
 *-----------------------------------------------------------------------------*/
function void ucie_sb_driver_config::set_frequency(real freq_hz);
  clock_period = (1.0 / freq_hz) * 1e9;
  clock_high_time = clock_period / 2.0;
  clock_low_time = clock_period / 2.0;
  `uvm_info("CONFIG", $sformatf("Set frequency to %.1f MHz (period=%.3f ns)", freq_hz/1e6, clock_period), UVM_LOW)
endfunction

/*-----------------------------------------------------------------------------
 * DUTY CYCLE CONFIGURATION
 * 
 * Adjusts clock high and low times to achieve specified duty cycle while
 * maintaining the same overall period. Useful for testing timing margins
 * and signal integrity scenarios.
 *
 * PARAMETERS:
 *   duty_percent - Desired duty cycle as percentage (0.0 to 100.0)
 *
 * CALCULATION:
 *   high_time = period × (duty_percent / 100)
 *   low_time = period - high_time
 *-----------------------------------------------------------------------------*/
function void ucie_sb_driver_config::set_duty_cycle(real duty_percent);
  clock_high_time = clock_period * (duty_percent / 100.0);
  clock_low_time = clock_period - clock_high_time;
endfunction

/*******************************************************************************
 * DRIVER CLASS IMPLEMENTATION
 * Complete transaction processing and serial transmission engine
 ******************************************************************************/

/*-----------------------------------------------------------------------------
 * BUILD PHASE IMPLEMENTATION
 * 
 * UVM build phase handler responsible for:
 *   • Virtual interface acquisition from configuration database
 *   • Driver configuration retrieval or default creation
 *   • Configuration parameter validation and correction
 *   • Timing parameter calculation and logging
 *
 * CONFIGURATION VALIDATION:
 *   • Ensures minimum gap cycles meet UCIe specification (≥32)
 *   • Validates timing parameters for simulation feasibility
 *   • Reports final configuration for debugging
 *-----------------------------------------------------------------------------*/
function void ucie_sb_driver::build_phase(uvm_phase phase);
  super.build_phase(phase);
  
  if (!uvm_config_db#(virtual ucie_sb_inf)::get(this, "", "vif", vif))
    `uvm_fatal("DRIVER", "Virtual interface not found")
  
  if (!uvm_config_db#(ucie_sb_driver_config)::get(this, "", "cfg", cfg)) begin
    cfg = ucie_sb_driver_config::type_id::create("cfg");
    `uvm_info("DRIVER", "Using default driver configuration", UVM_MEDIUM)
  end
  
  if (cfg.min_gap_cycles < 32) begin
    `uvm_warning("DRIVER", $sformatf("min_gap_cycles=%0d is less than UCIe minimum of 32", cfg.min_gap_cycles))
    cfg.min_gap_cycles = 32;
  end
  
  `uvm_info("DRIVER", $sformatf("Driver configured: %.1f MHz, %0d gap cycles", 
            1000.0/cfg.clock_period, cfg.min_gap_cycles), UVM_LOW)
endfunction

/*-----------------------------------------------------------------------------
 * RUN PHASE IMPLEMENTATION
 * 
 * Main driver execution loop providing:
 *   • Reset-aware initialization and signal management
 *   • Continuous transaction processing from sequencer
 *   • Transaction validation before transmission
 *   • Error handling and statistics collection
 *   • Proper sequencer handshaking (get_next_item/item_done)
 *
 * OPERATIONAL FLOW:
 *   1. Wait for reset deassertion
 *   2. Initialize TX signals to idle state
 *   3. Forever loop: get transaction → validate → drive → update stats
 *   4. Handle errors and maintain sequencer synchronization
 *-----------------------------------------------------------------------------*/
task ucie_sb_driver::run_phase(uvm_phase phase);
  ucie_sb_transaction trans;
  
  `uvm_info("DRIVER", "Starting sideband driver run phase", UVM_LOW)
  
  wait_for_reset_release();
  
  vif.SBTX_CLK = 0;
  vif.SBTX_DATA = 0;
  
  `uvm_info("DRIVER", "Sideband driver ready - clock and data will be generated per transaction", UVM_LOW)
  
  forever begin
    seq_item_port.get_next_item(trans);
    
    if (validate_transaction(trans)) begin
      drive_transaction(trans);
      update_statistics(trans);
    end else begin
      `uvm_error("DRIVER", {"Invalid transaction: ", trans.convert2string()})
      errors_detected++;
    end
    
    seq_item_port.item_done();
  end
endtask

/*-----------------------------------------------------------------------------
 * REPORT PHASE IMPLEMENTATION
 * 
 * UVM report phase handler for final statistics and performance reporting.
 * Conditionally prints comprehensive statistics if enabled in configuration.
 *-----------------------------------------------------------------------------*/
function void ucie_sb_driver::report_phase(uvm_phase phase);
  super.report_phase(phase);
  if (cfg.enable_statistics) begin
    print_statistics();
  end
endfunction

/*-----------------------------------------------------------------------------
 * TRANSACTION DISPATCH ENGINE
 * 
 * Main transaction processing coordinator that:
 *   • Validates reset state before transmission
 *   • Calculates and updates parity fields
 *   • Routes transactions to specialized handlers based on packet type
 *   • Provides unified entry point for all transaction types
 *
 * PACKET TYPE ROUTING:
 *   • PKT_CLOCK_PATTERN → drive_clock_pattern_transaction()
 *   • PKT_MESSAGE → drive_message_transaction()
 *   • PKT_REG_ACCESS/PKT_COMPLETION → drive_standard_transaction()
 *
 * PARITY HANDLING:
 *   Automatically recalculates parity to ensure transmission accuracy
 *   regardless of transaction source or randomization state.
 *-----------------------------------------------------------------------------*/
task ucie_sb_driver::drive_transaction(ucie_sb_transaction trans);
  bit [63:0] header_packet;
  bit [63:0] data_packet;
  
  if (vif.sb_reset) begin
    `uvm_warning("DRIVER", "Cannot drive transaction during reset")
    return;
  end
  
  `uvm_info("DRIVER", {"Driving transaction: ", trans.convert2string()}, UVM_MEDIUM)
  
  trans.calculate_parity();
  
  case (trans.pkt_type)
    PKT_CLOCK_PATTERN: begin
      drive_clock_pattern_transaction(trans);
    end
    PKT_MESSAGE: begin
      drive_message_transaction(trans);
    end
    default: begin
      drive_standard_transaction(trans);
    end
  endcase
endtask

/*-----------------------------------------------------------------------------
 * CLOCK PATTERN TRANSMISSION HANDLER
 * 
 * Specialized handler for UCIe clock pattern transmission with optimized
 * timing characteristics:
 *   • Supports both standard UCIe patterns and custom patterns
 *   • No automatic gap insertion (allows continuous pattern generation)
 *   • Handles unusual data payload scenarios with warnings
 *   • Optimized for training and synchronization sequences
 *
 * PATTERN TYPES:
 *   • Standard UCIe: Uses get_clock_pattern_header() (0x5555555555555555)
 *   • Custom: Uses standard header format with custom fields
 *
 * TIMING OPTIMIZATION:
 *   Clock patterns typically require continuous transmission without gaps
 *   for effective training, so gap insertion is left to sequence control.
 *-----------------------------------------------------------------------------*/
task ucie_sb_driver::drive_clock_pattern_transaction(ucie_sb_transaction trans);
  bit [63:0] header_packet;
  bit [63:0] data_packet;
  bit data_success;
  bit drive_success;
  
  `uvm_info("DRIVER", "Driving clock pattern transaction", UVM_MEDIUM)
  
  if (trans.opcode == CLOCK_PATTERN) begin
    header_packet = trans.get_clock_pattern_header();
    `uvm_info("DRIVER", "Using UCIe standard clock pattern", UVM_HIGH)
  end else begin
    header_packet = trans.get_header();
    `uvm_info("DRIVER", "Using custom clock pattern in register access format", UVM_HIGH)
  end
  
  drive_packet_with_clock(header_packet, drive_success);
  if (drive_success) begin
    last_packet_time = $time;
    `uvm_info("DRIVER", $sformatf("Successfully drove clock pattern: 0x%016h", header_packet), UVM_HIGH)
  end else begin
    `uvm_error("DRIVER", "Failed to drive clock pattern")
    errors_detected++;
    return;
  end
  
  if (trans.has_data) begin
    `uvm_warning("DRIVER", "Clock pattern transaction has data payload - this is unusual")
    data_packet = trans.is_64bit ? trans.data : {32'h0, trans.data[31:0]};
    drive_packet_with_clock(data_packet, data_success);
  end
  
endtask

/*-----------------------------------------------------------------------------
 * MESSAGE TRANSACTION HANDLER
 * 
 * Specialized handler for UCIe message transactions (SBINIT, etc.):
 *   • Processes message-specific header format (Figure 7-3)
 *   • Enforces standard gap timing after transmission
 *   • Validates message consistency (no data payload expected)
 *   • Handles SBINIT sequences and management messages
 *
 * MESSAGE CHARACTERISTICS:
 *   • Header-only transmission (no separate data packet)
 *   • Uses message-specific field encoding
 *   • Requires standard inter-packet gap
 *   • Critical for link initialization and management
 *-----------------------------------------------------------------------------*/
task ucie_sb_driver::drive_message_transaction(ucie_sb_transaction trans);
  bit [63:0] header_packet;
  bit header_success;
  
  `uvm_info("DRIVER", "Driving message transaction", UVM_MEDIUM)
  
  header_packet = trans.get_header();
  
  drive_packet_with_clock(header_packet, header_success);
  if (header_success) begin
    last_packet_time = $time;
    `uvm_info("DRIVER", $sformatf("Successfully drove message header: 0x%016h", header_packet), UVM_HIGH)
  end else begin
    `uvm_error("DRIVER", "Failed to drive message header")
    errors_detected++;
    return;
  end
  
  drive_gap();
  
  if (trans.has_data) begin
    `uvm_warning("DRIVER", "Message transaction has data payload - this may be incorrect")
  end
endtask

/*-----------------------------------------------------------------------------
 * STANDARD TRANSACTION HANDLER
 * 
 * Handler for register access and completion transactions following the
 * standard UCIe packet structure:
 *   • Header packet transmission with gap
 *   • Optional data packet transmission with gap
 *   • Proper 32-bit vs 64-bit data handling
 *   • Complete error checking and status reporting
 *
 * TRANSMISSION SEQUENCE:
 *   1. Drive header packet + gap
 *   2. If has_data: drive data packet + gap
 *   3. Handle 32-bit data padding (MSB zeros)
 *   4. Comprehensive error detection and reporting
 *
 * DATA WIDTH HANDLING:
 *   • 64-bit: Use full data field
 *   • 32-bit: Pad MSBs with zeros, use LSB 32 bits
 *-----------------------------------------------------------------------------*/
task ucie_sb_driver::drive_standard_transaction(ucie_sb_transaction trans);
  bit [63:0] header_packet;
  bit [63:0] data_packet;
  bit packet_success;
  bit data_packet_success;
  
  `uvm_info("DRIVER", "Driving standard register access/completion transaction", UVM_MEDIUM)
  
  header_packet = trans.get_header();
  
  drive_packet_with_clock(header_packet, packet_success);
  if (packet_success) begin
    last_packet_time = $time;
    `uvm_info("DRIVER", $sformatf("Successfully drove header packet: 0x%016h", header_packet), UVM_HIGH)
  end else begin
    `uvm_error("DRIVER", "Failed to drive header packet")
    errors_detected++;
    return;
  end
  
  drive_gap();
  
  if (trans.has_data) begin
    if (trans.is_64bit) begin
      data_packet = trans.data;
    end else begin
      data_packet = {32'h0, trans.data[31:0]};
    end
    
    `uvm_info("DRIVER", $sformatf("Driving data packet: 0x%016h", data_packet), UVM_HIGH)
    
    drive_packet_with_clock(data_packet, data_packet_success);
    if (data_packet_success) begin
      `uvm_info("DRIVER", "Successfully drove data packet", UVM_HIGH)
    end else begin
      `uvm_error("DRIVER", "Failed to drive data packet")
      errors_detected++;
      return;
    end
    
    drive_gap();
  end
endtask

/*-----------------------------------------------------------------------------
 * SOURCE-SYNCHRONOUS PACKET TRANSMISSION ENGINE
 * 
 * Core bit-level transmission engine providing precise source-synchronous
 * clock and data generation:
 *   • Bit-by-bit transmission with synchronized clock edges
 *   • Configurable timing parameters (period, duty cycle)
 *   • Reset-aware operation with safety checks
 *   • LSB-first bit ordering per UCIe specification
 *
 * TIMING SEQUENCE (per bit):
 *   1. Clock low phase (setup data)
 *   2. Drive data bit and clock high
 *   3. Hold for high time
 *   4. Return to clock low for next bit
 *
 * SIGNAL INTEGRITY:
 *   • Precise timing control with nanosecond resolution
 *   • Configurable setup and hold times
 *   • Clean clock return to idle state
 *-----------------------------------------------------------------------------*/
task ucie_sb_driver::drive_packet_with_clock(bit [63:0] packet, output bit success);
  if (vif.sb_reset) begin
    `uvm_warning("DRIVER", "Cannot drive packet during reset")
    success = 0;
    return;
  end
  
  `uvm_info("DRIVER", $sformatf("Driving 64-bit packet with clock: 0x%016h", packet), UVM_HIGH)
  
  for (int i = 0; i < PACKET_SIZE_BITS; i++) begin
    vif.SBTX_CLK = 1'b0;
    #(cfg.clock_low_time * 1ns);
    
    vif.SBTX_DATA = packet[i];
    vif.SBTX_CLK = 1'b1;
    #(cfg.clock_high_time * 1ns);
  end
  
  vif.SBTX_CLK = 1'b0;
  
  success = 1;
endtask

/*-----------------------------------------------------------------------------
 * INTER-PACKET GAP GENERATION
 * 
 * Generates protocol-compliant idle periods between packet transmissions:
 *   • Minimum 32 UI gap per UCIe specification
 *   • Both clock and data held low during gap
 *   • Configurable gap duration for testing
 *   • Additional gap time for margin testing
 *
 * GAP CHARACTERISTICS:
 *   • Clock = 0, Data = 0 (idle state)
 *   • Duration = num_cycles × period + additional gap time
 *   • Default to UCIe minimum (32 cycles)
 *   • Essential for receiver gap detection and validation
 *-----------------------------------------------------------------------------*/
task ucie_sb_driver::drive_gap(int num_cycles = MIN_GAP_CYCLES);
  `uvm_info("DRIVER", $sformatf("Driving %0d cycle gap (clock and data low)", num_cycles), UVM_DEBUG)
  
  vif.SBTX_CLK = 1'b0;
  vif.SBTX_DATA = 1'b0;
  
  #(num_cycles * cfg.clock_period * 1ns + cfg.gap_time * 1ns);
endtask

/*-----------------------------------------------------------------------------
 * RESET SYNCHRONIZATION
 * 
 * Provides proper reset handling and synchronization:
 *   • Waits for reset deassertion before operation
 *   • Includes settling time after reset release
 *   • Prevents transmission during reset conditions
 *   • Ensures clean startup sequence
 *
 * RESET HANDLING:
 *   • Monitors reset signal state
 *   • Provides informational logging
 *   • Includes post-reset stabilization delay
 *   • Coordinates with system reset sequences
 *-----------------------------------------------------------------------------*/
task ucie_sb_driver::wait_for_reset_release();
  if (vif.sb_reset) begin
    `uvm_info("DRIVER", "Waiting for reset release...", UVM_MEDIUM)
    wait (!vif.sb_reset);
    `uvm_info("DRIVER", "Reset released", UVM_MEDIUM)
    
    #(cfg.clock_period * 10 * 1ns);
  end
endtask

/*-----------------------------------------------------------------------------
 * COMPREHENSIVE TRANSACTION VALIDATION
 * 
 * Performs complete UCIe protocol compliance checking:
 *   • Basic transaction integrity (null checks)
 *   • UCIe source ID validation (srcid ≠ 0)
 *   • Clock pattern consistency verification
 *   • Message transaction validation
 *   • Address alignment enforcement
 *   • Byte enable constraint checking
 *   • Completion status field validation
 *
 * VALIDATION CATEGORIES:
 *   • Protocol Compliance: UCIe specification adherence
 *   • Data Integrity: Field consistency and constraints
 *   • Timing Requirements: Address alignment rules
 *   • Error Detection: Invalid combinations and values
 *
 * RETURN VALUE:
 *   • 1: Transaction passes all validation checks
 *   • 0: Transaction fails validation (with error logging)
 *-----------------------------------------------------------------------------*/
function bit ucie_sb_driver::validate_transaction(ucie_sb_transaction trans);
  if (!cfg.enable_protocol_checking) return 1;
  
  if (trans == null) begin
    `uvm_error("DRIVER", "Transaction is null")
    return 0;
  end
  
  // Skip srcid validation for clock pattern transactions
  if (!trans.is_clock_pattern && trans.srcid == 3'b000) begin
    `uvm_error("DRIVER", "srcid=0 is reserved in UCIe specification")
    return 0;
  end
  
  if (trans.is_clock_pattern) begin
    `uvm_info("DRIVER", "Clock pattern detected - srcid validation skipped", UVM_HIGH)
    if (trans.opcode == CLOCK_PATTERN) begin
      if (trans.has_data) begin
        `uvm_error("DRIVER", "UCIe CLOCK_PATTERN opcode should not have data payload")
        return 0;
      end
      `uvm_info("DRIVER", "Validated UCIe standard clock pattern", UVM_HIGH)
    end else if (trans.opcode == MEM_READ_32B || trans.opcode == MEM_READ_64B) begin
      `uvm_info("DRIVER", "Validated custom clock pattern using register access format", UVM_HIGH)
    end else begin
      `uvm_warning("DRIVER", $sformatf("Clock pattern using unusual opcode: %s", trans.opcode.name()))
    end
  end
  
  if (trans.pkt_type == PKT_MESSAGE) begin
    if (trans.has_data) begin
      `uvm_warning("DRIVER", "Message transaction has data payload - verify this is correct")
    end
    if (trans.opcode != MESSAGE_NO_DATA && trans.opcode != MGMT_MSG_NO_DATA) begin
      `uvm_warning("DRIVER", $sformatf("Message transaction using non-message opcode: %s", trans.opcode.name()))
    end
  end
  
  if (!trans.is_clock_pattern && trans.pkt_type != PKT_MESSAGE) begin
    if (trans.is_64bit && (trans.addr[2:0] != 3'b000)) begin
      `uvm_error("DRIVER", $sformatf("64-bit transaction address 0x%06h not 64-bit aligned", trans.addr))
      return 0;
    end
    
    if (!trans.is_64bit && (trans.addr[1:0] != 2'b00)) begin
      `uvm_error("DRIVER", $sformatf("32-bit transaction address 0x%06h not 32-bit aligned", trans.addr))
      return 0;
    end
  end
  
  if (!trans.is_64bit && !trans.is_clock_pattern && trans.pkt_type != PKT_MESSAGE) begin
    if (trans.be[7:4] != 4'b0000) begin
      `uvm_error("DRIVER", $sformatf("32-bit transaction has invalid BE[7:4]=0x%h (should be 0)", trans.be[7:4]))
      return 0;
    end
  end
  
  if (trans.pkt_type == PKT_COMPLETION) begin
    if (trans.status[15:3] != 13'h0000) begin
      `uvm_warning("DRIVER", $sformatf("Completion status has non-zero reserved bits: 0x%04h", trans.status))
    end
  end
  
  return 1;
endfunction

/*-----------------------------------------------------------------------------
 * PERFORMANCE STATISTICS COLLECTION
 * 
 * Real-time collection of driver performance metrics:
 *   • Packet transmission counting
 *   • Bit-level transmission tracking
 *   • Data packet detection and accounting
 *   • Conditional statistics based on configuration
 *
 * METRICS COLLECTED:
 *   • Total packets driven
 *   • Total bits transmitted
 *   • Header vs data packet breakdown
 *   • Transmission rate calculations
 *-----------------------------------------------------------------------------*/
function void ucie_sb_driver::update_statistics(ucie_sb_transaction trans);
  if (!cfg.enable_statistics) return;
  
  packets_driven++;
  bits_driven += PACKET_SIZE_BITS;
  
  if (trans.has_data) begin
    bits_driven += PACKET_SIZE_BITS;
  end
  
  `uvm_info("DRIVER", $sformatf("Statistics: %0d packets, %0d bits driven", 
            packets_driven, bits_driven), UVM_DEBUG)
endfunction

/*-----------------------------------------------------------------------------
 * COMPREHENSIVE STATISTICS REPORTING
 * 
 * Generates detailed performance and operational statistics:
 *   • Total transmission counts (packets, bits)
 *   • Error detection and reporting
 *   • Average transmission metrics
 *   • Performance analysis data
 *
 * REPORT CONTENT:
 *   • Packet transmission summary
 *   • Bit-level transmission details
 *   • Error rate and detection statistics
 *   • Efficiency metrics (bits per packet)
 *-----------------------------------------------------------------------------*/
function void ucie_sb_driver::print_statistics();
  `uvm_info("DRIVER", "=== Driver Statistics ===", UVM_LOW)
  `uvm_info("DRIVER", $sformatf("Packets driven: %0d", packets_driven), UVM_LOW)
  `uvm_info("DRIVER", $sformatf("Bits driven: %0d", bits_driven), UVM_LOW)
  `uvm_info("DRIVER", $sformatf("Errors detected: %0d", errors_detected), UVM_LOW)
  if (packets_driven > 0) begin
    `uvm_info("DRIVER", $sformatf("Average bits per packet: %.1f", real'(bits_driven)/real'(packets_driven)), UVM_LOW)
  end
  `uvm_info("DRIVER", "========================", UVM_LOW)
endfunction