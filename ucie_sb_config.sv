/*******************************************************************************
 * UCIe Sideband Protocol Configuration
 * 
 * OVERVIEW:
 *   Configuration class for UCIe (Universal Chiplet Interconnect Express)
 *   sideband protocol components. Provides comprehensive parameter control
 *   for initial flow, timing, link training, and protocol behavior.
 *
 * CONFIGURATION DOMAINS:
 *   • Basic sideband parameters (source/destination IDs)
 *   • Initial flow configuration (clock patterns, SBINIT messages)
 *   • Timing parameters (timeouts, periods, frequencies)
 *   • Protocol behavior controls (enable/disable features)
 *   • Link parameter training settings
 *
 * USAGE PATTERNS:
 *   • Agent configuration inheritance and distribution
 *   • Driver timing parameter customization
 *   • Protocol compliance feature control
 *   • Test-specific behavior modification
 *
 * COMPLIANCE:
 *   • IEEE 1800-2017 SystemVerilog
 *   • UVM 1.2 methodology
 *   • UCIe 1.1 specification
 *
 * AUTHOR: UCIe Sideband UVM Agent
 * VERSION: 3.0 - Production-grade configuration
 ******************************************************************************/

class ucie_sb_config extends uvm_object;
  `uvm_object_utils(ucie_sb_config)
  
  //=============================================================================
  // CONFIGURATION FIELDS
  //=============================================================================
  
  // Basic sideband parameters
  rand bit [2:0] srcid = 3'h1;           // Source ID
  rand bit [2:0] dstid = 3'h2;           // Destination ID
  
  // Initial flow configuration
  bit enable_initial_flow = 1;            // Enable initial flow
  bit enable_clock_pattern = 1;           // Enable clock pattern phase
  bit enable_sbinit_messages = 1;         // Enable SBINIT message phase
  
  // Timing parameters
  real timeout_8ms = 8_000_000.0;         // 8ms timeout in ns
  real clock_pattern_period = 1250.0;     // 800MHz period in ns (1.25ns)
  real sbinit_message_period = 1000.0;    // SBINIT message period in ns (1us)
  
  // Clock pattern configuration
  int remaining_clock_patterns = 4;       // Patterns to send after detection
  int required_pattern_detections = 2;    // Back-to-back patterns required
  // DEPRECATED: Custom pattern fields (now using UCIe standard CLOCK_PATTERN opcode)
  bit [31:0] clock_pattern_data = 32'h55555555; // DEPRECATED: Use CLOCK_PATTERN opcode instead
  bit [23:0] clock_pattern_addr = 24'hAAAAAA;   // DEPRECATED: Use CLOCK_PATTERN opcode instead
  
  // SBINIT message configuration
  bit [4:0] sbinit_oor_tag = 5'h10;      // SBINIT Out of Reset tag
  bit [4:0] sbinit_done_req_tag = 5'h11; // SBINIT Done Request tag
  bit [4:0] sbinit_done_rsp_tag = 5'h12; // SBINIT Done Response tag
  bit [23:0] sbinit_oor_addr = 24'h000010;     // SBINIT OOR address
  bit [23:0] sbinit_done_req_addr = 24'h000011; // SBINIT Done Req address
  bit [23:0] sbinit_done_rsp_addr = 24'h000012; // SBINIT Done Rsp address
  bit [3:0] sbinit_oor_result = 4'h1;    // SBINIT OOR result value
  
  // Training engine configuration
  bit enable_training_engine = 0;        // Enable training engine mode
  bit enable_register_access = 0;        // Enable register access training
  
  // Debug and monitoring
  bit enable_debug_logging = 1;          // Enable debug messages
  int verbosity_level = UVM_MEDIUM;      // Verbosity level
  bit enable_transaction_recording = 0;  // Enable transaction recording
  
  // Protocol configuration
  bit enable_tag_support = 1;            // Enable TAG support (from previous work)
  bit enable_timeout_checking = 1;       // Enable timeout checking
  bit enable_crc_checking = 0;           // Enable CRC checking (future)
  
  // Performance configuration
  int max_outstanding_transactions = 16; // Maximum outstanding transactions
  int fifo_depth = 64;                   // FIFO depth for buffering
  
  //=============================================================================
  // CONSTRAINTS
  //=============================================================================
  
  constraint valid_ids_c {
    srcid != dstid;                      // Source and destination must be different
    srcid inside {[0:7]};                // Valid 3-bit range
    dstid inside {[0:7]};                // Valid 3-bit range
  }
  
  constraint valid_timing_c {
    timeout_8ms >= 1_000_000.0;         // At least 1ms
    timeout_8ms <= 100_000_000.0;       // At most 100ms
    clock_pattern_period >= 500.0;      // At least 2GHz
    clock_pattern_period <= 5000.0;     // At most 200MHz
    sbinit_message_period >= 100.0;     // At least 10MHz
    sbinit_message_period <= 10000.0;   // At most 100KHz
  }
  
  constraint valid_patterns_c {
    remaining_clock_patterns inside {[1:8]};      // 1-8 patterns
    required_pattern_detections inside {[1:4]};   // 1-4 detections
  }
  
  //=============================================================================
  // CONSTRUCTOR
  //=============================================================================
  
  function new(string name = "ucie_sb_config");
    super.new(name);
  endfunction
  
  //=============================================================================
  // CONFIGURATION FUNCTIONS
  //=============================================================================
  
  // Set basic configuration for initial flow testing
  virtual function void configure_for_initial_flow_test();
    enable_initial_flow = 1;
    enable_clock_pattern = 1;
    enable_sbinit_messages = 1;
    timeout_8ms = 10_000_000.0;  // 10ms for faster testing
    enable_debug_logging = 1;
    verbosity_level = UVM_HIGH;
    
    `uvm_info("SB_CONFIG", "Configured for initial flow testing", UVM_LOW)
  endfunction
  
  // Set configuration for training engine mode
  virtual function void configure_for_training_engine();
    enable_initial_flow = 1;
    enable_training_engine = 1;
    enable_register_access = 1;
    enable_tag_support = 1;
    max_outstanding_transactions = 32;
    
    `uvm_info("SB_CONFIG", "Configured for training engine mode", UVM_LOW)
  endfunction
  
  // Set configuration for performance testing
  virtual function void configure_for_performance_test();
    timeout_8ms = 1_000_000.0;   // 1ms for fast testing
    clock_pattern_period = 625.0; // 1.6GHz for high performance
    sbinit_message_period = 100.0; // 10MHz message rate
    max_outstanding_transactions = 64;
    fifo_depth = 128;
    
    `uvm_info("SB_CONFIG", "Configured for performance testing", UVM_LOW)
  endfunction
  
  // Set debug configuration
  virtual function void configure_for_debug();
    enable_debug_logging = 1;
    verbosity_level = UVM_DEBUG;
    enable_transaction_recording = 1;
    
    `uvm_info("SB_CONFIG", "Configured for debug mode", UVM_LOW)
  endfunction
  
  //=============================================================================
  // VALIDATION FUNCTIONS
  //=============================================================================
  
  virtual function bit validate_config();
    bit valid = 1;
    
    // Check basic parameters
    if (srcid == dstid) begin
      `uvm_error("SB_CONFIG", "Source ID and Destination ID cannot be the same")
      valid = 0;
    end
    
    // Check timing parameters
    if (timeout_8ms < 1_000_000.0) begin
      `uvm_warning("SB_CONFIG", "Timeout less than 1ms may cause premature timeouts")
    end
    
    if (clock_pattern_period < 625.0) begin
      `uvm_warning("SB_CONFIG", "Clock pattern period less than 625ps (>1.6GHz) may be too fast")
    end
    
    // Check pattern parameters
    if (remaining_clock_patterns < 1) begin
      `uvm_error("SB_CONFIG", "Must send at least 1 remaining clock pattern")
      valid = 0;
    end
    
    if (required_pattern_detections < 1) begin
      `uvm_error("SB_CONFIG", "Must require at least 1 pattern detection")
      valid = 0;
    end
    
    return valid;
  endfunction
  
  //=============================================================================
  // UTILITY FUNCTIONS
  //=============================================================================
  
  virtual function void print_config();
    `uvm_info("SB_CONFIG", "=== Sideband Configuration ===", UVM_LOW)
    `uvm_info("SB_CONFIG", $sformatf("  Source ID: %0d", srcid), UVM_LOW)
    `uvm_info("SB_CONFIG", $sformatf("  Destination ID: %0d", dstid), UVM_LOW)
    `uvm_info("SB_CONFIG", $sformatf("  Initial Flow: %0b", enable_initial_flow), UVM_LOW)
    `uvm_info("SB_CONFIG", $sformatf("  Clock Pattern: %0b", enable_clock_pattern), UVM_LOW)
    `uvm_info("SB_CONFIG", $sformatf("  SBINIT Messages: %0b", enable_sbinit_messages), UVM_LOW)
    `uvm_info("SB_CONFIG", $sformatf("  Timeout: %.1f ns", timeout_8ms), UVM_LOW)
    `uvm_info("SB_CONFIG", $sformatf("  Clock Period: %.1f ns", clock_pattern_period), UVM_LOW)
    `uvm_info("SB_CONFIG", $sformatf("  Training Engine: %0b", enable_training_engine), UVM_LOW)
    `uvm_info("SB_CONFIG", $sformatf("  TAG Support: %0b", enable_tag_support), UVM_LOW)
    `uvm_info("SB_CONFIG", "==============================", UVM_LOW)
  endfunction
  
  virtual function ucie_sb_config copy_config();
    ucie_sb_config cfg_copy;
    cfg_copy = ucie_sb_config::type_id::create("cfg_copy");
    cfg_copy.copy(this);
    return cfg_copy;
  endfunction
  
  virtual function void randomize_config();
    if (!this.randomize()) begin
      `uvm_warning("SB_CONFIG", "Failed to randomize configuration")
    end else begin
      `uvm_info("SB_CONFIG", "Configuration randomized successfully", UVM_MEDIUM)
    end
  endfunction
  
  //=============================================================================
  // UVM OBJECT METHODS
  //=============================================================================
  
  virtual function void do_copy(uvm_object rhs);
    ucie_sb_config rhs_cfg;
    
    if (!$cast(rhs_cfg, rhs)) begin
      `uvm_fatal("SB_CONFIG", "Failed to cast rhs to ucie_sb_config")
    end
    
    super.do_copy(rhs);
    
    // Copy all fields
    this.srcid = rhs_cfg.srcid;
    this.dstid = rhs_cfg.dstid;
    this.enable_initial_flow = rhs_cfg.enable_initial_flow;
    this.enable_clock_pattern = rhs_cfg.enable_clock_pattern;
    this.enable_sbinit_messages = rhs_cfg.enable_sbinit_messages;
    this.timeout_8ms = rhs_cfg.timeout_8ms;
    this.clock_pattern_period = rhs_cfg.clock_pattern_period;
    this.sbinit_message_period = rhs_cfg.sbinit_message_period;
    this.remaining_clock_patterns = rhs_cfg.remaining_clock_patterns;
    this.required_pattern_detections = rhs_cfg.required_pattern_detections;
    this.clock_pattern_data = rhs_cfg.clock_pattern_data;
    this.clock_pattern_addr = rhs_cfg.clock_pattern_addr;
    this.enable_training_engine = rhs_cfg.enable_training_engine;
    this.enable_register_access = rhs_cfg.enable_register_access;
    this.enable_debug_logging = rhs_cfg.enable_debug_logging;
    this.verbosity_level = rhs_cfg.verbosity_level;
    this.enable_tag_support = rhs_cfg.enable_tag_support;
    this.max_outstanding_transactions = rhs_cfg.max_outstanding_transactions;
  endfunction
  
  virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
    ucie_sb_config rhs_cfg;
    bit result = 1;
    
    if (!$cast(rhs_cfg, rhs)) begin
      return 0;
    end
    
    result &= super.do_compare(rhs, comparer);
    result &= (this.srcid == rhs_cfg.srcid);
    result &= (this.dstid == rhs_cfg.dstid);
    result &= (this.enable_initial_flow == rhs_cfg.enable_initial_flow);
    result &= (this.timeout_8ms == rhs_cfg.timeout_8ms);
    result &= (this.enable_training_engine == rhs_cfg.enable_training_engine);
    
    return result;
  endfunction
  
  virtual function string convert2string();
    string s;
    s = $sformatf("ucie_sb_config: srcid=%0d dstid=%0d initial_flow=%0b training=%0b timeout=%.1fns", 
                  srcid, dstid, enable_initial_flow, enable_training_engine, timeout_8ms);
    return s;
  endfunction

endclass : ucie_sb_config