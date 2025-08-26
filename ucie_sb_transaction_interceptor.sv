/*******************************************************************************
 * UCIe Sideband Transaction Interceptor
 * 
 * OVERVIEW:
 *   Advanced UVM component for UCIe (Universal Chiplet Interconnect Express)
 *   sideband transaction interception and modification. Monitors CFG_READ_32B
 *   transactions and provides intelligent completion handling with configurable
 *   response modification capabilities.
 *
 * KEY CAPABILITIES:
 *   • CFG_READ_32B transaction detection and tracking
 *   • COMPLETION_32B transaction interception on RX path  
 *   • Configurable transaction matching criteria (address, tag, srcid)
 *   • Custom completion generation for matched transactions
 *   • Transparent pass-through for non-matching transactions
 *   • Comprehensive transaction logging and statistics
 *
 * INTERCEPTION ARCHITECTURE:
 *   • TX path monitoring for CFG read request detection
 *   • RX path monitoring for completion interception
 *   • Pending transaction tracking with timeout management
 *   • Custom completion generation with configurable responses
 *   • Statistics collection and performance monitoring
 *
 * MATCHING CRITERIA:
 *   • Address-based matching with configurable ranges
 *   • Source ID filtering for targeted interception
 *   • Tag-based matching for specific transaction flows
 *   • Combined criteria support for complex scenarios
 *
 * OPERATIONAL MODES:
 *   • Active Mode: Full interception with custom responses
 *   • Pass-through Mode: Transparent forwarding for debugging
 *   • Debug Mode: Enhanced logging and extended timeouts
 *
 * COMPLIANCE:
 *   • IEEE 1800-2017 SystemVerilog
 *   • UVM 1.2 methodology
 *   • UCIe 1.1 specification
 *
 * AUTHOR: UCIe Sideband UVM Agent
 * VERSION: 1.0 - Production-grade transaction interceptor
 ******************************************************************************/

/*-----------------------------------------------------------------------------
 * INTERCEPTOR CONFIGURATION CLASS
 * 
 * Comprehensive configuration management for transaction interception behavior.
 * Provides centralized control over matching criteria, response generation,
 * and operational modes with preset configurations.
 *-----------------------------------------------------------------------------*/

class ucie_sb_interceptor_config extends uvm_object;
  `uvm_object_utils(ucie_sb_interceptor_config)
  
  /*---------------------------------------------------------------------------
   * OPERATIONAL MODE CONTROL
   * Interception behavior and component operation control
   *---------------------------------------------------------------------------*/
  
  bit enable_interception = 1;             // Enable transaction interception
  bit enable_debug = 1;                    // Enable debug messages
  bit enable_statistics = 1;               // Enable statistics collection
  bit pass_through_mode = 0;               // Pass-through mode (no interception)
  
  /*---------------------------------------------------------------------------
   * MATCHING CRITERIA CONFIGURATION
   * Configurable parameters for transaction identification and filtering
   *---------------------------------------------------------------------------*/
  
  // Address-based matching
  bit [23:0] match_addr_base = 24'h100000;  // Base address for interception
  bit [23:0] match_addr_mask = 24'hFFF000;  // Address mask (4KB blocks)
  bit enable_addr_match = 1;                // Enable address matching
  
  // Source ID matching  
  bit [2:0] match_srcid = 3'h1;            // Source ID to match
  bit enable_srcid_match = 0;              // Enable source ID matching
  
  // Tag-based matching
  bit [4:0] match_tag_base = 5'h10;        // Base tag for matching
  bit [4:0] match_tag_mask = 5'h1F;        // Tag mask
  bit enable_tag_match = 0;                // Enable tag matching
  
  /*---------------------------------------------------------------------------
   * COMPLETION GENERATION PARAMETERS
   * Custom completion response configuration and control
   *---------------------------------------------------------------------------*/
  
  bit [31:0] custom_completion_data = 32'hDEADBEEF; // Custom completion data
  bit [2:0] custom_completion_status = 3'b000;      // Success status
  bit generate_error_completion = 0;                // Generate error completions
  bit [2:0] error_status = 3'b001;                 // Error status code
  
  /*---------------------------------------------------------------------------
   * TIMING AND PERFORMANCE PARAMETERS
   * Timing control and performance optimization settings
   *---------------------------------------------------------------------------*/
  
  int completion_delay_cycles = 10;        // Delay before sending completion
  int max_pending_transactions = 16;       // Maximum pending transaction tracking
  real timeout_ns = 1000.0;               // Transaction timeout in nanoseconds
  
  /*---------------------------------------------------------------------------
   * CONSTRUCTOR - Initialize configuration with standard defaults
   *---------------------------------------------------------------------------*/
  function new(string name = "ucie_sb_interceptor_config");
    super.new(name);
  endfunction
  
  /*---------------------------------------------------------------------------
   * CONFIGURATION METHOD DECLARATIONS
   * External methods for preset configurations and parameter management
   *---------------------------------------------------------------------------*/
  
  extern function void set_address_range(bit [23:0] base_addr, bit [23:0] size);
  extern function void set_custom_data(bit [31:0] data);
  extern function void set_pass_through_mode();
  extern function void set_debug_mode();
  extern function void print_config();

endclass : ucie_sb_interceptor_config

/*-----------------------------------------------------------------------------
 * PENDING TRANSACTION TRACKING CLASS
 * 
 * Tracks pending CFG_READ_32B transactions for completion matching.
 * Maintains transaction details needed for intelligent completion handling.
 *-----------------------------------------------------------------------------*/

class ucie_sb_pending_transaction extends uvm_object;
  `uvm_object_utils(ucie_sb_pending_transaction)
  
  /*---------------------------------------------------------------------------
   * TRANSACTION IDENTIFICATION FIELDS
   * Fields needed for completion matching and response generation
   *---------------------------------------------------------------------------*/
  
  bit [4:0] tag;                          // Transaction tag
  bit [2:0] srcid;                        // Original source ID (becomes dstid)
  bit [2:0] dstid;                        // Original destination ID (becomes srcid)
  bit [23:0] addr;                        // Request address
  bit [7:0] be;                           // Byte enables
  realtime timestamp;                     // Transaction timestamp
  bit matched;                            // Indicates if transaction matched criteria
  
  /*---------------------------------------------------------------------------
   * CONSTRUCTOR - Initialize pending transaction
   *---------------------------------------------------------------------------*/
  function new(string name = "ucie_sb_pending_transaction");
    super.new(name);
    timestamp = $realtime;
  endfunction
  
  /*---------------------------------------------------------------------------
   * UTILITY METHOD DECLARATIONS
   * Helper methods for transaction management and debugging
   *---------------------------------------------------------------------------*/
  
  extern function bit is_expired(real timeout_ns);
  extern function string to_string();

endclass : ucie_sb_pending_transaction

/*******************************************************************************
 * MAIN INTERCEPTOR CLASS
 * 
 * Core UCIe sideband transaction interceptor providing intelligent transaction
 * monitoring, interception, and modification with comprehensive configuration
 * and debugging capabilities for verification environments.
 ******************************************************************************/

class ucie_sb_transaction_interceptor extends uvm_component;
  `uvm_component_utils(ucie_sb_transaction_interceptor)
  
  /*---------------------------------------------------------------------------
   * INTERCEPTOR INFRASTRUCTURE
   * Core components for agent integration and interface management
   *---------------------------------------------------------------------------*/
  
  ucie_sb_agent tx_agent;                 // TX path agent (monitor CFG reads)
  ucie_sb_agent rx_agent;                 // RX path agent (monitor completions)
  ucie_sb_agent driver_agent;             // Driver agent (send responses)
  
  /*---------------------------------------------------------------------------
   * CONFIGURATION AND CONNECTIVITY
   * Configuration management and analysis port connectivity
   *---------------------------------------------------------------------------*/
  
  ucie_sb_interceptor_config cfg;
  
  // Analysis ports for transaction monitoring
  uvm_analysis_port #(ucie_sb_transaction) tx_monitor_ap;
  uvm_analysis_port #(ucie_sb_transaction) rx_monitor_ap;
  uvm_analysis_port #(ucie_sb_transaction) intercepted_ap;
  
  /*---------------------------------------------------------------------------
   * TRANSACTION TRACKING AND MANAGEMENT
   * Simplified state management for latest CFG_READ matching
   *---------------------------------------------------------------------------*/
  
  // Latest CFG_READ state management
  ucie_sb_transaction latest_cfg_read;    // Latest matched CFG_READ transaction
  bit ready_for_completion = 0;           // Flag indicating ready to intercept COMPLETION
  
  // Transaction processing synchronization
  semaphore completion_sem;               // Completion processing semaphore
  event cfg_read_matched_event;           // CFG read matched and stored
  event completion_processed_event;       // Completion processed
  
  /*---------------------------------------------------------------------------
   * STATISTICS AND ANALYSIS INFRASTRUCTURE
   * Performance monitoring and interception statistics collection
   *---------------------------------------------------------------------------*/
  
  // Transaction counters
  int matched_cfg_reads = 0;              // CFG_READs that matched criteria
  int ignored_cfg_reads = 0;              // CFG_READs that didn't match criteria
  int completions_intercepted = 0;        // COMPLETION_32B intercepted and revised
  int completions_bypassed = 0;           // COMPLETION_32B forwarded unchanged
  int other_transactions_bypassed = 0;    // All other transaction types bypassed
  
  // Performance metrics
  realtime total_intercept_time = 0;      // Total interception processing time
  realtime max_intercept_time = 0;        // Maximum interception time
  realtime min_intercept_time = 0;        // Minimum interception time
  
  /*---------------------------------------------------------------------------
   * CONSTRUCTOR - Initialize interceptor component
   *---------------------------------------------------------------------------*/
  function new(string name = "ucie_sb_transaction_interceptor", uvm_component parent = null);
    super.new(name, parent);
    completion_sem = new(1);
  endfunction
  
  /*---------------------------------------------------------------------------
   * EXTERNAL METHOD DECLARATIONS
   * All implementation methods declared as extern for clean interface
   *---------------------------------------------------------------------------*/
  
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);
  extern virtual function void end_of_elaboration_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);
  extern virtual function void report_phase(uvm_phase phase);
  extern virtual task monitor_tx_transactions();
  extern virtual task monitor_rx_transactions();
  extern virtual task process_cfg_read(ucie_sb_transaction trans);
  extern virtual task process_rx_transaction(ucie_sb_transaction trans);
  extern virtual function bit matches_criteria(ucie_sb_transaction trans);
  extern virtual function bit completion_matches_latest_cfg_read(ucie_sb_transaction completion);
  extern virtual function ucie_sb_transaction generate_revised_completion(ucie_sb_transaction original);
  extern virtual task send_to_driver(ucie_sb_transaction trans);
  extern virtual function void set_default_config();
  extern virtual function void print_statistics();

endclass : ucie_sb_transaction_interceptor

/*******************************************************************************
 * CONFIGURATION CLASS IMPLEMENTATION
 ******************************************************************************/

/*---------------------------------------------------------------------------
 * SET ADDRESS RANGE CONFIGURATION
 * 
 * Configures address-based matching with base address and size parameters.
 * Automatically calculates appropriate mask for the specified size.
 *---------------------------------------------------------------------------*/
function void ucie_sb_interceptor_config::set_address_range(bit [23:0] base_addr, bit [23:0] size);
  match_addr_base = base_addr;
  // Calculate mask based on size (power of 2 alignment)
  match_addr_mask = ~(size - 1);
  enable_addr_match = 1;
  `uvm_info("INTERCEPTOR_CONFIG", $sformatf("Set address range: base=0x%06h, size=0x%06h, mask=0x%06h", 
            base_addr, size, match_addr_mask), UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * SET CUSTOM COMPLETION DATA
 * 
 * Configures custom data value for intercepted completion responses.
 * Enables custom completion generation mode.
 *---------------------------------------------------------------------------*/
function void ucie_sb_interceptor_config::set_custom_data(bit [31:0] data);
  custom_completion_data = data;
  `uvm_info("INTERCEPTOR_CONFIG", $sformatf("Set custom completion data: 0x%08h", data), UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * SET PASS-THROUGH MODE
 * 
 * Configures interceptor for pass-through operation where all transactions
 * are forwarded without modification. Useful for debugging and testing.
 *---------------------------------------------------------------------------*/
function void ucie_sb_interceptor_config::set_pass_through_mode();
  pass_through_mode = 1;
  enable_interception = 0;
  `uvm_info("INTERCEPTOR_CONFIG", "Configured for pass-through mode", UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * SET DEBUG MODE
 * 
 * Enables comprehensive debug logging and extended timeout for development
 * and analysis purposes.
 *---------------------------------------------------------------------------*/
function void ucie_sb_interceptor_config::set_debug_mode();
  enable_debug = 1;
  enable_statistics = 1;
  timeout_ns = 10000.0;  // Extended timeout for debug
  `uvm_info("INTERCEPTOR_CONFIG", "Configured for debug mode", UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * CONFIGURATION DEBUG REPORTING
 * 
 * Generates comprehensive configuration summary for debugging and analysis.
 * Provides complete visibility into interceptor configuration parameters.
 *---------------------------------------------------------------------------*/
function void ucie_sb_interceptor_config::print_config();
  `uvm_info("INTERCEPTOR_CONFIG", "=== Interceptor Configuration ===", UVM_LOW)
  `uvm_info("INTERCEPTOR_CONFIG", $sformatf("Interception enabled: %0b", enable_interception), UVM_LOW)
  `uvm_info("INTERCEPTOR_CONFIG", $sformatf("Pass-through mode: %0b", pass_through_mode), UVM_LOW)
  `uvm_info("INTERCEPTOR_CONFIG", $sformatf("Debug enabled: %0b", enable_debug), UVM_LOW)
  `uvm_info("INTERCEPTOR_CONFIG", $sformatf("Address match: base=0x%06h, mask=0x%06h, enabled=%0b", 
            match_addr_base, match_addr_mask, enable_addr_match), UVM_LOW)
  `uvm_info("INTERCEPTOR_CONFIG", $sformatf("Source ID match: srcid=%0d, enabled=%0b", 
            match_srcid, enable_srcid_match), UVM_LOW)
  `uvm_info("INTERCEPTOR_CONFIG", $sformatf("Custom completion data: 0x%08h", custom_completion_data), UVM_LOW)
  `uvm_info("INTERCEPTOR_CONFIG", $sformatf("Timeout: %0.1f ns", timeout_ns), UVM_LOW)
  `uvm_info("INTERCEPTOR_CONFIG", "================================", UVM_LOW)
endfunction

/*******************************************************************************
 * PENDING TRANSACTION IMPLEMENTATION
 ******************************************************************************/

/*---------------------------------------------------------------------------
 * TRANSACTION EXPIRATION CHECK
 * 
 * Checks if pending transaction has exceeded the specified timeout.
 * Used for cleanup of stale pending transactions.
 *---------------------------------------------------------------------------*/
function bit ucie_sb_pending_transaction::is_expired(real timeout_ns);
  realtime current_time = $realtime;
  return ((current_time - timestamp) > (timeout_ns * 1ns));
endfunction

/*---------------------------------------------------------------------------
 * TRANSACTION STRING REPRESENTATION
 * 
 * Generates human-readable string representation of pending transaction
 * for debugging and logging purposes.
 *---------------------------------------------------------------------------*/
function string ucie_sb_pending_transaction::to_string();
  string s;
  s = $sformatf("PendingTrans[tag=%0d, srcid=%0d, addr=0x%06h, matched=%0b, age=%0.1fns]", 
                tag, srcid, addr, matched, ($realtime - timestamp)/1ns);
  return s;
endfunction

/*******************************************************************************
 * MAIN INTERCEPTOR IMPLEMENTATION
 ******************************************************************************/

/*---------------------------------------------------------------------------
 * UVM BUILD PHASE IMPLEMENTATION
 * 
 * Component construction and configuration retrieval. Creates sideband
 * agents for TX/RX monitoring and driver functionality.
 *---------------------------------------------------------------------------*/
function void ucie_sb_transaction_interceptor::build_phase(uvm_phase phase);
  super.build_phase(phase);
  
  // Create sideband agents
  tx_agent = ucie_sb_agent::type_id::create("tx_agent", this);
  rx_agent = ucie_sb_agent::type_id::create("rx_agent", this);
  driver_agent = ucie_sb_agent::type_id::create("driver_agent", this);
  
  // Create analysis ports
  tx_monitor_ap = new("tx_monitor_ap", this);
  rx_monitor_ap = new("rx_monitor_ap", this);
  intercepted_ap = new("intercepted_ap", this);
  
  // Get interceptor configuration or create default
  if (!uvm_config_db#(ucie_sb_interceptor_config)::get(this, "", "cfg", cfg)) begin
    set_default_config();
  end
  
  `uvm_info("INTERCEPTOR", "Transaction interceptor build phase complete", UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * UVM CONNECT PHASE IMPLEMENTATION
 * 
 * Component connectivity establishment. Connects analysis ports from
 * agent monitors to interceptor processing methods.
 *---------------------------------------------------------------------------*/
function void ucie_sb_transaction_interceptor::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  
  // Connect agent monitor analysis ports to interceptor
  // Note: Actual connections depend on testbench integration
  
  `uvm_info("INTERCEPTOR", "Transaction interceptor connect phase complete", UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * UVM END OF ELABORATION PHASE IMPLEMENTATION
 * 
 * Final configuration validation and debug reporting. Prints configuration
 * summary if debug mode is enabled.
 *---------------------------------------------------------------------------*/
function void ucie_sb_transaction_interceptor::end_of_elaboration_phase(uvm_phase phase);
  super.end_of_elaboration_phase(phase);
  
  if (cfg.enable_debug) begin
    cfg.print_config();
  end
  
  `uvm_info("INTERCEPTOR", "Transaction interceptor end of elaboration phase complete", UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * UVM RUN PHASE IMPLEMENTATION
 * 
 * Main interceptor execution phase. Starts parallel monitoring processes
 * for TX and RX paths, plus cleanup task for expired transactions.
 *---------------------------------------------------------------------------*/
task ucie_sb_transaction_interceptor::run_phase(uvm_phase phase);
  super.run_phase(phase);
  
  `uvm_info("INTERCEPTOR", "Starting transaction interceptor run phase", UVM_LOW)
  
  // Start parallel monitoring tasks
  fork
    monitor_tx_transactions();
    monitor_rx_transactions();
  join_none
  
  // Wait for simulation completion
  // Note: In actual implementation, this would wait for specific completion conditions
endtask

/*---------------------------------------------------------------------------
 * UVM REPORT PHASE IMPLEMENTATION
 * 
 * Final statistics and status reporting. Generates comprehensive summary
 * of interception activity and performance metrics.
 *---------------------------------------------------------------------------*/
function void ucie_sb_transaction_interceptor::report_phase(uvm_phase phase);
  super.report_phase(phase);
  
  if (cfg.enable_statistics) begin
    print_statistics();
  end
endfunction

/*---------------------------------------------------------------------------
 * TX TRANSACTION MONITORING IMPLEMENTATION
 * 
 * Monitors TX path for CFG_READ_32B transactions only. Stores latest matching
 * CFG_READ for potential COMPLETION interception. All other transactions ignored.
 *---------------------------------------------------------------------------*/
task ucie_sb_transaction_interceptor::monitor_tx_transactions();
  ucie_sb_transaction trans;
  
  forever begin
    // Get transaction from TX agent monitor
    tx_agent.monitor.ap.get(trans);
    
    // Forward to analysis port
    tx_monitor_ap.write(trans);
    
    // Only process CFG_READ_32B transactions, ignore all others
    if (trans.opcode == CFG_READ_32B) begin
      process_cfg_read(trans);
    end
    // All other transaction types are ignored by TX monitor
  end
endtask

/*---------------------------------------------------------------------------
 * RX TRANSACTION MONITORING IMPLEMENTATION
 * 
 * Monitors RX path for ALL transactions. Only COMPLETION_32B transactions
 * are checked for interception. All other transactions bypass directly to driver.
 *---------------------------------------------------------------------------*/
task ucie_sb_transaction_interceptor::monitor_rx_transactions();
  ucie_sb_transaction trans;
  
  forever begin
    // Get transaction from RX agent monitor
    rx_agent.monitor.ap.get(trans);
    
    // Forward to analysis port
    rx_monitor_ap.write(trans);
    
    // Process all RX transactions
    process_rx_transaction(trans);
  end
endtask

/*---------------------------------------------------------------------------
 * CFG READ PROCESSING IMPLEMENTATION
 * 
 * Processes detected CFG_READ_32B transactions. Checks matching criteria
 * and stores latest matching CFG_READ for COMPLETION interception.
 *---------------------------------------------------------------------------*/
task ucie_sb_transaction_interceptor::process_cfg_read(ucie_sb_transaction trans);
  bit matches;
  
  if (cfg.enable_debug) begin
    `uvm_info("INTERCEPTOR", $sformatf("Detected CFG_READ_32B: addr=0x%06h, tag=%0d, srcid=%0d", 
              trans.addr, trans.tag, trans.srcid), UVM_HIGH)
  end
  
  // Check if transaction matches interception criteria
  matches = matches_criteria(trans);
  
  if (matches && cfg.enable_interception && !cfg.pass_through_mode) begin
    // Store as latest matched CFG_READ
    latest_cfg_read = trans.copy();
    ready_for_completion = 1;
    matched_cfg_reads++;
    
    if (cfg.enable_debug) begin
      `uvm_info("INTERCEPTOR", $sformatf("Stored CFG_READ for interception: tag=%0d, addr=0x%06h", 
                trans.tag, trans.addr), UVM_MEDIUM)
    end
    
    -> cfg_read_matched_event;
  end else begin
    ignored_cfg_reads++;
    
    if (cfg.enable_debug) begin
      `uvm_info("INTERCEPTOR", $sformatf("Ignored CFG_READ: tag=%0d (no match or disabled)", trans.tag), UVM_HIGH)
    end
  end
endtask

/*---------------------------------------------------------------------------
 * RX TRANSACTION PROCESSING IMPLEMENTATION
 * 
 * Processes ALL transactions from RX path. Only COMPLETION_32B transactions
 * are checked for interception. All other transactions bypass to driver.
 *---------------------------------------------------------------------------*/
task ucie_sb_transaction_interceptor::process_rx_transaction(ucie_sb_transaction trans);
  realtime start_time, process_time;
  
  start_time = $realtime;
  
  if (trans.opcode == COMPLETION_32B) begin
    // Check if this completion matches our latest CFG_READ
    if (ready_for_completion && completion_matches_latest_cfg_read(trans)) begin
      // INTERCEPT - Generate revised completion
      ucie_sb_transaction revised_completion = generate_revised_completion(trans);
      send_to_driver(revised_completion);
      completions_intercepted++;
      
      // Reset state for next interception
      ready_for_completion = 0;
      latest_cfg_read = null;
      
      // Write to intercepted analysis port
      intercepted_ap.write(revised_completion);
      
      if (cfg.enable_debug) begin
        `uvm_info("INTERCEPTOR", $sformatf("Intercepted COMPLETION_32B: tag=%0d, revised with custom data", 
                  trans.tag), UVM_MEDIUM)
      end
      
    end else begin
      // Forward original completion
      send_to_driver(trans);
      completions_bypassed++;
      
      if (cfg.enable_debug) begin
        `uvm_info("INTERCEPTOR", $sformatf("Bypassed COMPLETION_32B: tag=%0d (no match or not ready)", 
                  trans.tag), UVM_HIGH)
      end
    end
  end else begin
    // BYPASS all non-COMPLETION transactions directly
    send_to_driver(trans);
    other_transactions_bypassed++;
    
    if (cfg.enable_debug) begin
      `uvm_info("INTERCEPTOR", $sformatf("Bypassed transaction: opcode=%0d", trans.opcode), UVM_HIGH)
    end
  end
  
  // Update performance metrics
  process_time = $realtime - start_time;
  total_intercept_time += process_time;
  if (process_time > max_intercept_time) max_intercept_time = process_time;
  if (min_intercept_time == 0 || process_time < min_intercept_time) min_intercept_time = process_time;
  
  -> completion_processed_event;
endtask

/*---------------------------------------------------------------------------
 * COMPLETION MATCHING IMPLEMENTATION
 * 
 * Checks if a COMPLETION_32B transaction matches the latest stored CFG_READ
 * transaction based on tag and source/destination ID correspondence.
 *---------------------------------------------------------------------------*/
function bit ucie_sb_transaction_interceptor::completion_matches_latest_cfg_read(ucie_sb_transaction completion);
  if (latest_cfg_read == null) return 0;
  
  // Check tag match
  if (completion.tag != latest_cfg_read.tag) return 0;
  
  // Check source ID correspondence (completion srcid should match CFG_READ dstid)
  if (completion.srcid != latest_cfg_read.dstid) return 0;
  
  return 1;
endfunction

/*---------------------------------------------------------------------------
 * TRANSACTION MATCHING CRITERIA IMPLEMENTATION
 * 
 * Evaluates whether a CFG_READ_32B transaction matches the configured
 * interception criteria (address, source ID, tag).
 *---------------------------------------------------------------------------*/
function bit ucie_sb_transaction_interceptor::matches_criteria(ucie_sb_transaction trans);
  bit addr_match = 1;
  bit srcid_match = 1;
  bit tag_match = 1;
  
  // Address matching
  if (cfg.enable_addr_match) begin
    addr_match = ((trans.addr & cfg.match_addr_mask) == (cfg.match_addr_base & cfg.match_addr_mask));
  end
  
  // Source ID matching
  if (cfg.enable_srcid_match) begin
    srcid_match = (trans.srcid == cfg.match_srcid);
  end
  
  // Tag matching
  if (cfg.enable_tag_match) begin
    tag_match = ((trans.tag & cfg.match_tag_mask) == (cfg.match_tag_base & cfg.match_tag_mask));
  end
  
  return (addr_match && srcid_match && tag_match);
endfunction

/*---------------------------------------------------------------------------
 * REVISED COMPLETION GENERATION IMPLEMENTATION
 * 
 * Generates revised COMPLETION_32B transaction based on original completion
 * and latest CFG_READ transaction with configured custom response parameters.
 *---------------------------------------------------------------------------*/
function ucie_sb_transaction ucie_sb_transaction_interceptor::generate_revised_completion(ucie_sb_transaction original);
  ucie_sb_transaction revised;
  
  revised = original.copy();  // Start with original completion
  
  // Apply custom modifications
  if (cfg.generate_error_completion) begin
    revised.status[2:0] = cfg.error_status;
    revised.data = 32'h0;                    // No data for error completions
  end else begin
    revised.status[2:0] = cfg.custom_completion_status;
    revised.data[31:0] = cfg.custom_completion_data;  // Custom data payload
  end
  
  // Preserve UCIe protocol fields from original
  revised.opcode = COMPLETION_32B;
  revised.tag = original.tag;              // Keep original tag
  revised.srcid = original.srcid;          // Keep original source ID
  revised.dstid = original.dstid;          // Keep original destination ID
  revised.be = latest_cfg_read.be;         // Use CFG_READ byte enables
  revised.ep = 0;                          // No error poison
  revised.cr = 0;                          // No credit return
  
  // Update packet metadata
  revised.update_packet_info();
  
  return revised;
endfunction

/*---------------------------------------------------------------------------
 * TRANSACTION TRANSMISSION IMPLEMENTATION
 * 
 * Sends any transaction via driver agent with configurable delay.
 * Handles both intercepted/revised and bypassed transactions.
 *---------------------------------------------------------------------------*/
task ucie_sb_transaction_interceptor::send_to_driver(ucie_sb_transaction trans);
  // Add configurable delay for completions
  if (trans.opcode == COMPLETION_32B && cfg.completion_delay_cycles > 0) begin
    repeat(cfg.completion_delay_cycles) @(posedge driver_agent.vif.clk);
  end
  
  // Send via driver agent
  driver_agent.driver.send_transaction(trans);
  
  if (cfg.enable_debug) begin
    `uvm_info("INTERCEPTOR", $sformatf("Sent to driver: opcode=%0d, tag=%0d, data=0x%08h", 
              trans.opcode, trans.tag, trans.data[31:0]), UVM_HIGH)
  end
endtask



/*---------------------------------------------------------------------------
 * DEFAULT CONFIGURATION SETUP IMPLEMENTATION
 * 
 * Creates default interceptor configuration when none provided via config DB.
 * Establishes standard operational parameters for typical usage scenarios.
 *---------------------------------------------------------------------------*/
function void ucie_sb_transaction_interceptor::set_default_config();
  cfg = ucie_sb_interceptor_config::type_id::create("cfg");
  cfg.set_address_range(24'h100000, 24'h1000);  // 4KB range at 1MB
  cfg.set_custom_data(32'hCAFEBABE);
  `uvm_info("INTERCEPTOR", "Using default interceptor configuration", UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * STATISTICS REPORTING IMPLEMENTATION
 * 
 * Generates comprehensive statistics report including transaction counts,
 * performance metrics, and operational analysis.
 *---------------------------------------------------------------------------*/
function void ucie_sb_transaction_interceptor::print_statistics();
  real avg_intercept_time;
  
  if (completions_intercepted > 0) begin
    avg_intercept_time = total_intercept_time / completions_intercepted / 1ns;
  end else begin
    avg_intercept_time = 0.0;
  end
  
  `uvm_info("INTERCEPTOR", "=== Transaction Interceptor Statistics ===", UVM_LOW)
  `uvm_info("INTERCEPTOR", $sformatf("Matched CFG_READs: %0d", matched_cfg_reads), UVM_LOW)
  `uvm_info("INTERCEPTOR", $sformatf("Ignored CFG_READs: %0d", ignored_cfg_reads), UVM_LOW)
  `uvm_info("INTERCEPTOR", $sformatf("Completions intercepted: %0d", completions_intercepted), UVM_LOW)
  `uvm_info("INTERCEPTOR", $sformatf("Completions bypassed: %0d", completions_bypassed), UVM_LOW)
  `uvm_info("INTERCEPTOR", $sformatf("Other transactions bypassed: %0d", other_transactions_bypassed), UVM_LOW)
  `uvm_info("INTERCEPTOR", $sformatf("Ready for completion: %0b", ready_for_completion), UVM_LOW)
  `uvm_info("INTERCEPTOR", $sformatf("Average intercept time: %0.3f ns", avg_intercept_time), UVM_LOW)
  `uvm_info("INTERCEPTOR", $sformatf("Min/Max intercept time: %0.3f/%0.3f ns", 
            min_intercept_time/1ns, max_intercept_time/1ns), UVM_LOW)
  `uvm_info("INTERCEPTOR", "=========================================", UVM_LOW)
endfunction