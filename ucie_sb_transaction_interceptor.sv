/*******************************************************************************
 * UCIe Sideband Transaction Interceptor - FIFO-Based Architecture
 * 
 * OVERVIEW:
 *   FIFO-based UVM component for UCIe (Universal Chiplet Interconnect Express)
 *   sideband transaction interception using analysis ports and TLM FIFOs.
 *   Provides intelligent COMPLETION_32B interception based on matching CFG_READ
 *   transactions with sequencer-based output.
 *
 * ARCHITECTURE COMPONENTS:
 *   • SBTX Analysis Port: Receives TX transactions from sideband TX monitor
 *   • SBRX Analysis Port: Receives RX transactions from sideband RX monitor  
 *   • TX FIFO: Stores TX transactions for processing
 *   • RX FIFO: Stores RX transactions for processing
 *   • SBRX Sequencer: Outputs processed transactions to sideband RX driver
 *   • Stored Transaction: Latest matching CFG_READ for interception logic
 *
 * MAIN FUNCTIONS:
 *   1. Collect transactions from TX/RX analysis ports into FIFOs
 *   2. Process TX FIFO for CFG_READ address matching
 *   3. Process RX FIFO for COMPLETION_32B interception/bypass
 *   4. Send processed transactions to sequencer for driving
 *
 * INTERCEPTION LOGIC:
 *   • TX CFG_READ matches address → Store transaction, intercept next COMPLETION
 *   • TX CFG_READ no match → Pass through RX transactions directly
 *   • RX COMPLETION_32B + stored match → Revise data and update parity
 *   • All other RX transactions → Pass through to sequencer
 *
 * COMPLIANCE:
 *   • IEEE 1800-2017 SystemVerilog
 *   • UVM 1.2 methodology
 *   • UCIe 1.1 specification
 *
 * AUTHOR: UCIe Sideband UVM Agent
 * VERSION: 2.0 - FIFO-based interceptor architecture
 ******************************************************************************/

/*-----------------------------------------------------------------------------
 * FIFO-BASED INTERCEPTOR CONFIGURATION CLASS
 * 
 * Configuration management for FIFO-based transaction interception with
 * address matching criteria and completion revision parameters.
 *-----------------------------------------------------------------------------*/

class ucie_sb_interceptor_config extends uvm_object;
  `uvm_object_utils(ucie_sb_interceptor_config)
  
  /*---------------------------------------------------------------------------
   * OPERATIONAL MODE CONTROL
   * Interceptor behavior and component operation control
   *---------------------------------------------------------------------------*/
  
  bit enable_interception = 1;             // Enable transaction interception
  bit enable_debug = 1;                    // Enable debug messages
  bit enable_statistics = 1;               // Enable statistics collection
  bit pass_through_mode = 0;               // Pass-through mode (no interception)
  
  /*---------------------------------------------------------------------------
   * CFG_READ MATCHING CRITERIA
   * Address-based matching for CFG_READ transaction identification
   *---------------------------------------------------------------------------*/
  
  bit [23:0] cfg_read_addr_base = 24'h100000;  // Base address for CFG_READ matching
  bit [23:0] cfg_read_addr_mask = 24'hFFF000;  // Address mask (4KB blocks)
  bit enable_addr_match = 1;                   // Enable address matching
  
  /*---------------------------------------------------------------------------
   * COMPLETION REVISION PARAMETERS
   * Custom data and parity generation for intercepted completions
   *---------------------------------------------------------------------------*/
  
  bit [31:0] custom_completion_data = 32'hDEADBEEF; // Custom completion data
  bit [2:0] custom_completion_status = 3'b000;      // Success status
  bit generate_error_completion = 0;                // Generate error completions
  bit [2:0] error_status = 3'b001;                 // Error status code
  bit auto_update_parity = 1;                       // Automatically update parity
  
  /*---------------------------------------------------------------------------
   * FIFO CONFIGURATION PARAMETERS
   * FIFO sizing and timeout parameters
   *---------------------------------------------------------------------------*/
  
  int tx_fifo_size = 16;                   // TX FIFO depth
  int rx_fifo_size = 16;                   // RX FIFO depth
  real processing_delay_ns = 10.0;         // Processing delay between transactions
  
  /*---------------------------------------------------------------------------
   * CONSTRUCTOR - Initialize configuration with standard defaults
   *---------------------------------------------------------------------------*/
  function new(string name = "ucie_sb_interceptor_config");
    super.new(name);
  endfunction
  
  /*---------------------------------------------------------------------------
   * CONFIGURATION METHOD DECLARATIONS
   * External methods for configuration management
   *---------------------------------------------------------------------------*/
  
  extern function void set_cfg_read_address(bit [23:0] addr, bit [23:0] mask);
  extern function void set_custom_data(bit [31:0] data);
  extern function void set_fifo_sizes(int tx_size, int rx_size);
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
 * FIFO-BASED TRANSACTION INTERCEPTOR
 * 
 * Main interceptor component using FIFO-based architecture for transaction
 * collection, processing, and sequencer-based output with intelligent
 * COMPLETION_32B interception based on CFG_READ matching.
 ******************************************************************************/

class ucie_sb_transaction_interceptor extends uvm_component;
  `uvm_component_utils(ucie_sb_transaction_interceptor)
  
  /*---------------------------------------------------------------------------
   * ANALYSIS PORT INTERFACES
   * Input analysis ports for TX and RX transaction collection
   *---------------------------------------------------------------------------*/
  
  uvm_analysis_imp_sbtx #(ucie_sb_transaction, ucie_sb_transaction_interceptor) sbtx_ap;
  uvm_analysis_imp_sbrx #(ucie_sb_transaction, ucie_sb_transaction_interceptor) sbrx_ap;
  
  /*---------------------------------------------------------------------------
   * FIFO INFRASTRUCTURE
   * TLM FIFOs for transaction storage and processing
   *---------------------------------------------------------------------------*/
  
  uvm_tlm_fifo #(ucie_sb_transaction) tx_fifo;     // TX transaction FIFO
  uvm_tlm_fifo #(ucie_sb_transaction) rx_fifo;     // RX transaction FIFO
  
  /*---------------------------------------------------------------------------
   * SEQUENCER INTERFACE
   * Output sequencer for processed transaction driving
   *---------------------------------------------------------------------------*/
  
  ucie_sb_sequencer sbrx_sequencer;                // SBRX sequencer for output
  
  /*---------------------------------------------------------------------------
   * STORED TRANSACTION STATE
   * Latest matching CFG_READ transaction for interception logic
   *---------------------------------------------------------------------------*/
  
  ucie_sb_transaction stored_cfg_read;             // Stored CFG_READ transaction
  bit cfg_read_stored = 0;                         // Flag indicating stored CFG_READ
  
  /*---------------------------------------------------------------------------
   * CONFIGURATION AND CONNECTIVITY
   * Configuration management and analysis port connectivity
   *---------------------------------------------------------------------------*/
  
  ucie_sb_interceptor_config cfg;
  
  /*---------------------------------------------------------------------------
   * STATISTICS AND ANALYSIS INFRASTRUCTURE
   * Performance monitoring and interception statistics collection
   *---------------------------------------------------------------------------*/
  
  // Transaction counters
  int tx_transactions_received = 0;        // TX transactions received via AP
  int rx_transactions_received = 0;        // RX transactions received via AP
  int cfg_reads_matched = 0;               // CFG_READs that matched address
  int cfg_reads_ignored = 0;               // CFG_READs that didn't match
  int completions_intercepted = 0;         // COMPLETION_32B intercepted and revised
  int completions_bypassed = 0;            // COMPLETION_32B forwarded unchanged
  int other_transactions_bypassed = 0;     // All other transaction types bypassed
  
  // Performance metrics
  realtime total_processing_time = 0;      // Total processing time
  realtime max_processing_time = 0;        // Maximum processing time
  realtime min_processing_time = 0;        // Minimum processing time
  
  /*---------------------------------------------------------------------------
   * CONSTRUCTOR - Initialize FIFO interceptor component
   *---------------------------------------------------------------------------*/
  function new(string name = "ucie_sb_transaction_interceptor", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  /*---------------------------------------------------------------------------
   * EXTERNAL METHOD DECLARATIONS
   * All implementation methods declared as extern for clean interface
   *---------------------------------------------------------------------------*/
  
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);
  extern virtual function void report_phase(uvm_phase phase);
  extern virtual function void write_sbtx(ucie_sb_transaction trans);
  extern virtual function void write_sbrx(ucie_sb_transaction trans);
  extern virtual task process_transactions();
  extern virtual task process_tx_transaction(ucie_sb_transaction tx_trans);
  extern virtual task process_rx_transaction(ucie_sb_transaction rx_trans);
  extern virtual function bit cfg_read_matches_address(ucie_sb_transaction trans);
  extern virtual function ucie_sb_transaction revise_completion(ucie_sb_transaction completion);
  extern virtual task send_to_sequencer(ucie_sb_transaction trans);
  extern virtual function void set_default_config();
  extern virtual function void print_statistics();

endclass : ucie_sb_transaction_interceptor

/*******************************************************************************
 * CONFIGURATION CLASS IMPLEMENTATION
 ******************************************************************************/

/*---------------------------------------------------------------------------
 * SET CFG_READ ADDRESS CONFIGURATION
 * 
 * Configures address-based matching for CFG_READ transactions with
 * base address and mask parameters.
 *---------------------------------------------------------------------------*/
function void ucie_sb_interceptor_config::set_cfg_read_address(bit [23:0] addr, bit [23:0] mask);
  cfg_read_addr_base = addr;
  cfg_read_addr_mask = mask;
  enable_addr_match = 1;
  `uvm_info("FIFO_INTERCEPTOR_CONFIG", $sformatf("Set CFG_READ address: base=0x%06h, mask=0x%06h", 
            addr, mask), UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * SET CUSTOM COMPLETION DATA
 * 
 * Configures custom data value for intercepted completion responses.
 *---------------------------------------------------------------------------*/
function void ucie_sb_interceptor_config::set_custom_data(bit [31:0] data);
  custom_completion_data = data;
  `uvm_info("FIFO_INTERCEPTOR_CONFIG", $sformatf("Set custom completion data: 0x%08h", data), UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * SET FIFO SIZES
 * 
 * Configures TX and RX FIFO depths for transaction buffering.
 *---------------------------------------------------------------------------*/
function void ucie_sb_interceptor_config::set_fifo_sizes(int tx_size, int rx_size);
  tx_fifo_size = tx_size;
  rx_fifo_size = rx_size;
  `uvm_info("FIFO_INTERCEPTOR_CONFIG", $sformatf("Set FIFO sizes: TX=%0d, RX=%0d", tx_size, rx_size), UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * CONFIGURATION DEBUG REPORTING
 * 
 * Generates comprehensive configuration summary for debugging.
 *---------------------------------------------------------------------------*/
function void ucie_sb_interceptor_config::print_config();
  `uvm_info("FIFO_INTERCEPTOR_CONFIG", "=== FIFO Interceptor Configuration ===", UVM_LOW)
  `uvm_info("FIFO_INTERCEPTOR_CONFIG", $sformatf("Interception enabled: %0b", enable_interception), UVM_LOW)
  `uvm_info("FIFO_INTERCEPTOR_CONFIG", $sformatf("CFG_READ address: base=0x%06h, mask=0x%06h", 
            cfg_read_addr_base, cfg_read_addr_mask), UVM_LOW)
  `uvm_info("FIFO_INTERCEPTOR_CONFIG", $sformatf("Custom completion data: 0x%08h", custom_completion_data), UVM_LOW)
  `uvm_info("FIFO_INTERCEPTOR_CONFIG", $sformatf("FIFO sizes: TX=%0d, RX=%0d", tx_fifo_size, rx_fifo_size), UVM_LOW)
  `uvm_info("FIFO_INTERCEPTOR_CONFIG", "======================================", UVM_LOW)
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
 * Component construction and FIFO creation with configuration retrieval.
 *---------------------------------------------------------------------------*/
function void ucie_sb_transaction_interceptor::build_phase(uvm_phase phase);
  super.build_phase(phase);
  
  // Create analysis port implementations
  sbtx_ap = new("sbtx_ap", this);
  sbrx_ap = new("sbrx_ap", this);
  
  // Get interceptor configuration or create default
  if (!uvm_config_db#(ucie_sb_interceptor_config)::get(this, "", "cfg", cfg)) begin
    set_default_config();
  end
  
  // Create FIFOs with configured sizes
  tx_fifo = new("tx_fifo", this, cfg.tx_fifo_size);
  rx_fifo = new("rx_fifo", this, cfg.rx_fifo_size);
  
  // Create sequencer
  sbrx_sequencer = ucie_sb_sequencer::type_id::create("sbrx_sequencer", this);
  
  `uvm_info("FIFO_INTERCEPTOR", "FIFO interceptor build phase complete", UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * UVM CONNECT PHASE IMPLEMENTATION
 * 
 * Component connectivity establishment. Analysis ports are connected
 * externally by the testbench environment.
 *---------------------------------------------------------------------------*/
function void ucie_sb_transaction_interceptor::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  `uvm_info("FIFO_INTERCEPTOR", "FIFO interceptor connect phase complete", UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * UVM RUN PHASE IMPLEMENTATION
 * 
 * Main interceptor execution phase. Starts transaction processing task.
 *---------------------------------------------------------------------------*/
task ucie_sb_transaction_interceptor::run_phase(uvm_phase phase);
  super.run_phase(phase);
  
  `uvm_info("FIFO_INTERCEPTOR", "Starting FIFO interceptor run phase", UVM_LOW)
  
  // Start transaction processing
  process_transactions();
endtask

/*---------------------------------------------------------------------------
 * UVM REPORT PHASE IMPLEMENTATION
 * 
 * Final statistics and status reporting.
 *---------------------------------------------------------------------------*/
function void ucie_sb_transaction_interceptor::report_phase(uvm_phase phase);
  super.report_phase(phase);
  
  if (cfg.enable_statistics) begin
    print_statistics();
  end
endfunction

/*---------------------------------------------------------------------------
 * SBTX ANALYSIS PORT WRITE IMPLEMENTATION
 * 
 * Receives TX transactions from sideband TX monitor and pushes to TX FIFO.
 *---------------------------------------------------------------------------*/
function void ucie_sb_transaction_interceptor::write_sbtx(ucie_sb_transaction trans);
  tx_transactions_received++;
  
  if (cfg.enable_debug) begin
    `uvm_info("FIFO_INTERCEPTOR", $sformatf("Received TX transaction: opcode=%0d, addr=0x%06h, tag=%0d", 
              trans.opcode, trans.addr, trans.tag), UVM_HIGH)
  end
  
  // Push to TX FIFO
  if (!tx_fifo.try_put(trans)) begin
    `uvm_error("FIFO_INTERCEPTOR", "TX FIFO full - dropping transaction")
  end
endfunction

/*---------------------------------------------------------------------------
 * SBRX ANALYSIS PORT WRITE IMPLEMENTATION
 * 
 * Receives RX transactions from sideband RX monitor and pushes to RX FIFO.
 *---------------------------------------------------------------------------*/
function void ucie_sb_transaction_interceptor::write_sbrx(ucie_sb_transaction trans);
  rx_transactions_received++;
  
  if (cfg.enable_debug) begin
    `uvm_info("FIFO_INTERCEPTOR", $sformatf("Received RX transaction: opcode=%0d, tag=%0d, data=0x%08h", 
              trans.opcode, trans.tag, trans.data[31:0]), UVM_HIGH)
  end
  
  // Push to RX FIFO
  if (!rx_fifo.try_put(trans)) begin
    `uvm_error("FIFO_INTERCEPTOR", "RX FIFO full - dropping transaction")
  end
endfunction

/*---------------------------------------------------------------------------
 * MAIN TRANSACTION PROCESSING IMPLEMENTATION
 * 
 * Main processing loop that handles TX and RX FIFO processing according
 * to the interception logic specification.
 *---------------------------------------------------------------------------*/
task ucie_sb_transaction_interceptor::process_transactions();
  ucie_sb_transaction tx_trans, rx_trans;
  realtime start_time, process_time;
  
  forever begin
    // Get TX transaction from FIFO
    tx_fifo.get(tx_trans);
    start_time = $realtime;
    
    // Process TX transaction
    process_tx_transaction(tx_trans);
    
    // Get RX transaction from FIFO
    rx_fifo.get(rx_trans);
    
    // Process RX transaction based on TX processing result
    process_rx_transaction(rx_trans);
    
    // Update performance metrics
    process_time = $realtime - start_time;
    total_processing_time += process_time;
    if (process_time > max_processing_time) max_processing_time = process_time;
    if (min_processing_time == 0 || process_time < min_processing_time) min_processing_time = process_time;
    
    // Processing delay
    #(cfg.processing_delay_ns * 1ns);
  end
endtask

/*---------------------------------------------------------------------------
 * TX TRANSACTION PROCESSING IMPLEMENTATION
 * 
 * Processes TX transactions for CFG_READ address matching and storage.
 *---------------------------------------------------------------------------*/
task ucie_sb_transaction_interceptor::process_tx_transaction(ucie_sb_transaction tx_trans);
  if (tx_trans.opcode == CFG_READ_32B) begin
    if (cfg_read_matches_address(tx_trans)) begin
      // Store matching CFG_READ transaction
      stored_cfg_read = tx_trans.copy();
      cfg_read_stored = 1;
      cfg_reads_matched++;
      
      if (cfg.enable_debug) begin
        `uvm_info("FIFO_INTERCEPTOR", $sformatf("Stored CFG_READ: addr=0x%06h, tag=%0d", 
                  tx_trans.addr, tx_trans.tag), UVM_MEDIUM)
      end
    end else begin
      // Clear stored transaction for non-matching CFG_READ
      cfg_read_stored = 0;
      stored_cfg_read = null;
      cfg_reads_ignored++;
      
      if (cfg.enable_debug) begin
        `uvm_info("FIFO_INTERCEPTOR", $sformatf("Ignored CFG_READ: addr=0x%06h (no address match)", 
                  tx_trans.addr), UVM_HIGH)
      end
    end
  end else begin
    // For non-CFG_READ transactions, clear stored state
    cfg_read_stored = 0;
    stored_cfg_read = null;
  end
endtask

/*---------------------------------------------------------------------------
 * RX TRANSACTION PROCESSING IMPLEMENTATION
 * 
 * Processes RX transactions with interception/bypass logic based on
 * stored CFG_READ state and transaction type.
 *---------------------------------------------------------------------------*/
task ucie_sb_transaction_interceptor::process_rx_transaction(ucie_sb_transaction rx_trans);
  ucie_sb_transaction processed_trans;
  
  if (cfg_read_stored && rx_trans.opcode == COMPLETION_32B) begin
    // Check if COMPLETION matches stored CFG_READ
    if (rx_trans.tag == stored_cfg_read.tag && 
        rx_trans.srcid == stored_cfg_read.dstid) begin
      
      // INTERCEPT - Revise completion data and update parity
      processed_trans = revise_completion(rx_trans);
      send_to_sequencer(processed_trans);
      completions_intercepted++;
      
      if (cfg.enable_debug) begin
        `uvm_info("FIFO_INTERCEPTOR", $sformatf("Intercepted COMPLETION_32B: tag=%0d, revised data=0x%08h", 
                  rx_trans.tag, processed_trans.data[31:0]), UVM_MEDIUM)
      end
      
      // Clear stored CFG_READ after successful interception
      cfg_read_stored = 0;
      stored_cfg_read = null;
      
    end else begin
      // COMPLETION doesn't match - bypass
      send_to_sequencer(rx_trans);
      completions_bypassed++;
      
      if (cfg.enable_debug) begin
        `uvm_info("FIFO_INTERCEPTOR", $sformatf("Bypassed COMPLETION_32B: tag=%0d (no match)", rx_trans.tag), UVM_HIGH)
      end
    end
  end else begin
    // No stored CFG_READ or non-COMPLETION - bypass directly
    send_to_sequencer(rx_trans);
    
    if (rx_trans.opcode == COMPLETION_32B) begin
      completions_bypassed++;
    end else begin
      other_transactions_bypassed++;
    end
    
    if (cfg.enable_debug) begin
      `uvm_info("FIFO_INTERCEPTOR", $sformatf("Bypassed transaction: opcode=%0d", rx_trans.opcode), UVM_HIGH)
    end
  end
endtask

/*---------------------------------------------------------------------------
 * CFG_READ ADDRESS MATCHING IMPLEMENTATION
 * 
 * Checks if CFG_READ transaction matches the configured address criteria.
 *---------------------------------------------------------------------------*/
function bit ucie_sb_transaction_interceptor::cfg_read_matches_address(ucie_sb_transaction trans);
  if (!cfg.enable_addr_match) return 1;
  
  return ((trans.addr & cfg.cfg_read_addr_mask) == (cfg.cfg_read_addr_base & cfg.cfg_read_addr_mask));
endfunction

/*---------------------------------------------------------------------------
 * COMPLETION REVISION IMPLEMENTATION
 * 
 * Revises COMPLETION_32B transaction with custom data and updates parity.
 *---------------------------------------------------------------------------*/
function ucie_sb_transaction ucie_sb_transaction_interceptor::revise_completion(ucie_sb_transaction completion);
  ucie_sb_transaction revised;
  
  revised = completion.copy();  // Start with original completion
  
  // Apply custom modifications
  if (cfg.generate_error_completion) begin
    revised.status[2:0] = cfg.error_status;
    revised.data = 32'h0;                    // No data for error completions
  end else begin
    revised.status[2:0] = cfg.custom_completion_status;
    revised.data[31:0] = cfg.custom_completion_data;  // Custom data payload
  end
  
  // Update parity if enabled
  if (cfg.auto_update_parity) begin
    revised.update_packet_info();             // Recalculate parity and packet fields
  end
  
  return revised;
endfunction

/*---------------------------------------------------------------------------
 * SEQUENCER TRANSMISSION IMPLEMENTATION
 * 
 * Sends processed transaction to SBRX sequencer for driving.
 *---------------------------------------------------------------------------*/
task ucie_sb_transaction_interceptor::send_to_sequencer(ucie_sb_transaction trans);
  // Send transaction to sequencer
  sbrx_sequencer.send_request(trans);
  
  if (cfg.enable_debug) begin
    `uvm_info("FIFO_INTERCEPTOR", $sformatf("Sent to sequencer: opcode=%0d, tag=%0d, data=0x%08h", 
              trans.opcode, trans.tag, trans.data[31:0]), UVM_HIGH)
  end
endtask



/*---------------------------------------------------------------------------
 * DEFAULT CONFIGURATION SETUP IMPLEMENTATION
 * 
 * Creates default interceptor configuration when none provided.
 *---------------------------------------------------------------------------*/
function void ucie_sb_transaction_interceptor::set_default_config();
  cfg = ucie_sb_interceptor_config::type_id::create("cfg");
  cfg.set_cfg_read_address(24'h100000, 24'hFFF000);  // 4KB range at 1MB
  cfg.set_custom_data(32'hCAFEBABE);
  cfg.set_fifo_sizes(16, 16);
  `uvm_info("FIFO_INTERCEPTOR", "Using default FIFO interceptor configuration", UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * STATISTICS REPORTING IMPLEMENTATION
 * 
 * Generates comprehensive statistics report including transaction counts
 * and performance metrics.
 *---------------------------------------------------------------------------*/
function void ucie_sb_transaction_interceptor::print_statistics();
  real avg_processing_time;
  
  if ((cfg_reads_matched + cfg_reads_ignored + other_transactions_bypassed) > 0) begin
    avg_processing_time = total_processing_time / (cfg_reads_matched + cfg_reads_ignored + other_transactions_bypassed) / 1ns;
  end else begin
    avg_processing_time = 0.0;
  end
  
  `uvm_info("FIFO_INTERCEPTOR", "=== FIFO Interceptor Statistics ===", UVM_LOW)
  `uvm_info("FIFO_INTERCEPTOR", $sformatf("TX transactions received: %0d", tx_transactions_received), UVM_LOW)
  `uvm_info("FIFO_INTERCEPTOR", $sformatf("RX transactions received: %0d", rx_transactions_received), UVM_LOW)
  `uvm_info("FIFO_INTERCEPTOR", $sformatf("CFG_READs matched: %0d", cfg_reads_matched), UVM_LOW)
  `uvm_info("FIFO_INTERCEPTOR", $sformatf("CFG_READs ignored: %0d", cfg_reads_ignored), UVM_LOW)
  `uvm_info("FIFO_INTERCEPTOR", $sformatf("Completions intercepted: %0d", completions_intercepted), UVM_LOW)
  `uvm_info("FIFO_INTERCEPTOR", $sformatf("Completions bypassed: %0d", completions_bypassed), UVM_LOW)
  `uvm_info("FIFO_INTERCEPTOR", $sformatf("Other transactions bypassed: %0d", other_transactions_bypassed), UVM_LOW)
  `uvm_info("FIFO_INTERCEPTOR", $sformatf("CFG_READ currently stored: %0b", cfg_read_stored), UVM_LOW)
  `uvm_info("FIFO_INTERCEPTOR", $sformatf("Average processing time: %0.3f ns", avg_processing_time), UVM_LOW)
  `uvm_info("FIFO_INTERCEPTOR", $sformatf("Min/Max processing time: %0.3f/%0.3f ns", 
            min_processing_time/1ns, max_processing_time/1ns), UVM_LOW)
  `uvm_info("FIFO_INTERCEPTOR", "===================================", UVM_LOW)
endfunction