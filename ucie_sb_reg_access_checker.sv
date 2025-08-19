/*******************************************************************************
 * UCIe Sideband Register Access Protocol Checker
 * 
 * OVERVIEW:
 *   Advanced bidirectional protocol checker for UCIe (Universal Chiplet 
 *   Interconnect Express) sideband register access transactions. Provides
 *   comprehensive request-completion matching, timing analysis, and protocol
 *   compliance verification across both TX and RX paths.
 *
 * VERIFICATION ARCHITECTURE:
 *   • Bidirectional transaction flow monitoring (TX↔RX)
 *   • Tag-based request tracking with 32-entry capacity per direction
 *   • Non-TAG mode support with blocking behavior validation
 *   • Asynchronous FIFO-based processing for optimal performance
 *   • Real-time protocol compliance checking and error detection
 *
 * TRANSACTION FLOW COVERAGE:
 *   • TX→RX Flow: TX sends request, RX returns completion
 *   • RX→TX Flow: RX sends request, TX returns completion
 *   • Request Types: MEM/DMS/CFG operations (32-bit/64-bit)
 *   • Completion Types: No data, 32-bit data, 64-bit data
 *
 * PROTOCOL VALIDATION:
 *   • Source/destination ID swapping verification
 *   • Tag consistency and reuse detection
 *   • Data width matching between requests and completions
 *   • Timeout detection for missing completions
 *   • Protocol error counting and reporting
 *
 * PERFORMANCE ANALYSIS:
 *   • Response time statistics (min/max/average)
 *   • Transaction throughput monitoring
 *   • FIFO depth tracking and optimization
 *   • Bidirectional flow performance comparison
 *
 * OPERATIONAL MODES:
 *   • TAG Mode: Full 32-tag support with concurrent transactions
 *   • Non-TAG Mode: Single outstanding request with blocking validation
 *   • Configurable timeout monitoring and error handling
 *
 * INTEGRATION:
 *   • Direct FIFO connectivity for monitor attachment
 *   • UVM analysis port compatibility
 *   • Configuration database parameter control
 *   • Comprehensive statistics and debug reporting
 *
 * COMPLIANCE:
 *   • IEEE 1800-2017 SystemVerilog
 *   • UVM 1.2 methodology
 *   • UCIe 1.1 specification
 *
 * AUTHOR: UCIe Sideband UVM Agent
 * VERSION: 4.0 - Advanced bidirectional verification architecture
 ******************************************************************************/

class ucie_sb_reg_access_checker extends uvm_component;
  `uvm_component_utils(ucie_sb_reg_access_checker)
  
  /*---------------------------------------------------------------------------
   * TRANSACTION INTERFACE FIFOS
   * Direct analysis export connections for monitor attachment
   *---------------------------------------------------------------------------*/
  
  uvm_tlm_analysis_fifo #(ucie_sb_transaction) tx_fifo;
  uvm_tlm_analysis_fifo #(ucie_sb_transaction) rx_fifo;
  
  /*---------------------------------------------------------------------------
   * CONFIGURATION PARAMETERS
   * Runtime behavior and feature control settings
   *---------------------------------------------------------------------------*/
  
  bit enable_checking = 1;
  bit enable_timeout_check = 1;
  real timeout_ns = 1000.0;
  bit enable_statistics = 1;
  bit enable_tag_support = 1;
  
  /*---------------------------------------------------------------------------
   * OUTSTANDING REQUEST TRACKING STRUCTURE
   * Comprehensive request metadata for bidirectional flow management
   *---------------------------------------------------------------------------*/
  
  typedef struct {
    ucie_sb_transaction req_trans;
    realtime req_time;
    bit [2:0] srcid;
    bit [2:0] dstid;
    bit [23:0] addr;
    bit is_read;
    bit is_64bit;
    bit is_tx_initiated;
  } outstanding_req_t;
  
  /*---------------------------------------------------------------------------
   * TAG-BASED REQUEST TRACKING ARRAYS
   * Separate tracking for TX-initiated and RX-initiated transactions
   *---------------------------------------------------------------------------*/
  
  outstanding_req_t tx_outstanding_requests[32];
  bit tx_tag_in_use[32];
  
  outstanding_req_t rx_outstanding_requests[32];
  bit rx_tag_in_use[32];
  
  /*---------------------------------------------------------------------------
   * NON-TAG MODE TRACKING
   * Single outstanding request tracking with blocking validation
   *---------------------------------------------------------------------------*/
  
  bit tx_has_outstanding_request = 0;
  bit rx_has_outstanding_request = 0;
  outstanding_req_t tx_single_outstanding_request;
  outstanding_req_t rx_single_outstanding_request;
  
  /*---------------------------------------------------------------------------
   * BIDIRECTIONAL STATISTICS COUNTERS
   * Comprehensive performance and error tracking per direction
   *---------------------------------------------------------------------------*/
  
  int tx_requests_sent = 0;
  int tx_completions_received = 0;
  int tx_matched_transactions = 0;
  int tx_tag_mismatches = 0;
  int tx_timeout_errors = 0;
  int tx_tag_violations = 0;
  int tx_blocking_violations = 0;
  
  int rx_requests_sent = 0;
  int rx_completions_received = 0;
  int rx_matched_transactions = 0;
  int rx_tag_mismatches = 0;
  int rx_timeout_errors = 0;
  int rx_tag_violations = 0;
  int rx_blocking_violations = 0;
  
  /*---------------------------------------------------------------------------
   * GENERAL PERFORMANCE METRICS
   * System-wide statistics and FIFO utilization tracking
   *---------------------------------------------------------------------------*/
  
  int protocol_errors = 0;
  int tx_transactions_queued = 0;
  int rx_transactions_queued = 0;
  int max_tx_fifo_depth = 0;
  int max_rx_fifo_depth = 0;
  
  /*---------------------------------------------------------------------------
   * TIMING ANALYSIS METRICS
   * Response time statistics for performance characterization
   *---------------------------------------------------------------------------*/
  
  realtime tx_total_response_time = 0;
  realtime tx_min_response_time = 0;
  realtime tx_max_response_time = 0;
  
  realtime rx_total_response_time = 0;
  realtime rx_min_response_time = 0;
  realtime rx_max_response_time = 0;
  
  /*---------------------------------------------------------------------------
   * CONSTRUCTOR - Initialize tracking arrays and state
   *---------------------------------------------------------------------------*/
  function new(string name = "ucie_sb_reg_access_checker", uvm_component parent = null);
    super.new(name, parent);
    
    for (int i = 0; i < 32; i++) begin
      tx_tag_in_use[i] = 0;
      rx_tag_in_use[i] = 0;
    end
    
    tx_has_outstanding_request = 0;
    rx_has_outstanding_request = 0;
  endfunction
  
  /*---------------------------------------------------------------------------
   * EXTERN METHOD DECLARATIONS
   * All implementation methods declared as extern for clean interface
   *---------------------------------------------------------------------------*/
  
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void end_of_elaboration_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);
  extern virtual function void report_phase(uvm_phase phase);
  
  extern virtual task tx_processor();
  extern virtual task rx_processor();
  extern virtual task fifo_monitor();
  
  extern virtual function void process_tx_request(ucie_sb_transaction trans);
  extern virtual function void process_rx_request(ucie_sb_transaction trans);
  extern virtual function void process_rx_completion(ucie_sb_transaction trans);
  extern virtual function void process_tx_completion(ucie_sb_transaction trans);
  
  extern virtual function bit is_register_access_request(ucie_sb_transaction trans);
  extern virtual function bit is_completion(ucie_sb_transaction trans);
  extern virtual function bit is_read_request(ucie_sb_transaction trans);
  extern virtual function bit validate_completion(ucie_sb_transaction comp, outstanding_req_t req);
  
  extern virtual task timeout_monitor();
  
  extern virtual function void update_tx_timing_statistics(realtime response_time);
  extern virtual function void update_rx_timing_statistics(realtime response_time);
  extern virtual function void print_statistics();
  extern virtual function void check_outstanding_requests();
  
  extern virtual function void set_timeout(real timeout_ns_val);
  extern virtual function void enable_timeout_checking(bit enable);
  extern virtual function void set_tag_support(bit enable);
  extern virtual function void reset_statistics();
  
  extern virtual function int get_tx_fifo_depth();
  extern virtual function int get_rx_fifo_depth();
  extern virtual function void flush_fifos();

endclass : ucie_sb_reg_access_checker

/*******************************************************************************
 * IMPLEMENTATION SECTION
 * All method implementations with detailed behavioral documentation
 ******************************************************************************/

/*-----------------------------------------------------------------------------
 * UVM PHASE IMPLEMENTATIONS
 * Standard UVM component lifecycle management with comprehensive setup
 *-----------------------------------------------------------------------------*/

function void ucie_sb_reg_access_checker::build_phase(uvm_phase phase);
  super.build_phase(phase);
  
  tx_fifo = new("tx_fifo", this);
  rx_fifo = new("rx_fifo", this);
  
  `uvm_info("REG_CHECKER", "Register access checker built with FIFO-only architecture", UVM_LOW)
  `uvm_info("REG_CHECKER", "Connect monitors to: tx_fifo.analysis_export and rx_fifo.analysis_export", UVM_LOW)
endfunction

function void ucie_sb_reg_access_checker::end_of_elaboration_phase(uvm_phase phase);
  super.end_of_elaboration_phase(phase);
  
  `uvm_info("REG_CHECKER", $sformatf("Configuration: enable_checking=%0b, timeout=%.1fns, tag_support=%0b", 
                                     enable_checking, timeout_ns, enable_tag_support), UVM_LOW)
endfunction

task ucie_sb_reg_access_checker::run_phase(uvm_phase phase);
  fork
    tx_processor();
    rx_processor();
    fifo_monitor();
    
    if (enable_timeout_check) begin
      timeout_monitor();
    end
  join_none
endtask

function void ucie_sb_reg_access_checker::report_phase(uvm_phase phase);
  super.report_phase(phase);
  print_statistics();
  check_outstanding_requests();
endfunction

/*-----------------------------------------------------------------------------
 * ASYNCHRONOUS TRANSACTION PROCESSORS
 * Parallel processing engines for TX and RX transaction streams
 *-----------------------------------------------------------------------------*/

/*-----------------------------------------------------------------------------
 * TX TRANSACTION PROCESSOR
 * 
 * Processes all transactions from TX path including:
 *   • TX-initiated requests (TX→RX flow)
 *   • RX-initiated completions (RX→TX response)
 *   • Protocol validation and error detection
 *   • Statistics collection and performance tracking
 *
 * PROCESSING FLOW:
 *   1. Retrieve transaction from TX FIFO (blocking)
 *   2. Classify transaction type (request vs completion)
 *   3. Route to appropriate handler based on flow direction
 *   4. Update statistics and performance metrics
 *-----------------------------------------------------------------------------*/
task ucie_sb_reg_access_checker::tx_processor();
  ucie_sb_transaction trans;
  
  forever begin
    tx_fifo.get(trans);
    
    if (!enable_checking) continue;
    
    tx_transactions_queued++;
    
    `uvm_info("REG_CHECKER", $sformatf("Processing TX transaction: opcode=%s, tag=%0d", 
                                       trans.opcode.name(), trans.tag), UVM_DEBUG)
    
    if (is_register_access_request(trans)) begin
      process_tx_request(trans);
    end
    else if (is_completion(trans)) begin
      process_rx_completion(trans);
    end
    else begin
      `uvm_info("REG_CHECKER", $sformatf("Ignoring non-register TX transaction: opcode=%s", 
                                         trans.opcode.name()), UVM_HIGH)
    end
  end
endtask

/*-----------------------------------------------------------------------------
 * RX TRANSACTION PROCESSOR
 * 
 * Processes all transactions from RX path including:
 *   • RX-initiated requests (RX→TX flow)
 *   • TX-initiated completions (TX→RX response)
 *   • Bidirectional flow coordination and validation
 *   • Performance analysis and error tracking
 *
 * PROCESSING FLOW:
 *   1. Retrieve transaction from RX FIFO (blocking)
 *   2. Determine transaction role in bidirectional flow
 *   3. Execute appropriate validation and matching logic
 *   4. Maintain timing statistics and error counters
 *-----------------------------------------------------------------------------*/
task ucie_sb_reg_access_checker::rx_processor();
  ucie_sb_transaction trans;
  
  forever begin
    rx_fifo.get(trans);
    
    if (!enable_checking) continue;
    
    rx_transactions_queued++;
    
    `uvm_info("REG_CHECKER", $sformatf("Processing RX transaction: opcode=%s, tag=%0d", 
                                       trans.opcode.name(), trans.tag), UVM_DEBUG)
    
    if (is_register_access_request(trans)) begin
      process_rx_request(trans);
    end
    else if (is_completion(trans)) begin
      process_tx_completion(trans);
    end
    else begin
      `uvm_info("REG_CHECKER", $sformatf("Ignoring non-register RX transaction: opcode=%s", 
                                         trans.opcode.name()), UVM_HIGH)
    end
  end
endtask

/*-----------------------------------------------------------------------------
 * FIFO UTILIZATION MONITOR
 * 
 * Continuous monitoring of FIFO depths for performance analysis:
 *   • Maximum depth tracking for capacity planning
 *   • High utilization alerting for bottleneck detection
 *   • System load characterization and optimization
 *
 * MONITORING METRICS:
 *   • Peak FIFO depth per direction
 *   • Current utilization levels
 *   • Performance warning thresholds
 *-----------------------------------------------------------------------------*/
task ucie_sb_reg_access_checker::fifo_monitor();
  forever begin
    #100ns;
    
    if (tx_fifo.size() > max_tx_fifo_depth) begin
      max_tx_fifo_depth = tx_fifo.size();
    end
    
    if (rx_fifo.size() > max_rx_fifo_depth) begin
      max_rx_fifo_depth = rx_fifo.size();
    end
    
    if (tx_fifo.size() > 10) begin
      `uvm_info("REG_CHECKER", $sformatf("High TX FIFO usage: %0d transactions", tx_fifo.size()), UVM_MEDIUM)
    end
    
    if (rx_fifo.size() > 10) begin
      `uvm_info("REG_CHECKER", $sformatf("High RX FIFO usage: %0d transactions", rx_fifo.size()), UVM_MEDIUM)
    end
  end
endtask

/*-----------------------------------------------------------------------------
 * BIDIRECTIONAL REQUEST PROCESSING ENGINES
 * Specialized handlers for each transaction flow direction
 *-----------------------------------------------------------------------------*/

/*-----------------------------------------------------------------------------
 * TX-INITIATED REQUEST PROCESSOR
 * 
 * Handles register access requests originating from TX path:
 *   • Tag allocation and reuse validation
 *   • Non-TAG mode blocking behavior verification
 *   • Request metadata storage for completion matching
 *   • Protocol compliance checking and error reporting
 *
 * TAG MODE OPERATION:
 *   • Validates tag availability (32-entry space)
 *   • Stores complete request context for matching
 *   • Enables concurrent transaction support
 *
 * NON-TAG MODE OPERATION:
 *   • Enforces single outstanding request limitation
 *   • Validates TAG field is zero
 *   • Implements blocking behavior per specification
 *-----------------------------------------------------------------------------*/
function void ucie_sb_reg_access_checker::process_tx_request(ucie_sb_transaction trans);
  bit [4:0] tag = trans.tag;
  
  `uvm_info("REG_CHECKER", $sformatf("Processing TX request: opcode=%s, tag=%0d, addr=0x%06h", 
                                     trans.opcode.name(), tag, trans.addr), UVM_HIGH)
  
  if (!enable_tag_support && tag != 4'h0) begin
    `uvm_error("REG_CHECKER", $sformatf("TX request TAG violation: expected 4'h0, got %0d in non-TAG mode", tag))
    tx_tag_violations++;
    protocol_errors++;
    return;
  end
  
  if (enable_tag_support) begin
    if (tx_tag_in_use[tag]) begin
      `uvm_error("REG_CHECKER", $sformatf("TX tag %0d already in use! Previous request not completed", tag))
      protocol_errors++;
      return;
    end
    
    tx_outstanding_requests[tag].req_trans = trans;
    tx_outstanding_requests[tag].req_time = $realtime;
    tx_outstanding_requests[tag].srcid = trans.srcid;
    tx_outstanding_requests[tag].dstid = trans.dstid;
    tx_outstanding_requests[tag].addr = trans.addr;
    tx_outstanding_requests[tag].is_read = is_read_request(trans);
    tx_outstanding_requests[tag].is_64bit = trans.is_64bit;
    tx_outstanding_requests[tag].is_tx_initiated = 1;
    tx_tag_in_use[tag] = 1;
    
    tx_requests_sent++;
    
    `uvm_info("REG_CHECKER", $sformatf("Stored TX request: tag=%0d, srcid=%0d→dstid=%0d, addr=0x%06h, read=%0b", 
                                       tag, trans.srcid, trans.dstid, trans.addr, tx_outstanding_requests[tag].is_read), UVM_MEDIUM)
  end else begin
    if (tx_has_outstanding_request) begin
      `uvm_error("REG_CHECKER", $sformatf("TX blocking violation: New TX request while outstanding request exists"))
      tx_blocking_violations++;
      return;
    end
    
    tx_single_outstanding_request.req_trans = trans;
    tx_single_outstanding_request.req_time = $realtime;
    tx_single_outstanding_request.srcid = trans.srcid;
    tx_single_outstanding_request.dstid = trans.dstid;
    tx_single_outstanding_request.addr = trans.addr;
    tx_single_outstanding_request.is_read = is_read_request(trans);
    tx_single_outstanding_request.is_64bit = trans.is_64bit;
    tx_single_outstanding_request.is_tx_initiated = 1;
    tx_has_outstanding_request = 1;
    
    tx_requests_sent++;
    
    `uvm_info("REG_CHECKER", $sformatf("Stored single TX request: srcid=%0d→dstid=%0d, addr=0x%06h, read=%0b", 
                                        trans.srcid, trans.dstid, trans.addr, tx_single_outstanding_request.is_read), UVM_MEDIUM)
  end
endfunction

/*-----------------------------------------------------------------------------
 * RX-INITIATED REQUEST PROCESSOR
 * 
 * Handles register access requests originating from RX path:
 *   • Independent tag space management for RX→TX flow
 *   • Parallel tracking with TX-initiated requests
 *   • Non-TAG mode blocking validation for RX direction
 *   • Bidirectional flow coordination and statistics
 *
 * ARCHITECTURAL DESIGN:
 *   • Separate tag arrays prevent cross-direction interference
 *   • Independent blocking state for non-TAG mode
 *   • Parallel processing enables full-duplex operation
 *   • Comprehensive error detection and reporting
 *-----------------------------------------------------------------------------*/
function void ucie_sb_reg_access_checker::process_rx_request(ucie_sb_transaction trans);
  bit [4:0] tag = trans.tag;
  
  `uvm_info("REG_CHECKER", $sformatf("Processing RX request: opcode=%s, tag=%0d, addr=0x%06h", 
                                     trans.opcode.name(), tag, trans.addr), UVM_HIGH)
  
  if (!enable_tag_support && tag != 4'h0) begin
    `uvm_error("REG_CHECKER", $sformatf("RX request TAG violation: expected 4'h0, got %0d in non-TAG mode", tag))
    rx_tag_violations++;
    protocol_errors++;
    return;
  end
  
  if (enable_tag_support) begin
    if (rx_tag_in_use[tag]) begin
      `uvm_error("REG_CHECKER", $sformatf("RX tag %0d already in use! Previous request not completed", tag))
      protocol_errors++;
      return;
    end
    
    rx_outstanding_requests[tag].req_trans = trans;
    rx_outstanding_requests[tag].req_time = $realtime;
    rx_outstanding_requests[tag].srcid = trans.srcid;
    rx_outstanding_requests[tag].dstid = trans.dstid;
    rx_outstanding_requests[tag].addr = trans.addr;
    rx_outstanding_requests[tag].is_read = is_read_request(trans);
    rx_outstanding_requests[tag].is_64bit = trans.is_64bit;
    rx_outstanding_requests[tag].is_tx_initiated = 0;
    rx_tag_in_use[tag] = 1;
    
    rx_requests_sent++;
    
    `uvm_info("REG_CHECKER", $sformatf("Stored RX request: tag=%0d, srcid=%0d→dstid=%0d, addr=0x%06h, read=%0b", 
                                       tag, trans.srcid, trans.dstid, trans.addr, rx_outstanding_requests[tag].is_read), UVM_MEDIUM)
  end else begin
    if (rx_has_outstanding_request) begin
      `uvm_error("REG_CHECKER", $sformatf("RX blocking violation: New RX request while outstanding request exists"))
      rx_blocking_violations++;
      return;
    end
    
    rx_single_outstanding_request.req_trans = trans;
    rx_single_outstanding_request.req_time = $realtime;
    rx_single_outstanding_request.srcid = trans.srcid;
    rx_single_outstanding_request.dstid = trans.dstid;
    rx_single_outstanding_request.addr = trans.addr;
    rx_single_outstanding_request.is_read = is_read_request(trans);
    rx_single_outstanding_request.is_64bit = trans.is_64bit;
    rx_single_outstanding_request.is_tx_initiated = 0;
    rx_has_outstanding_request = 1;
    
    rx_requests_sent++;
    
    `uvm_info("REG_CHECKER", $sformatf("Stored single RX request: srcid=%0d→dstid=%0d, addr=0x%06h, read=%0b", 
                                        trans.srcid, trans.dstid, trans.addr, rx_single_outstanding_request.is_read), UVM_MEDIUM)
  end
endfunction

/*-----------------------------------------------------------------------------
 * TX COMPLETION PROCESSOR (RX→TX Response)
 * 
 * Processes completion transactions responding to RX-initiated requests:
 *   • Matches completions with corresponding RX requests
 *   • Validates source/destination ID swapping
 *   • Calculates response time statistics
 *   • Manages tag deallocation and state cleanup
 *
 * VALIDATION CHECKS:
 *   • Tag correspondence with outstanding RX request
 *   • Source/destination ID proper swapping
 *   • Data width consistency for read completions
 *   • Protocol compliance and error detection
 *-----------------------------------------------------------------------------*/
function void ucie_sb_reg_access_checker::process_rx_completion(ucie_sb_transaction trans);
  bit [4:0] tag = trans.tag;
  realtime response_time;
  
  `uvm_info("REG_CHECKER", $sformatf("Processing TX completion (RX→TX response): tag=%0d, srcid=%0d, dstid=%0d, status=0x%04h", 
                                     tag, trans.srcid, trans.dstid, trans.status), UVM_HIGH)
  
  if (!enable_tag_support && tag != 4'h0) begin
    `uvm_error("REG_CHECKER", $sformatf("TX completion TAG violation: expected 4'h0, got %0d in non-TAG mode", tag))
    tx_tag_violations++;
    protocol_errors++;
    return;
  end
  
  if (enable_tag_support) begin
    if (!rx_tag_in_use[tag]) begin
      `uvm_error("REG_CHECKER", $sformatf("TX completion tag %0d has no corresponding RX request!", tag))
      protocol_errors++;
      return;
    end
    
    if (!validate_completion(trans, rx_outstanding_requests[tag])) begin
      rx_tag_mismatches++;
      return;
    end
    
    response_time = $realtime - rx_outstanding_requests[tag].req_time;
    update_rx_timing_statistics(response_time);
    
    rx_tag_in_use[tag] = 0;
    rx_completions_received++;
    rx_matched_transactions++;
    
            `uvm_info("REG_CHECKER", $sformatf("Matched RX→TX completion: tag=%0d, response_time=%.1fns", 
                                         tag, response_time/1ns), UVM_MEDIUM)
    end else begin
     if (!tx_has_outstanding_request) begin
       `uvm_error("REG_CHECKER", $sformatf("TX completion with no outstanding TX request in non-TAG mode!"))
       protocol_errors++;
       return;
     end
     
     if (!validate_completion(trans, tx_single_outstanding_request)) begin
       rx_tag_mismatches++;
       return;
     end
     
     response_time = $realtime - tx_single_outstanding_request.req_time;
     update_rx_timing_statistics(response_time);
     
     tx_has_outstanding_request = 0;
     rx_completions_received++;
     rx_matched_transactions++;
     
     `uvm_info("REG_CHECKER", $sformatf("Matched single RX→TX completion: response_time=%.1fns", 
                                        response_time/1ns), UVM_MEDIUM)
   end
endfunction

/*-----------------------------------------------------------------------------
 * RX COMPLETION PROCESSOR (TX→RX Response)
 * 
 * Processes completion transactions responding to TX-initiated requests:
 *   • Matches completions with corresponding TX requests
 *   • Implements comprehensive protocol validation
 *   • Tracks performance metrics and timing statistics
 *   • Manages bidirectional flow coordination
 *
 * MATCHING ALGORITHM:
 *   • Tag-based lookup in TX outstanding request array
 *   • Protocol field validation (srcid/dstid swapping)
 *   • Data consistency checking for read operations
 *   • Response time calculation and statistical analysis
 *-----------------------------------------------------------------------------*/
function void ucie_sb_reg_access_checker::process_tx_completion(ucie_sb_transaction trans);
  bit [4:0] tag = trans.tag;
  realtime response_time;
  
  `uvm_info("REG_CHECKER", $sformatf("Processing RX completion (TX→RX response): tag=%0d, srcid=%0d, dstid=%0d, status=0x%04h", 
                                     tag, trans.srcid, trans.dstid, trans.status), UVM_HIGH)
  
  if (!enable_tag_support && tag != 4'h0) begin
    `uvm_error("REG_CHECKER", $sformatf("RX completion TAG violation: expected 4'h0, got %0d in non-TAG mode", tag))
    rx_tag_violations++;
    protocol_errors++;
    return;
  end
  
  if (enable_tag_support) begin
    if (!tx_tag_in_use[tag]) begin
      `uvm_error("REG_CHECKER", $sformatf("RX completion tag %0d has no corresponding TX request!", tag))
      protocol_errors++;
      return;
    end
    
    if (!validate_completion(trans, tx_outstanding_requests[tag])) begin
      tx_tag_mismatches++;
      return;
    end
    
    response_time = $realtime - tx_outstanding_requests[tag].req_time;
    update_tx_timing_statistics(response_time);
    
    tx_tag_in_use[tag] = 0;
    tx_completions_received++;
    tx_matched_transactions++;
    
            `uvm_info("REG_CHECKER", $sformatf("Matched TX→RX completion: tag=%0d, response_time=%.1fns", 
                                         tag, response_time/1ns), UVM_MEDIUM)
    end else begin
     if (!rx_has_outstanding_request) begin
       `uvm_error("REG_CHECKER", $sformatf("RX completion with no outstanding RX request in non-TAG mode!"))
       protocol_errors++;
       return;
     end
     
     if (!validate_completion(trans, rx_single_outstanding_request)) begin
       tx_tag_mismatches++;
       return;
     end
     
     response_time = $realtime - rx_single_outstanding_request.req_time;
     update_tx_timing_statistics(response_time);
     
     rx_has_outstanding_request = 0;
     tx_completions_received++;
     tx_matched_transactions++;
     
     `uvm_info("REG_CHECKER", $sformatf("Matched single TX→RX completion: response_time=%.1fns", 
                                        response_time/1ns), UVM_MEDIUM)
   end
endfunction

/*-----------------------------------------------------------------------------
 * PROTOCOL VALIDATION FUNCTIONS
 * Core validation logic for transaction classification and compliance
 *-----------------------------------------------------------------------------*/

function bit ucie_sb_reg_access_checker::is_register_access_request(ucie_sb_transaction trans);
  return (trans.pkt_type == PKT_REG_ACCESS && 
          (trans.opcode inside {MEM_READ_32B, MEM_WRITE_32B, DMS_READ_32B, DMS_WRITE_32B, 
                                CFG_READ_32B, CFG_WRITE_32B, MEM_READ_64B, MEM_WRITE_64B, 
                                DMS_READ_64B, DMS_WRITE_64B, CFG_READ_64B, CFG_WRITE_64B}));
endfunction

function bit ucie_sb_reg_access_checker::is_completion(ucie_sb_transaction trans);
  return (trans.pkt_type == PKT_COMPLETION && 
          (trans.opcode inside {COMPLETION_NO_DATA, COMPLETION_32B, COMPLETION_64B}));
endfunction

function bit ucie_sb_reg_access_checker::is_read_request(ucie_sb_transaction trans);
  return (trans.opcode inside {MEM_READ_32B, DMS_READ_32B, CFG_READ_32B, 
                               MEM_READ_64B, DMS_READ_64B, CFG_READ_64B});
endfunction

/*-----------------------------------------------------------------------------
 * COMPLETION VALIDATION ENGINE
 * 
 * Comprehensive validation of request-completion matching:
 *   • Source/destination ID swapping verification
 *   • Data presence and width consistency checking
 *   • Protocol compliance validation
 *   • Error detection and reporting
 *
 * VALIDATION CRITERIA:
 *   • Completion srcid must equal request dstid
 *   • Completion dstid must equal request srcid
 *   • Read completions must have appropriate data payload
 *   • Data width must match request specifications
 *-----------------------------------------------------------------------------*/
function bit ucie_sb_reg_access_checker::validate_completion(ucie_sb_transaction comp, outstanding_req_t req);
  bit valid = 1;
  bit expected_has_data;
  bit expected_64bit;
  
  if (comp.srcid != req.dstid) begin
    `uvm_error("REG_CHECKER", $sformatf("Completion srcid mismatch: expected=%0d, got=%0d", 
                                        req.dstid, comp.srcid))
    valid = 0;
  end
  
  if (comp.dstid != req.srcid) begin
    `uvm_error("REG_CHECKER", $sformatf("Completion dstid mismatch: expected=%0d, got=%0d", 
                                        req.srcid, comp.dstid))
    valid = 0;
  end
  
  if (req.is_read) begin
    expected_has_data = 1;
    expected_64bit = req.is_64bit;
    
    if (comp.has_data != expected_has_data) begin
      `uvm_error("REG_CHECKER", $sformatf("Read completion data mismatch: expected has_data=%0b, got=%0b", 
                                          expected_has_data, comp.has_data))
      valid = 0;
    end
    
    if (comp.is_64bit != expected_64bit) begin
      `uvm_error("REG_CHECKER", $sformatf("Read completion size mismatch: expected 64bit=%0b, got=%0b", 
                                          expected_64bit, comp.is_64bit))
      valid = 0;
    end
  end
  
  return valid;
endfunction

/*-----------------------------------------------------------------------------
 * TIMEOUT MONITORING ENGINE
 * 
 * Continuous monitoring for request timeout violations:
 *   • Periodic scanning of outstanding request arrays
 *   • Configurable timeout threshold enforcement
 *   • Automatic cleanup of timed-out requests
 *   • Comprehensive error reporting and statistics
 *
 * MONITORING SCOPE:
 *   • TX-initiated requests (both TAG and non-TAG modes)
 *   • RX-initiated requests (both TAG and non-TAG modes)
 *   • Configurable timeout periods per system requirements
 *   • Automatic state cleanup for system recovery
 *-----------------------------------------------------------------------------*/
task ucie_sb_reg_access_checker::timeout_monitor();
  realtime current_time;
  
  forever begin
    #(timeout_ns * 1ns / 10);
    
    current_time = $realtime;
    
    if (enable_tag_support) begin
      for (int tag = 0; tag < 32; tag++) begin
        if (tx_tag_in_use[tag]) begin
          if ((current_time - tx_outstanding_requests[tag].req_time) > (timeout_ns * 1ns)) begin
            `uvm_error("REG_CHECKER", $sformatf("TX request timeout: tag=%0d, addr=0x%06h, elapsed=%.1fns", 
                                                tag, tx_outstanding_requests[tag].addr, 
                                                (current_time - tx_outstanding_requests[tag].req_time)/1ns))
            tx_timeout_errors++;
            tx_tag_in_use[tag] = 0;
          end
        end
      end
    end else begin
      if (tx_has_outstanding_request) begin
        if ((current_time - tx_single_outstanding_request.req_time) > (timeout_ns * 1ns)) begin
          `uvm_error("REG_CHECKER", $sformatf("Single TX request timeout: elapsed=%.1fns", 
                                              (current_time - tx_single_outstanding_request.req_time)/1ns))
          tx_timeout_errors++;
          tx_has_outstanding_request = 0;
        end
      end
    end
    
    if (enable_tag_support) begin
      for (int tag = 0; tag < 32; tag++) begin
        if (rx_tag_in_use[tag]) begin
          if ((current_time - rx_outstanding_requests[tag].req_time) > (timeout_ns * 1ns)) begin
            `uvm_error("REG_CHECKER", $sformatf("RX request timeout: tag=%0d, addr=0x%06h, elapsed=%.1fns", 
                                                tag, rx_outstanding_requests[tag].addr, 
                                                (current_time - rx_outstanding_requests[tag].req_time)/1ns))
            rx_timeout_errors++;
            rx_tag_in_use[tag] = 0;
          end
        end
      end
    end else begin
      if (rx_has_outstanding_request) begin
        if ((current_time - rx_single_outstanding_request.req_time) > (timeout_ns * 1ns)) begin
          `uvm_error("REG_CHECKER", $sformatf("Single RX request timeout: elapsed=%.1fns", 
                                              (current_time - rx_single_outstanding_request.req_time)/1ns))
          rx_timeout_errors++;
          rx_has_outstanding_request = 0;
        end
      end
    end
  end
endtask

/*-----------------------------------------------------------------------------
 * PERFORMANCE ANALYSIS AND REPORTING
 * Comprehensive statistics collection and analysis framework
 *-----------------------------------------------------------------------------*/

function void ucie_sb_reg_access_checker::update_tx_timing_statistics(realtime response_time);
  tx_total_response_time += response_time;
  
  if (tx_matched_transactions == 1) begin
    tx_min_response_time = response_time;
    tx_max_response_time = response_time;
  end else begin
    if (response_time < tx_min_response_time) tx_min_response_time = response_time;
    if (response_time > tx_max_response_time) tx_max_response_time = response_time;
  end
endfunction

function void ucie_sb_reg_access_checker::update_rx_timing_statistics(realtime response_time);
  rx_total_response_time += response_time;
  
  if (rx_matched_transactions == 1) begin
    rx_min_response_time = response_time;
    rx_max_response_time = response_time;
  end else begin
    if (response_time < rx_min_response_time) rx_min_response_time = response_time;
    if (response_time > rx_max_response_time) rx_max_response_time = response_time;
  end
endfunction

/*-----------------------------------------------------------------------------
 * COMPREHENSIVE STATISTICS REPORTING
 * 
 * Generates detailed performance and compliance analysis including:
 *   • Bidirectional flow statistics and comparison
 *   • FIFO utilization and performance metrics
 *   • Response time analysis (min/max/average)
 *   • Error detection and protocol violation summary
 *
 * REPORT SECTIONS:
 *   • Configuration summary and operational mode
 *   • FIFO performance and utilization statistics
 *   • TX→RX flow analysis and metrics
 *   • RX→TX flow analysis and metrics
 *   • Protocol error summary and compliance status
 *-----------------------------------------------------------------------------*/
function void ucie_sb_reg_access_checker::print_statistics();
  realtime tx_avg_response_time, rx_avg_response_time;
  
  if (!enable_statistics) return;
  
  `uvm_info("REG_CHECKER", "=== Bidirectional Register Access Checker Statistics ===", UVM_LOW)
  `uvm_info("REG_CHECKER", $sformatf("Configuration: TAG support %s", enable_tag_support ? "enabled" : "disabled"), UVM_LOW)
  `uvm_info("REG_CHECKER", "FIFO Statistics:", UVM_LOW)
  `uvm_info("REG_CHECKER", $sformatf("  TX transactions queued: %0d", tx_transactions_queued), UVM_LOW)
  `uvm_info("REG_CHECKER", $sformatf("  RX transactions queued: %0d", rx_transactions_queued), UVM_LOW)
  `uvm_info("REG_CHECKER", $sformatf("  Max TX FIFO depth: %0d", max_tx_fifo_depth), UVM_LOW)
  `uvm_info("REG_CHECKER", $sformatf("  Max RX FIFO depth: %0d", max_rx_fifo_depth), UVM_LOW)
  `uvm_info("REG_CHECKER", $sformatf("  Current TX FIFO depth: %0d", tx_fifo.size()), UVM_LOW)
  `uvm_info("REG_CHECKER", $sformatf("  Current RX FIFO depth: %0d", rx_fifo.size()), UVM_LOW)
  
  `uvm_info("REG_CHECKER", "TX→RX Flow Statistics:", UVM_LOW)
  `uvm_info("REG_CHECKER", $sformatf("  TX requests sent: %0d", tx_requests_sent), UVM_LOW)
  `uvm_info("REG_CHECKER", $sformatf("  RX completions received: %0d", tx_completions_received), UVM_LOW)
  `uvm_info("REG_CHECKER", $sformatf("  Matched transactions: %0d", tx_matched_transactions), UVM_LOW)
  `uvm_info("REG_CHECKER", $sformatf("  Tag mismatches: %0d", tx_tag_mismatches), UVM_LOW)
  `uvm_info("REG_CHECKER", $sformatf("  Timeout errors: %0d", tx_timeout_errors), UVM_LOW)
  `uvm_info("REG_CHECKER", $sformatf("  Tag violations: %0d", tx_tag_violations), UVM_LOW)
  `uvm_info("REG_CHECKER", $sformatf("  Blocking violations: %0d", tx_blocking_violations), UVM_LOW)
  
  if (tx_matched_transactions > 0) begin
    tx_avg_response_time = tx_total_response_time / tx_matched_transactions;
    `uvm_info("REG_CHECKER", $sformatf("  Response time - Min: %.1fns, Max: %.1fns, Avg: %.1fns", 
                                       tx_min_response_time/1ns, tx_max_response_time/1ns, tx_avg_response_time/1ns), UVM_LOW)
  end
  
  `uvm_info("REG_CHECKER", "RX→TX Flow Statistics:", UVM_LOW)
  `uvm_info("REG_CHECKER", $sformatf("  RX requests sent: %0d", rx_requests_sent), UVM_LOW)
  `uvm_info("REG_CHECKER", $sformatf("  TX completions received: %0d", rx_completions_received), UVM_LOW)
  `uvm_info("REG_CHECKER", $sformatf("  Matched transactions: %0d", rx_matched_transactions), UVM_LOW)
  `uvm_info("REG_CHECKER", $sformatf("  Tag mismatches: %0d", rx_tag_mismatches), UVM_LOW)
  `uvm_info("REG_CHECKER", $sformatf("  Timeout errors: %0d", rx_timeout_errors), UVM_LOW)
  `uvm_info("REG_CHECKER", $sformatf("  Tag violations: %0d", rx_tag_violations), UVM_LOW)
  `uvm_info("REG_CHECKER", $sformatf("  Blocking violations: %0d", rx_blocking_violations), UVM_LOW)
  
  if (rx_matched_transactions > 0) begin
    rx_avg_response_time = rx_total_response_time / rx_matched_transactions;
    `uvm_info("REG_CHECKER", $sformatf("  Response time - Min: %.1fns, Max: %.1fns, Avg: %.1fns", 
                                       rx_min_response_time/1ns, rx_max_response_time/1ns, rx_avg_response_time/1ns), UVM_LOW)
  end
  
  `uvm_info("REG_CHECKER", $sformatf("Protocol errors: %0d", protocol_errors), UVM_LOW)
  `uvm_info("REG_CHECKER", "========================================================", UVM_LOW)
endfunction

/*-----------------------------------------------------------------------------
 * OUTSTANDING REQUEST AUDIT
 * 
 * End-of-test validation for incomplete transactions:
 *   • Scans all outstanding request arrays
 *   • Reports incomplete transactions as warnings/errors
 *   • Provides debugging information for unmatched requests
 *   • Ensures clean test completion verification
 *-----------------------------------------------------------------------------*/
function void ucie_sb_reg_access_checker::check_outstanding_requests();
  int tx_outstanding_count = 0;
  int rx_outstanding_count = 0;
  
  if (enable_tag_support) begin
    for (int tag = 0; tag < 32; tag++) begin
      if (tx_tag_in_use[tag]) begin
        tx_outstanding_count++;
        `uvm_warning("REG_CHECKER", $sformatf("Outstanding TX request at end of test: tag=%0d, addr=0x%06h", 
                                              tag, tx_outstanding_requests[tag].addr))
      end
    end
  end else begin
    if (tx_has_outstanding_request) begin
      tx_outstanding_count++;
      `uvm_warning("REG_CHECKER", $sformatf("Outstanding single TX request at end of test: addr=0x%06h", 
                                            tx_single_outstanding_request.addr))
    end
  end
  
  if (enable_tag_support) begin
    for (int tag = 0; tag < 32; tag++) begin
      if (rx_tag_in_use[tag]) begin
        rx_outstanding_count++;
        `uvm_warning("REG_CHECKER", $sformatf("Outstanding RX request at end of test: tag=%0d, addr=0x%06h", 
                                              tag, rx_outstanding_requests[tag].addr))
      end
    end
  end else begin
    if (rx_has_outstanding_request) begin
      rx_outstanding_count++;
      `uvm_warning("REG_CHECKER", $sformatf("Outstanding single RX request at end of test: addr=0x%06h", 
                                            rx_single_outstanding_request.addr))
    end
  end
  
  if (enable_tag_support) begin
    if (tx_outstanding_count > 0) begin
      `uvm_error("REG_CHECKER", $sformatf("%0d TX requests remain outstanding at end of test", tx_outstanding_count))
    end
    
    if (rx_outstanding_count > 0) begin
      `uvm_error("REG_CHECKER", $sformatf("%0d RX requests remain outstanding at end of test", rx_outstanding_count))
    end
  end else begin
    if (tx_outstanding_count > 0) begin
      `uvm_error("REG_CHECKER", $sformatf("%0d TX requests remain outstanding at end of test", tx_outstanding_count))
    end
    
    if (rx_outstanding_count > 0) begin
      `uvm_error("REG_CHECKER", $sformatf("%0d RX requests remain outstanding at end of test", rx_outstanding_count))
    end
  end
endfunction

/*-----------------------------------------------------------------------------
 * CONFIGURATION AND CONTROL INTERFACE
 * Runtime configuration and system management functions
 *-----------------------------------------------------------------------------*/

function void ucie_sb_reg_access_checker::set_timeout(real timeout_ns_val);
  timeout_ns = timeout_ns_val;
  `uvm_info("REG_CHECKER", $sformatf("Set timeout to %.1fns", timeout_ns), UVM_LOW)
endfunction

function void ucie_sb_reg_access_checker::enable_timeout_checking(bit enable);
  enable_timeout_check = enable;
  `uvm_info("REG_CHECKER", $sformatf("Timeout checking %s", enable ? "enabled" : "disabled"), UVM_LOW)
endfunction

function void ucie_sb_reg_access_checker::set_tag_support(bit enable);
  enable_tag_support = enable;
  `uvm_info("REG_CHECKER", $sformatf("TAG support %s", enable ? "enabled" : "disabled"), UVM_LOW)
endfunction

/*-----------------------------------------------------------------------------
 * STATISTICS RESET AND MANAGEMENT
 * 
 * Comprehensive reset of all statistical counters and tracking state:
 *   • Bidirectional flow statistics reset
 *   • Timing analysis data clearing
 *   • Outstanding request state cleanup
 *   • FIFO utilization metrics reset
 *-----------------------------------------------------------------------------*/
function void ucie_sb_reg_access_checker::reset_statistics();
  tx_requests_sent = 0;
  tx_completions_received = 0;
  tx_matched_transactions = 0;
  tx_tag_mismatches = 0;
  tx_timeout_errors = 0;
  tx_tag_violations = 0;
  tx_blocking_violations = 0;
  tx_total_response_time = 0;
  tx_min_response_time = 0;
  tx_max_response_time = 0;
  
  rx_requests_sent = 0;
  rx_completions_received = 0;
  rx_matched_transactions = 0;
  rx_tag_mismatches = 0;
  rx_timeout_errors = 0;
  rx_tag_violations = 0;
  rx_blocking_violations = 0;
  rx_total_response_time = 0;
  rx_min_response_time = 0;
  rx_max_response_time = 0;
  
  protocol_errors = 0;
  tx_transactions_queued = 0;
  rx_transactions_queued = 0;
  max_tx_fifo_depth = 0;
  max_rx_fifo_depth = 0;
  
  tx_has_outstanding_request = 0;
  rx_has_outstanding_request = 0;
  
  `uvm_info("REG_CHECKER", "Bidirectional statistics reset", UVM_LOW)
endfunction

/*-----------------------------------------------------------------------------
 * FIFO MANAGEMENT INTERFACE
 * Direct FIFO access and control for advanced usage scenarios
 *-----------------------------------------------------------------------------*/

function int ucie_sb_reg_access_checker::get_tx_fifo_depth();
  return tx_fifo.size();
endfunction

function int ucie_sb_reg_access_checker::get_rx_fifo_depth();
  return rx_fifo.size();
endfunction

function void ucie_sb_reg_access_checker::flush_fifos();
  tx_fifo.flush();
  rx_fifo.flush();
  `uvm_info("REG_CHECKER", "FIFOs flushed", UVM_LOW)
endfunction