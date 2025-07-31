// UCIe Sideband Register Access Checker
// Monitors TX register access requests and matches with RX completions

//=============================================================================
// CLASS: ucie_sb_reg_access_checker
//
// DESCRIPTION:
//   Checker that monitors bidirectional sideband register access transactions.
//   Handles both TX→RX and RX→TX request-completion flows. Ensures proper 
//   request-completion pairing with correct tag matching and validates protocol 
//   compliance for both directions.
//
// FEATURES:
//   - Bidirectional request-completion tracking (TX↔RX)
//   - Separate tracking for TX-initiated and RX-initiated transactions
//   - Tag-based matching with direction awareness (when TAG support enabled)
//   - Non-TAG mode with blocking behavior (when TAG support disabled)
//   - Validates proper source/destination swapping for both directions
//   - Timeout detection for missing completions
//   - Comprehensive statistics for both directions
//   - FIFO buffering for concurrent transaction handling
//
// AUTHOR: UCIe Sideband UVM Agent
// VERSION: 3.0 - TAG/Non-TAG Mode Support
//=============================================================================

class ucie_sb_reg_access_checker extends uvm_component;
  `uvm_component_utils(ucie_sb_reg_access_checker)
  
  //=============================================================================
  // CLASS FIELDS
  //=============================================================================
  
  // Analysis ports for receiving transactions
  uvm_analysis_imp_tx #(ucie_sb_transaction, ucie_sb_reg_access_checker) tx_imp;
  uvm_analysis_imp_rx #(ucie_sb_transaction, ucie_sb_reg_access_checker) rx_imp;
  
  // FIFOs for buffering transactions from TX and RX sides
  uvm_tlm_analysis_fifo #(ucie_sb_transaction) tx_fifo;
  uvm_tlm_analysis_fifo #(ucie_sb_transaction) rx_fifo;
  
  // Configuration parameters
  bit enable_checking = 1;
  bit enable_timeout_check = 1;
  real timeout_ns = 1000.0;  // 1us timeout for completions
  bit enable_statistics = 1;
  bit enable_tag_support = 1;  // NEW: Enable/disable TAG functionality
  
  // Outstanding request tracking with direction awareness
  typedef struct {
    ucie_sb_transaction req_trans;
    realtime req_time;
    bit [2:0] srcid;
    bit [2:0] dstid;
    bit [23:0] addr;
    bit is_read;
    bit is_64bit;
    bit is_tx_initiated;  // 1=TX→RX request, 0=RX→TX request
  } outstanding_req_t;
  
  // Tag-based request tracking (5-bit tag = 32 entries per direction)
  // TX-initiated requests (TX sends request, expects RX completion)
  outstanding_req_t tx_outstanding_requests[32];
  bit tx_tag_in_use[32];
  
  // RX-initiated requests (RX sends request, expects TX completion)  
  outstanding_req_t rx_outstanding_requests[32];
  bit rx_tag_in_use[32];
  
  // Non-TAG mode tracking - only one outstanding request per direction
  bit tx_has_outstanding_request = 0;  // NEW: For non-TAG mode blocking
  bit rx_has_outstanding_request = 0;  // NEW: For non-TAG mode blocking
  outstanding_req_t tx_single_outstanding_request;  // NEW: Single request tracking
  outstanding_req_t rx_single_outstanding_request;  // NEW: Single request tracking
  
  // Statistics - Bidirectional
  // TX-initiated flows (TX request → RX completion)
  int tx_requests_sent = 0;
  int tx_completions_received = 0;
  int tx_matched_transactions = 0;
  int tx_tag_mismatches = 0;
  int tx_timeout_errors = 0;
  int tx_tag_violations = 0;  // NEW: TAG field violations in non-TAG mode
  int tx_blocking_violations = 0;  // NEW: Blocking violations in non-TAG mode
  
  // RX-initiated flows (RX request → TX completion)
  int rx_requests_sent = 0;
  int rx_completions_received = 0;
  int rx_matched_transactions = 0;
  int rx_tag_mismatches = 0;
  int rx_timeout_errors = 0;
  int rx_tag_violations = 0;  // NEW: TAG field violations in non-TAG mode
  int rx_blocking_violations = 0;  // NEW: Blocking violations in non-TAG mode
  
  // General statistics
  int protocol_errors = 0;
  int tx_transactions_queued = 0;
  int rx_transactions_queued = 0;
  int max_tx_fifo_depth = 0;
  int max_rx_fifo_depth = 0;
  
  // Timing tracking - Bidirectional
  // TX-initiated timing
  realtime tx_total_response_time = 0;
  realtime tx_min_response_time = 0;
  realtime tx_max_response_time = 0;
  
  // RX-initiated timing
  realtime rx_total_response_time = 0;
  realtime rx_min_response_time = 0;
  realtime rx_max_response_time = 0;
  
  //=============================================================================
  // CONSTRUCTOR
  //=============================================================================
  
  function new(string name = "ucie_sb_reg_access_checker", uvm_component parent = null);
    super.new(name, parent);
    
    // Initialize tracking arrays for both directions
    for (int i = 0; i < 32; i++) begin
      tx_tag_in_use[i] = 0;
      rx_tag_in_use[i] = 0;
    end
    
    // Initialize non-TAG mode tracking
    tx_has_outstanding_request = 0;
    rx_has_outstanding_request = 0;
  endfunction
  
  //=============================================================================
  // UVM PHASES
  //=============================================================================
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    // Create analysis imports
    tx_imp = new("tx_imp", this);
    rx_imp = new("rx_imp", this);
    
    // Create FIFOs for buffering transactions
    tx_fifo = new("tx_fifo", this);
    rx_fifo = new("rx_fifo", this);
    
    `uvm_info("REG_CHECKER", "Register access checker built with FIFOs", UVM_LOW)
  endfunction
  
  virtual function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    
    `uvm_info("REG_CHECKER", $sformatf("Configuration: enable_checking=%0b, timeout=%.1fns, tag_support=%0b", 
                                       enable_checking, timeout_ns, enable_tag_support), UVM_LOW)
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    fork
      // Process TX transactions from FIFO
      tx_processor();
      
      // Process RX transactions from FIFO  
      rx_processor();
      
      // Timeout monitoring
      if (enable_timeout_check) begin
        timeout_monitor();
      end
    join_none
  endtask
  
  virtual function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    print_statistics();
    check_outstanding_requests();
  endfunction
  
  //=============================================================================
  // ANALYSIS IMPORT IMPLEMENTATIONS
  //=============================================================================
  
  // TX side analysis - put transactions into FIFO for asynchronous processing
  virtual function void write_tx(ucie_sb_transaction trans);
    if (!enable_checking) return;
    
    // Put all TX transactions into FIFO (filtering done in processor)
    tx_fifo.analysis_export.write(trans);
    tx_transactions_queued++;
    
    // Track maximum FIFO depth
    if (tx_fifo.size() > max_tx_fifo_depth) begin
      max_tx_fifo_depth = tx_fifo.size();
    end
    
    `uvm_info("REG_CHECKER", $sformatf("TX transaction queued: opcode=%s, tag=%0d, fifo_depth=%0d", 
                                       trans.opcode.name(), trans.tag, tx_fifo.size()), UVM_DEBUG)
  endfunction
  
  // RX side analysis - put transactions into FIFO for asynchronous processing
  virtual function void write_rx(ucie_sb_transaction trans);
    if (!enable_checking) return;
    
    // Put all RX transactions into FIFO (filtering done in processor)
    rx_fifo.analysis_export.write(trans);
    rx_transactions_queued++;
    
    // Track maximum FIFO depth
    if (rx_fifo.size() > max_rx_fifo_depth) begin
      max_rx_fifo_depth = rx_fifo.size();
    end
    
    `uvm_info("REG_CHECKER", $sformatf("RX transaction queued: opcode=%s, tag=%0d, fifo_depth=%0d", 
                                       trans.opcode.name(), trans.tag, rx_fifo.size()), UVM_DEBUG)
  endfunction
  
  //=============================================================================
  // FIFO PROCESSORS (ASYNCHRONOUS)
  //=============================================================================
  
  // TX FIFO processor - handles both requests and completions
  virtual task tx_processor();
    ucie_sb_transaction trans;
    
    forever begin
      // Get transaction from TX FIFO (blocking)
      tx_fifo.get(trans);
      
      // Process register access requests (TX→RX flow)
      if (is_register_access_request(trans)) begin
        process_tx_request(trans);
      end
      // Process completions (RX→TX response)
      else if (is_completion(trans)) begin
        process_rx_completion(trans);
      end
    end
  endtask
  
  // RX FIFO processor - handles both requests and completions
  virtual task rx_processor();
    ucie_sb_transaction trans;
    
    forever begin
      // Get transaction from RX FIFO (blocking)
      rx_fifo.get(trans);
      
      // Process register access requests (RX→TX flow)
      if (is_register_access_request(trans)) begin
        process_rx_request(trans);
      end
      // Process completions (TX→RX response)
      else if (is_completion(trans)) begin
        process_tx_completion(trans);
      end
    end
  endtask
  
  //=============================================================================
  // BIDIRECTIONAL REQUEST/COMPLETION PROCESSING
  //=============================================================================
  
  // TX-initiated request processing (TX sends request)
  virtual function void process_tx_request(ucie_sb_transaction trans);
    bit [4:0] tag = trans.tag;
    
    `uvm_info("REG_CHECKER", $sformatf("Processing TX request: opcode=%s, tag=%0d, addr=0x%06h", 
                                       trans.opcode.name(), tag, trans.addr), UVM_HIGH)
    
    // Validate TAG field for non-TAG mode
    if (!enable_tag_support && tag != 4'h0) begin
      `uvm_error("REG_CHECKER", $sformatf("TX request TAG violation: expected 4'h0, got %0d in non-TAG mode", tag))
      tx_tag_violations++;
      protocol_errors++;
      return;
    end
    
    // Check if TAG support is enabled
    if (enable_tag_support) begin
      // Check if tag is already in use for TX-initiated requests
      if (tx_tag_in_use[tag]) begin
        `uvm_error("REG_CHECKER", $sformatf("TX tag %0d already in use! Previous request not completed", tag))
        protocol_errors++;
        return;
      end
      
      // Store TX-initiated request information
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
      // Non-TAG mode: Block if a request is already outstanding
      if (tx_has_outstanding_request) begin
        `uvm_error("REG_CHECKER", $sformatf("TX blocking violation: New TX request while outstanding request exists"))
        tx_blocking_violations++;
        return;
      end
      
      // Store single outstanding request
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
  
  // RX-initiated request processing (RX sends request)
  virtual function void process_rx_request(ucie_sb_transaction trans);
    bit [4:0] tag = trans.tag;
    
    `uvm_info("REG_CHECKER", $sformatf("Processing RX request: opcode=%s, tag=%0d, addr=0x%06h", 
                                       trans.opcode.name(), tag, trans.addr), UVM_HIGH)
    
    // Validate TAG field for non-TAG mode
    if (!enable_tag_support && tag != 4'h0) begin
      `uvm_error("REG_CHECKER", $sformatf("RX request TAG violation: expected 4'h0, got %0d in non-TAG mode", tag))
      rx_tag_violations++;
      protocol_errors++;
      return;
    end
    
    // Check if TAG support is enabled
    if (enable_tag_support) begin
      // Check if tag is already in use for RX-initiated requests
      if (rx_tag_in_use[tag]) begin
        `uvm_error("REG_CHECKER", $sformatf("RX tag %0d already in use! Previous request not completed", tag))
        protocol_errors++;
        return;
      end
      
      // Store RX-initiated request information
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
      // Non-TAG mode: Block if a request is already outstanding
      if (rx_has_outstanding_request) begin
        `uvm_error("REG_CHECKER", $sformatf("RX blocking violation: New RX request while outstanding request exists"))
        rx_blocking_violations++;
        return;
      end
      
      // Store single outstanding request
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
  
  // TX completion processing (response to RX-initiated request)
  virtual function void process_rx_completion(ucie_sb_transaction trans);
    bit [4:0] tag = trans.tag;
    realtime response_time;
    
    `uvm_info("REG_CHECKER", $sformatf("Processing TX completion (RX→TX response): tag=%0d, srcid=%0d, dstid=%0d, status=0x%04h", 
                                       tag, trans.srcid, trans.dstid, trans.status), UVM_HIGH)
    
    // Validate TAG field for non-TAG mode
    if (!enable_tag_support && tag != 4'h0) begin
      `uvm_error("REG_CHECKER", $sformatf("TX completion TAG violation: expected 4'h0, got %0d in non-TAG mode", tag))
      tx_tag_violations++;
      protocol_errors++;
      return;
    end
    
    // Check if TAG support is enabled
    if (enable_tag_support) begin
      // Check if tag has corresponding RX-initiated request
      if (!rx_tag_in_use[tag]) begin
        `uvm_error("REG_CHECKER", $sformatf("TX completion tag %0d has no corresponding RX request!", tag))
        protocol_errors++;
        return;
      end
      
      // Validate request-completion matching
      if (!validate_completion(trans, rx_outstanding_requests[tag])) begin
        rx_tag_mismatches++;
        return;
      end
      
      // Calculate response time for RX-initiated request
      response_time = $realtime - rx_outstanding_requests[tag].req_time;
      update_rx_timing_statistics(response_time);
      
      // Mark RX tag as free
      rx_tag_in_use[tag] = 0;
      rx_completions_received++;
      rx_matched_transactions++;
      
              `uvm_info("REG_CHECKER", $sformatf("Matched RX→TX completion: tag=%0d, response_time=%.1fns", 
                                           tag, response_time/1ns), UVM_MEDIUM)
      end else begin
       // Non-TAG mode: Check if there's an outstanding RX request
       if (!rx_has_outstanding_request) begin
         `uvm_error("REG_CHECKER", $sformatf("TX completion with no outstanding RX request in non-TAG mode!"))
         protocol_errors++;
         return;
       end
       
       // Validate request-completion matching
       if (!validate_completion(trans, rx_single_outstanding_request)) begin
         rx_tag_mismatches++;
         return;
       end
       
       // Calculate response time for RX-initiated request
       response_time = $realtime - rx_single_outstanding_request.req_time;
       update_rx_timing_statistics(response_time);
       
       // Clear the single outstanding RX request
       rx_has_outstanding_request = 0;
       rx_completions_received++;
       rx_matched_transactions++;
       
       `uvm_info("REG_CHECKER", $sformatf("Matched single RX→TX completion: response_time=%.1fns", 
                                          response_time/1ns), UVM_MEDIUM)
     end
  endfunction
  
  // RX completion processing (response to TX-initiated request)
  virtual function void process_tx_completion(ucie_sb_transaction trans);
    bit [4:0] tag = trans.tag;
    realtime response_time;
    
    `uvm_info("REG_CHECKER", $sformatf("Processing RX completion (TX→RX response): tag=%0d, srcid=%0d, dstid=%0d, status=0x%04h", 
                                       tag, trans.srcid, trans.dstid, trans.status), UVM_HIGH)
    
    // Validate TAG field for non-TAG mode
    if (!enable_tag_support && tag != 4'h0) begin
      `uvm_error("REG_CHECKER", $sformatf("RX completion TAG violation: expected 4'h0, got %0d in non-TAG mode", tag))
      rx_tag_violations++;
      protocol_errors++;
      return;
    end
    
    // Check if TAG support is enabled
    if (enable_tag_support) begin
      // Check if tag has corresponding TX-initiated request
      if (!tx_tag_in_use[tag]) begin
        `uvm_error("REG_CHECKER", $sformatf("RX completion tag %0d has no corresponding TX request!", tag))
        protocol_errors++;
        return;
      end
      
      // Validate request-completion matching
      if (!validate_completion(trans, tx_outstanding_requests[tag])) begin
        tx_tag_mismatches++;
        return;
      end
      
      // Calculate response time for TX-initiated request
      response_time = $realtime - tx_outstanding_requests[tag].req_time;
      update_tx_timing_statistics(response_time);
      
      // Mark TX tag as free
      tx_tag_in_use[tag] = 0;
      tx_completions_received++;
      tx_matched_transactions++;
      
              `uvm_info("REG_CHECKER", $sformatf("Matched TX→RX completion: tag=%0d, response_time=%.1fns", 
                                           tag, response_time/1ns), UVM_MEDIUM)
      end else begin
       // Non-TAG mode: Check if there's an outstanding TX request
       if (!tx_has_outstanding_request) begin
         `uvm_error("REG_CHECKER", $sformatf("RX completion with no outstanding TX request in non-TAG mode!"))
         protocol_errors++;
         return;
       end
       
       // Validate request-completion matching
       if (!validate_completion(trans, tx_single_outstanding_request)) begin
         tx_tag_mismatches++;
         return;
       end
       
       // Calculate response time for TX-initiated request
       response_time = $realtime - tx_single_outstanding_request.req_time;
       update_tx_timing_statistics(response_time);
       
       // Clear the single outstanding TX request
       tx_has_outstanding_request = 0;
       tx_completions_received++;
       tx_matched_transactions++;
       
       `uvm_info("REG_CHECKER", $sformatf("Matched single TX→RX completion: response_time=%.1fns", 
                                          response_time/1ns), UVM_MEDIUM)
     end
  endfunction
  
  //=============================================================================
  // VALIDATION FUNCTIONS
  //=============================================================================
  
  virtual function bit is_register_access_request(ucie_sb_transaction trans);
    return (trans.pkt_type == PKT_REG_ACCESS && 
            (trans.opcode inside {MEM_READ_32B, MEM_WRITE_32B, DMS_READ_32B, DMS_WRITE_32B, 
                                  CFG_READ_32B, CFG_WRITE_32B, MEM_READ_64B, MEM_WRITE_64B, 
                                  DMS_READ_64B, DMS_WRITE_64B, CFG_READ_64B, CFG_WRITE_64B}));
  endfunction
  
  virtual function bit is_completion(ucie_sb_transaction trans);
    return (trans.pkt_type == PKT_COMPLETION && 
            (trans.opcode inside {COMPLETION_NO_DATA, COMPLETION_32B, COMPLETION_64B}));
  endfunction
  
  virtual function bit is_read_request(ucie_sb_transaction trans);
    return (trans.opcode inside {MEM_READ_32B, DMS_READ_32B, CFG_READ_32B, 
                                 MEM_READ_64B, DMS_READ_64B, CFG_READ_64B});
  endfunction
  
  virtual function bit validate_completion(ucie_sb_transaction comp, outstanding_req_t req);
    bit valid = 1;
    
    // Check srcid/dstid swap (completion returns to requester)
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
    
    // Check data size consistency for read completions
    if (req.is_read) begin
      bit expected_has_data = 1;
      bit expected_64bit = req.is_64bit;
      
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
  
  //=============================================================================
  // TIMEOUT MONITORING
  //=============================================================================
  
  virtual task timeout_monitor();
    realtime current_time;
    
    forever begin
      #(timeout_ns * 1ns / 10); // Check every 1/10 of timeout period
      
      current_time = $realtime;
      
      // Check TX-initiated request timeouts
      if (enable_tag_support) begin
        for (int tag = 0; tag < 32; tag++) begin
          if (tx_tag_in_use[tag]) begin
            if ((current_time - tx_outstanding_requests[tag].req_time) > (timeout_ns * 1ns)) begin
              `uvm_error("REG_CHECKER", $sformatf("TX request timeout: tag=%0d, addr=0x%06h, elapsed=%.1fns", 
                                                  tag, tx_outstanding_requests[tag].addr, 
                                                  (current_time - tx_outstanding_requests[tag].req_time)/1ns))
              tx_timeout_errors++;
              tx_tag_in_use[tag] = 0; // Clear timed-out request
            end
          end
        end
      end else begin
        if (tx_has_outstanding_request) begin
          if ((current_time - tx_single_outstanding_request.req_time) > (timeout_ns * 1ns)) begin
            `uvm_error("REG_CHECKER", $sformatf("Single TX request timeout: elapsed=%.1fns", 
                                                (current_time - tx_single_outstanding_request.req_time)/1ns))
            tx_timeout_errors++;
            tx_has_outstanding_request = 0; // Clear timed-out request
          end
        end
      end
      
      // Check RX-initiated request timeouts
      if (enable_tag_support) begin
        for (int tag = 0; tag < 32; tag++) begin
          if (rx_tag_in_use[tag]) begin
            if ((current_time - rx_outstanding_requests[tag].req_time) > (timeout_ns * 1ns)) begin
              `uvm_error("REG_CHECKER", $sformatf("RX request timeout: tag=%0d, addr=0x%06h, elapsed=%.1fns", 
                                                  tag, rx_outstanding_requests[tag].addr, 
                                                  (current_time - rx_outstanding_requests[tag].req_time)/1ns))
              rx_timeout_errors++;
              rx_tag_in_use[tag] = 0; // Clear timed-out request
            end
          end
        end
      end else begin
        if (rx_has_outstanding_request) begin
          if ((current_time - rx_single_outstanding_request.req_time) > (timeout_ns * 1ns)) begin
            `uvm_error("REG_CHECKER", $sformatf("Single RX request timeout: elapsed=%.1fns", 
                                                (current_time - rx_single_outstanding_request.req_time)/1ns))
            rx_timeout_errors++;
            rx_has_outstanding_request = 0; // Clear timed-out request
          end
        end
      end
    end
  endtask
  
  //=============================================================================
  // STATISTICS AND REPORTING
  //=============================================================================
  
  virtual function void update_tx_timing_statistics(realtime response_time);
    tx_total_response_time += response_time;
    
    if (tx_matched_transactions == 1) begin
      tx_min_response_time = response_time;
      tx_max_response_time = response_time;
    end else begin
      if (response_time < tx_min_response_time) tx_min_response_time = response_time;
      if (response_time > tx_max_response_time) tx_max_response_time = response_time;
    end
  endfunction
  
  virtual function void update_rx_timing_statistics(realtime response_time);
    rx_total_response_time += response_time;
    
    if (rx_matched_transactions == 1) begin
      rx_min_response_time = response_time;
      rx_max_response_time = response_time;
    end else begin
      if (response_time < rx_min_response_time) rx_min_response_time = response_time;
      if (response_time > rx_max_response_time) rx_max_response_time = response_time;
    end
  endfunction
  
  virtual function void print_statistics();
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
  
  virtual function void check_outstanding_requests();
    int tx_outstanding_count = 0;
    int rx_outstanding_count = 0;
    
    // Check TX-initiated outstanding requests
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
    
    // Check RX-initiated outstanding requests
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
  
  //=============================================================================
  // CONFIGURATION FUNCTIONS
  //=============================================================================
  
  virtual function void set_timeout(real timeout_ns_val);
    timeout_ns = timeout_ns_val;
    `uvm_info("REG_CHECKER", $sformatf("Set timeout to %.1fns", timeout_ns), UVM_LOW)
  endfunction
  
  virtual function void enable_timeout_checking(bit enable);
    enable_timeout_check = enable;
    `uvm_info("REG_CHECKER", $sformatf("Timeout checking %s", enable ? "enabled" : "disabled"), UVM_LOW)
  endfunction
  
  virtual function void set_tag_support(bit enable);
    enable_tag_support = enable;
    `uvm_info("REG_CHECKER", $sformatf("TAG support %s", enable ? "enabled" : "disabled"), UVM_LOW)
  endfunction
  
  virtual function void reset_statistics();
    // TX-initiated statistics
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
    
    // RX-initiated statistics
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
    
    // General statistics
    protocol_errors = 0;
    tx_transactions_queued = 0;
    rx_transactions_queued = 0;
    max_tx_fifo_depth = 0;
    max_rx_fifo_depth = 0;
    
    // Reset non-TAG mode tracking
    tx_has_outstanding_request = 0;
    rx_has_outstanding_request = 0;
    
    `uvm_info("REG_CHECKER", "Bidirectional statistics reset", UVM_LOW)
  endfunction
  
  //=============================================================================
  // FIFO MANAGEMENT FUNCTIONS
  //=============================================================================
  
  virtual function int get_tx_fifo_depth();
    return tx_fifo.size();
  endfunction
  
  virtual function int get_rx_fifo_depth();
    return rx_fifo.size();
  endfunction
  
  virtual function void flush_fifos();
    tx_fifo.flush();
    rx_fifo.flush();
    `uvm_info("REG_CHECKER", "FIFOs flushed", UVM_LOW)
  endfunction

endclass : ucie_sb_reg_access_checker