// UCIe Sideband Register Access Checker
// Monitors TX register access requests and matches with RX completions

//=============================================================================
// CLASS: ucie_sb_reg_access_checker
//
// DESCRIPTION:
//   Checker that monitors sideband TX side for register access requests and
//   RX side for corresponding completions. Ensures proper request-completion
//   pairing with correct tag matching and validates protocol compliance.
//
// FEATURES:
//   - Tracks outstanding register access requests by tag
//   - Matches requests with corresponding completions
//   - Validates tag consistency and completion ordering
//   - Supports timeout detection for missing completions
//   - Statistics collection and reporting
//   - Configurable checking parameters
//
// AUTHOR: UCIe Sideband UVM Agent
// VERSION: 1.0
//=============================================================================

class ucie_sb_reg_access_checker extends uvm_component;
  `uvm_component_utils(ucie_sb_reg_access_checker)
  
  //=============================================================================
  // CLASS FIELDS
  //=============================================================================
  
  // Analysis ports for receiving transactions
  uvm_analysis_imp_tx #(ucie_sb_transaction, ucie_sb_reg_access_checker) tx_imp;
  uvm_analysis_imp_rx #(ucie_sb_transaction, ucie_sb_reg_access_checker) rx_imp;
  
  // Configuration parameters
  bit enable_checking = 1;
  bit enable_timeout_check = 1;
  real timeout_ns = 1000.0;  // 1us timeout for completions
  bit enable_statistics = 1;
  
  // Outstanding request tracking
  typedef struct {
    ucie_sb_transaction req_trans;
    realtime req_time;
    bit [2:0] srcid;
    bit [2:0] dstid;
    bit [23:0] addr;
    bit is_read;
    bit is_64bit;
  } outstanding_req_t;
  
  // Tag-based request tracking (5-bit tag = 32 entries)
  outstanding_req_t outstanding_requests[32];
  bit tag_in_use[32];
  
  // Statistics
  int requests_sent = 0;
  int completions_received = 0;
  int matched_transactions = 0;
  int tag_mismatches = 0;
  int timeout_errors = 0;
  int protocol_errors = 0;
  
  // Timing tracking
  realtime total_response_time = 0;
  realtime min_response_time = 0;
  realtime max_response_time = 0;
  
  //=============================================================================
  // CONSTRUCTOR
  //=============================================================================
  
  function new(string name = "ucie_sb_reg_access_checker", uvm_component parent = null);
    super.new(name, parent);
    
    // Initialize tracking arrays
    for (int i = 0; i < 32; i++) begin
      tag_in_use[i] = 0;
    end
  endfunction
  
  //=============================================================================
  // UVM PHASES
  //=============================================================================
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    // Create analysis imports
    tx_imp = new("tx_imp", this);
    rx_imp = new("rx_imp", this);
    
    `uvm_info("REG_CHECKER", "Register access checker built", UVM_LOW)
  endfunction
  
  virtual function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    
    `uvm_info("REG_CHECKER", $sformatf("Configuration: enable_checking=%0b, timeout=%.1fns", 
                                       enable_checking, timeout_ns), UVM_LOW)
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    if (enable_timeout_check) begin
      fork
        timeout_monitor();
      join_none
    end
  endtask
  
  virtual function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    print_statistics();
    check_outstanding_requests();
  endfunction
  
  //=============================================================================
  // ANALYSIS IMPORT IMPLEMENTATIONS
  //=============================================================================
  
  // TX side analysis - monitor register access requests
  virtual function void write_tx(ucie_sb_transaction trans);
    if (!enable_checking) return;
    
    // Check if this is a register access request
    if (is_register_access_request(trans)) begin
      process_request(trans);
    end
  endfunction
  
  // RX side analysis - monitor completions
  virtual function void write_rx(ucie_sb_transaction trans);
    if (!enable_checking) return;
    
    // Check if this is a completion
    if (is_completion(trans)) begin
      process_completion(trans);
    end
  endfunction
  
  //=============================================================================
  // REQUEST/COMPLETION PROCESSING
  //=============================================================================
  
  virtual function void process_request(ucie_sb_transaction trans);
    bit [4:0] tag = trans.tag;
    
    `uvm_info("REG_CHECKER", $sformatf("Processing request: opcode=%s, tag=%0d, addr=0x%06h", 
                                       trans.opcode.name(), tag, trans.addr), UVM_HIGH)
    
    // Check if tag is already in use
    if (tag_in_use[tag]) begin
      `uvm_error("REG_CHECKER", $sformatf("Tag %0d already in use! Previous request not completed", tag))
      protocol_errors++;
      return;
    end
    
    // Store request information
    outstanding_requests[tag].req_trans = trans;
    outstanding_requests[tag].req_time = $realtime;
    outstanding_requests[tag].srcid = trans.srcid;
    outstanding_requests[tag].dstid = trans.dstid;
    outstanding_requests[tag].addr = trans.addr;
    outstanding_requests[tag].is_read = is_read_request(trans);
    outstanding_requests[tag].is_64bit = trans.is_64bit;
    tag_in_use[tag] = 1;
    
    requests_sent++;
    
    `uvm_info("REG_CHECKER", $sformatf("Stored request: tag=%0d, srcid=%0d→dstid=%0d, addr=0x%06h, read=%0b", 
                                       tag, trans.srcid, trans.dstid, trans.addr, outstanding_requests[tag].is_read), UVM_MEDIUM)
  endfunction
  
  virtual function void process_completion(ucie_sb_transaction trans);
    bit [4:0] tag = trans.tag;
    realtime response_time;
    
    `uvm_info("REG_CHECKER", $sformatf("Processing completion: tag=%0d, srcid=%0d, dstid=%0d, status=0x%04h", 
                                       tag, trans.srcid, trans.dstid, trans.status), UVM_HIGH)
    
    // Check if tag has corresponding request
    if (!tag_in_use[tag]) begin
      `uvm_error("REG_CHECKER", $sformatf("Completion tag %0d has no corresponding request!", tag))
      protocol_errors++;
      return;
    end
    
    // Validate request-completion matching
    if (!validate_completion(trans, outstanding_requests[tag])) begin
      tag_mismatches++;
      return;
    end
    
    // Calculate response time
    response_time = $realtime - outstanding_requests[tag].req_time;
    update_timing_statistics(response_time);
    
    // Mark tag as free
    tag_in_use[tag] = 0;
    completions_received++;
    matched_transactions++;
    
    `uvm_info("REG_CHECKER", $sformatf("Matched completion: tag=%0d, response_time=%.1fns", 
                                       tag, response_time/1ns), UVM_MEDIUM)
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
      
      for (int tag = 0; tag < 32; tag++) begin
        if (tag_in_use[tag]) begin
          if ((current_time - outstanding_requests[tag].req_time) > (timeout_ns * 1ns)) begin
            `uvm_error("REG_CHECKER", $sformatf("Request timeout: tag=%0d, addr=0x%06h, elapsed=%.1fns", 
                                                tag, outstanding_requests[tag].addr, 
                                                (current_time - outstanding_requests[tag].req_time)/1ns))
            timeout_errors++;
            tag_in_use[tag] = 0; // Clear timed-out request
          end
        end
      end
    end
  endtask
  
  //=============================================================================
  // STATISTICS AND REPORTING
  //=============================================================================
  
  virtual function void update_timing_statistics(realtime response_time);
    total_response_time += response_time;
    
    if (matched_transactions == 1) begin
      min_response_time = response_time;
      max_response_time = response_time;
    end else begin
      if (response_time < min_response_time) min_response_time = response_time;
      if (response_time > max_response_time) max_response_time = response_time;
    end
  endfunction
  
  virtual function void print_statistics();
    realtime avg_response_time;
    
    if (!enable_statistics) return;
    
    `uvm_info("REG_CHECKER", "=== Register Access Checker Statistics ===", UVM_LOW)
    `uvm_info("REG_CHECKER", $sformatf("Requests sent: %0d", requests_sent), UVM_LOW)
    `uvm_info("REG_CHECKER", $sformatf("Completions received: %0d", completions_received), UVM_LOW)
    `uvm_info("REG_CHECKER", $sformatf("Matched transactions: %0d", matched_transactions), UVM_LOW)
    `uvm_info("REG_CHECKER", $sformatf("Tag mismatches: %0d", tag_mismatches), UVM_LOW)
    `uvm_info("REG_CHECKER", $sformatf("Timeout errors: %0d", timeout_errors), UVM_LOW)
    `uvm_info("REG_CHECKER", $sformatf("Protocol errors: %0d", protocol_errors), UVM_LOW)
    
    if (matched_transactions > 0) begin
      avg_response_time = total_response_time / matched_transactions;
      `uvm_info("REG_CHECKER", $sformatf("Response time - Min: %.1fns, Max: %.1fns, Avg: %.1fns", 
                                         min_response_time/1ns, max_response_time/1ns, avg_response_time/1ns), UVM_LOW)
    end
    
    `uvm_info("REG_CHECKER", "==========================================", UVM_LOW)
  endfunction
  
  virtual function void check_outstanding_requests();
    int outstanding_count = 0;
    
    for (int tag = 0; tag < 32; tag++) begin
      if (tag_in_use[tag]) begin
        outstanding_count++;
        `uvm_warning("REG_CHECKER", $sformatf("Outstanding request at end of test: tag=%0d, addr=0x%06h", 
                                              tag, outstanding_requests[tag].addr))
      end
    end
    
    if (outstanding_count > 0) begin
      `uvm_error("REG_CHECKER", $sformatf("%0d requests remain outstanding at end of test", outstanding_count))
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
  
  virtual function void reset_statistics();
    requests_sent = 0;
    completions_received = 0;
    matched_transactions = 0;
    tag_mismatches = 0;
    timeout_errors = 0;
    protocol_errors = 0;
    total_response_time = 0;
    min_response_time = 0;
    max_response_time = 0;
    `uvm_info("REG_CHECKER", "Statistics reset", UVM_LOW)
  endfunction

endclass : ucie_sb_reg_access_checker