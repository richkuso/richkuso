// UCIe Sideband Register Access Checker Usage Example
// Demonstrates FIFO-only architecture and TAG/non-TAG modes

//=============================================================================
// ARCHITECTURE COMPARISON: Before vs After
//=============================================================================

/*
BEFORE (Analysis Port Wrappers - DEPRECATED):
┌─────────────┐    ┌─────────────┐    ┌─────────────┐    ┌─────────────┐
│ TX Monitor  │───▶│ tx_imp      │───▶│ write_tx()  │───▶│ tx_fifo     │
└─────────────┘    │ (Analysis   │    │ (Function)  │    │ (TLM FIFO)  │
                   │  Import)    │    └─────────────┘    └─────────────┘
                   └─────────────┘

AFTER (FIFO-Only - RECOMMENDED):
┌─────────────┐    ┌─────────────┐
│ TX Monitor  │───▶│ tx_fifo     │
└─────────────┘    │.analysis_   │
                   │ export      │
                   └─────────────┘

Benefits:
✅ 50% fewer components (removed analysis imports + wrapper functions)
✅ Direct connection - no function call overhead  
✅ Simpler architecture - easier to understand and debug
✅ Better performance - one less data copy operation
✅ Cleaner testbench connections
*/

//=============================================================================
// USAGE EXAMPLE: FIFO-Only Architecture with TAG Support Configuration
//=============================================================================

class my_test extends uvm_test;
  `uvm_component_utils(my_test)
  
  ucie_sb_reg_access_checker checker;
  ucie_sb_agent tx_agent;
  ucie_sb_agent rx_agent;
  
  function new(string name = "my_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    // Create agents and checker
    tx_agent = ucie_sb_agent::type_id::create("tx_agent", this);
    rx_agent = ucie_sb_agent::type_id::create("rx_agent", this);
    checker = ucie_sb_reg_access_checker::type_id::create("checker", this);
    
    // Example 1: Enable TAG support (default mode)
    // In this mode, up to 32 outstanding requests per direction are supported
    // Each request must have a unique 5-bit TAG value
    checker.set_tag_support(1);
    
    // Example 2: Disable TAG support (blocking mode)  
    // In this mode, only one outstanding request per direction is allowed
    // TAG field must be 4'h0 for all requests and completions
    // checker.set_tag_support(0);
    
    // Optional: Configure timeout checking
    checker.set_timeout(2000.0); // 2us timeout
    checker.enable_timeout_checking(1);
  endfunction
  
  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    
    // ===================================================================
    // FIFO-Only Architecture: Direct Monitor-to-FIFO Connections
    // ===================================================================
    
    // Connect TX monitor directly to checker's TX FIFO
    // This replaces the old: tx_monitor.ap.connect(checker.tx_imp)
    tx_agent.monitor.ap.connect(checker.tx_fifo.analysis_export);
    
    // Connect RX monitor directly to checker's RX FIFO  
    // This replaces the old: rx_monitor.ap.connect(checker.rx_imp)
    rx_agent.monitor.ap.connect(checker.rx_fifo.analysis_export);
    
    `uvm_info("TEST", "=== FIFO-Only Architecture Connected ===", UVM_LOW)
    `uvm_info("TEST", "TX Monitor → checker.tx_fifo.analysis_export", UVM_LOW)
    `uvm_info("TEST", "RX Monitor → checker.rx_fifo.analysis_export", UVM_LOW)
    `uvm_info("TEST", "No analysis port wrappers needed!", UVM_LOW)
  endfunction
  
  virtual function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    
    `uvm_info("TEST", "=== Configuration Summary ===", UVM_LOW)
    `uvm_info("TEST", $sformatf("TAG Support: %s", 
              checker.enable_tag_support ? "ENABLED" : "DISABLED"), UVM_LOW)
    
    if (checker.enable_tag_support) begin
      `uvm_info("TEST", "- Multiple outstanding requests supported (up to 32 per direction)", UVM_LOW)
      `uvm_info("TEST", "- TAG field must be unique for outstanding requests", UVM_LOW)
      `uvm_info("TEST", "- TAG field can be any 5-bit value (0-31)", UVM_LOW)
    end else begin
      `uvm_info("TEST", "- Only one outstanding request per direction allowed", UVM_LOW)
      `uvm_info("TEST", "- TAG field must be 4'h0 for all transactions", UVM_LOW)
      `uvm_info("TEST", "- New requests blocked until previous completes", UVM_LOW)
    end
  endfunction
  
endclass

//=============================================================================
// TRANSACTION EXAMPLES
//=============================================================================

// Example transactions for TAG mode
class tag_mode_example;
  
  // Valid TAG mode transactions
  static function void create_valid_tag_transactions();
    ucie_sb_transaction req1, req2, comp1, comp2;
    
    // Request 1 with TAG=5
    req1 = ucie_sb_transaction::type_id::create("req1");
    req1.pkt_type = PKT_REG_ACCESS;
    req1.opcode = MEM_READ_32B;
    req1.tag = 5;  // Valid unique tag
    req1.srcid = 1;
    req1.dstid = 2;
    req1.addr = 24'h123456;
    
    // Request 2 with TAG=10 (different from req1)
    req2 = ucie_sb_transaction::type_id::create("req2");
    req2.pkt_type = PKT_REG_ACCESS;
    req2.opcode = MEM_WRITE_32B;
    req2.tag = 10; // Valid unique tag
    req2.srcid = 1;
    req2.dstid = 2;
    req2.addr = 24'h789ABC;
    
    // Completion for req1 (TAG=5)
    comp1 = ucie_sb_transaction::type_id::create("comp1");
    comp1.pkt_type = PKT_COMPLETION;
    comp1.opcode = COMPLETION_32B;
    comp1.tag = 5;  // Must match req1.tag
    comp1.srcid = 2; // Swapped from req1.dstid
    comp1.dstid = 1; // Swapped from req1.srcid
    
    // Completion for req2 (TAG=10)
    comp2 = ucie_sb_transaction::type_id::create("comp2");
    comp2.pkt_type = PKT_COMPLETION;
    comp2.opcode = COMPLETION_NO_DATA;
    comp2.tag = 10; // Must match req2.tag
    comp2.srcid = 2; // Swapped from req2.dstid
    comp2.dstid = 1; // Swapped from req2.srcid
  endfunction
  
endclass

// Example transactions for non-TAG mode
class non_tag_mode_example;
  
  // Valid non-TAG mode transactions
  static function void create_valid_non_tag_transactions();
    ucie_sb_transaction req1, comp1, req2, comp2;
    
    // Request 1 with TAG=0 (required in non-TAG mode)
    req1 = ucie_sb_transaction::type_id::create("req1");
    req1.pkt_type = PKT_REG_ACCESS;
    req1.opcode = MEM_READ_32B;
    req1.tag = 0;  // Must be 4'h0 in non-TAG mode
    req1.srcid = 1;
    req1.dstid = 2;
    req1.addr = 24'h123456;
    
    // Completion for req1 (TAG=0)
    comp1 = ucie_sb_transaction::type_id::create("comp1");
    comp1.pkt_type = PKT_COMPLETION;
    comp1.opcode = COMPLETION_32B;
    comp1.tag = 0;  // Must be 4'h0 in non-TAG mode
    comp1.srcid = 2; // Swapped from req1.dstid
    comp1.dstid = 1; // Swapped from req1.srcid
    
    // Request 2 can only be sent AFTER comp1 is received
    req2 = ucie_sb_transaction::type_id::create("req2");
    req2.pkt_type = PKT_REG_ACCESS;
    req2.opcode = MEM_WRITE_32B;
    req2.tag = 0;  // Must be 4'h0 in non-TAG mode
    req2.srcid = 1;
    req2.dstid = 2;
    req2.addr = 24'h789ABC;
    
    // Completion for req2 (TAG=0)
    comp2 = ucie_sb_transaction::type_id::create("comp2");
    comp2.pkt_type = PKT_COMPLETION;
    comp2.opcode = COMPLETION_NO_DATA;
    comp2.tag = 0;  // Must be 4'h0 in non-TAG mode
    comp2.srcid = 2; // Swapped from req2.dstid
    comp2.dstid = 1; // Swapped from req2.srcid
  endfunction
  
  // Invalid non-TAG mode transactions (will cause errors)
  static function void create_invalid_non_tag_transactions();
    ucie_sb_transaction bad_req, bad_comp;
    
    // BAD: Request with non-zero TAG in non-TAG mode
    bad_req = ucie_sb_transaction::type_id::create("bad_req");
    bad_req.pkt_type = PKT_REG_ACCESS;
    bad_req.opcode = MEM_READ_32B;
    bad_req.tag = 5;  // ERROR: Must be 0 in non-TAG mode
    bad_req.srcid = 1;
    bad_req.dstid = 2;
    bad_req.addr = 24'h123456;
    // This will trigger: "TX request TAG violation: expected 4'h0, got 5 in non-TAG mode"
    
    // BAD: Completion with non-zero TAG in non-TAG mode
    bad_comp = ucie_sb_transaction::type_id::create("bad_comp");
    bad_comp.pkt_type = PKT_COMPLETION;
    bad_comp.opcode = COMPLETION_32B;
    bad_comp.tag = 3;  // ERROR: Must be 0 in non-TAG mode
    bad_comp.srcid = 2;
    bad_comp.dstid = 1;
    // This will trigger: "RX completion TAG violation: expected 4'h0, got 3 in non-TAG mode"
  endfunction
  
endclass

//=============================================================================
// STATISTICS INTERPRETATION
//=============================================================================

/*
When TAG support is ENABLED:
- tx_tag_violations: Should be 0 (no TAG field violations)
- tx_blocking_violations: Should be 0 (no blocking violations)
- Multiple requests can be outstanding simultaneously
- TAG mismatches indicate protocol errors

When TAG support is DISABLED:
- tx_tag_violations: Counts non-zero TAG field violations
- tx_blocking_violations: Counts attempts to send requests while one is outstanding
- Only one request per direction can be outstanding
- Blocking behavior enforced automatically

Common statistics for both modes:
- tx_requests_sent: Total requests sent from TX side
- tx_completions_received: Total completions received on TX side
- tx_matched_transactions: Successfully matched request-completion pairs
- tx_timeout_errors: Requests that timed out waiting for completion
*/

//=============================================================================
// SIMPLE CONNECTION EXAMPLE
//=============================================================================

/*
For users who just want to see the basic connection pattern:

class simple_testbench extends uvm_test;
  ucie_sb_reg_access_checker checker;
  ucie_sb_monitor tx_monitor, rx_monitor;
  
  function void build_phase(uvm_phase phase);
    checker = ucie_sb_reg_access_checker::type_id::create("checker", this);
    tx_monitor = ucie_sb_monitor::type_id::create("tx_monitor", this);
    rx_monitor = ucie_sb_monitor::type_id::create("rx_monitor", this);
  endfunction
  
  function void connect_phase(uvm_phase phase);
    // Direct FIFO connections - that's it!
    tx_monitor.ap.connect(checker.tx_fifo.analysis_export);
    rx_monitor.ap.connect(checker.rx_fifo.analysis_export);
  endfunction
endclass
*/

//=============================================================================
// CONFIGURATION EXAMPLES
//=============================================================================

/*
// TAG Mode (Multiple Outstanding Requests)
checker.set_tag_support(1);           // Enable TAG support
checker.set_timeout(1000.0);          // 1μs timeout
checker.enable_timeout_checking(1);   // Enable timeout monitoring

// Non-TAG Mode (Blocking Behavior)  
checker.set_tag_support(0);           // Disable TAG support
checker.set_timeout(5000.0);          // 5μs timeout (longer for blocking)
checker.enable_timeout_checking(1);   // Enable timeout monitoring

// Performance Mode (Minimal Checking)
checker.enable_checking = 1;          // Keep checking enabled
checker.enable_timeout_check = 0;     // Disable timeout for speed
checker.enable_statistics = 1;        // Keep statistics

// Debug Mode (Maximum Visibility)
checker.enable_checking = 1;          // Full checking
checker.enable_timeout_check = 1;     // Timeout monitoring
checker.enable_statistics = 1;        // Full statistics
// Set UVM verbosity to UVM_DEBUG for detailed logs
*/