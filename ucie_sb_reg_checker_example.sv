// UCIe Sideband Register Access Checker Example
// Demonstrates how to integrate and use the register access checker

module ucie_sb_reg_checker_example;
  import uvm_pkg::*;
  import ucie_sb_pkg::*;
  `include "uvm_macros.svh"
  `include "ucie_sb_reg_access_checker.sv"
  
  // Clock and reset
  logic clk = 0;
  logic reset = 1;
  
  // Generate clock
  always #2.5ns clk = ~clk; // 200MHz system clock
  
  // Reset sequence
  initial begin
    reset = 1;
    #100ns;
    reset = 0;
  end
  
  // Interface instantiation
  ucie_sb_interface sb_intf(.clk(clk), .reset(reset));
  
  // Clock generation for sideband
  always #0.625ns sb_intf.SBTX_CLK = ~sb_intf.SBTX_CLK; // 800MHz
  always #0.625ns sb_intf.SBRX_CLK = ~sb_intf.SBRX_CLK; // 800MHz
  
  initial begin
    sb_intf.SBTX_CLK = 0;
    sb_intf.SBRX_CLK = 0;
    sb_intf.SBTX_DATA = 0;
    sb_intf.SBRX_DATA = 0;
  end
  
  //=============================================================================
  // Test Environment with Register Access Checker
  //=============================================================================
  
  class reg_checker_env extends uvm_env;
    `uvm_component_utils(reg_checker_env)
    
    // Components
    ucie_sb_agent tx_agent;
    ucie_sb_agent rx_agent;
    ucie_sb_reg_access_checker reg_checker;
    
    function new(string name = "reg_checker_env", uvm_component parent = null);
      super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      
      // Create agents
      tx_agent = ucie_sb_agent::type_id::create("tx_agent", this);
      rx_agent = ucie_sb_agent::type_id::create("rx_agent", this);
      
      // Create register access checker
      reg_checker = ucie_sb_reg_access_checker::type_id::create("reg_checker", this);
      
      // Configure agents
      uvm_config_db#(uvm_active_passive_enum)::set(this, "tx_agent", "is_active", UVM_ACTIVE);
      uvm_config_db#(uvm_active_passive_enum)::set(this, "rx_agent", "is_active", UVM_PASSIVE);
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      
      // Connect TX agent monitor to checker TX port
      tx_agent.ap.connect(reg_checker.tx_imp);
      
      // Connect RX agent monitor to checker RX port
      rx_agent.ap.connect(reg_checker.rx_imp);
      
      `uvm_info("ENV", "Register access checker connections established", UVM_LOW)
    endfunction
  endclass
  
  //=============================================================================
  // Register Access Test Sequence
  //=============================================================================
  
  class reg_access_test_seq extends ucie_sb_base_sequence;
    `uvm_object_utils(reg_access_test_seq)
    
    rand int num_transactions = 10;
    constraint num_trans_c { num_transactions inside {[5:20]}; }
    
    function new(string name = "reg_access_test_seq");
      super.new(name);
    endfunction
    
    virtual task body();
      ucie_sb_transaction req_trans, comp_trans;
      
      `uvm_info("REG_TEST_SEQ", $sformatf("Starting %0d register access transactions", num_transactions), UVM_LOW)
      
      for (int i = 0; i < num_transactions; i++) begin
        // Create register read request
        req_trans = ucie_sb_transaction::type_id::create($sformatf("req_%0d", i));
        start_item(req_trans);
        assert(req_trans.randomize() with {
          opcode inside {MEM_READ_32B, MEM_READ_64B, CFG_READ_32B, CFG_READ_64B};
          tag == i % 32; // Use different tags
          srcid == 3'b001; // D2D Adapter
          dstid == 3'b000; // Local die
          addr inside {[24'h100000:24'h1FFFFF]}; // Valid address range
        });
        finish_item(req_trans);
        
        `uvm_info("REG_TEST_SEQ", $sformatf("Sent request %0d: tag=%0d, addr=0x%06h", 
                                            i, req_trans.tag, req_trans.addr), UVM_MEDIUM)
        
        // Add some delay between requests
        #(($urandom_range(1, 5)) * 10ns);
        
        // Simulate completion (in real test, this would come from DUT)
        fork
          begin
            // Random delay for completion
            #(($urandom_range(50, 200)) * 1ns);
            
            // Create matching completion
            comp_trans = create_completion(req_trans);
            
            // Send completion on RX side (simulate DUT response)
            send_completion_on_rx(comp_trans);
            
            `uvm_info("REG_TEST_SEQ", $sformatf("Sent completion %0d: tag=%0d", 
                                                i, comp_trans.tag), UVM_MEDIUM)
          end
        join_none
      end
      
      // Wait for all completions
      #1000ns;
      
      `uvm_info("REG_TEST_SEQ", "Register access test sequence completed", UVM_LOW)
    endtask
    
    virtual function ucie_sb_transaction create_completion(ucie_sb_transaction req);
      ucie_sb_transaction comp = ucie_sb_transaction::type_id::create("completion");
      
      // Set completion fields based on request
      comp.opcode = req.is_64bit ? COMPLETION_64B : COMPLETION_32B;
      comp.pkt_type = PKT_COMPLETION;
      comp.tag = req.tag;
      comp.srcid = req.dstid; // Swap: responder becomes sender
      comp.dstid = req.srcid; // Swap: requester becomes destination
      comp.status = 16'h0000; // Success
      comp.has_data = 1; // Read completion has data
      comp.is_64bit = req.is_64bit;
      comp.data = $urandom_range(0, 64'hFFFFFFFFFFFFFFFF); // Random data
      
      return comp;
    endfunction
    
    virtual task send_completion_on_rx(ucie_sb_transaction comp);
      // In a real testbench, this would be handled by the DUT
      // For this example, we'll simulate it by directly calling the RX monitor
      // This is just for demonstration - normally completions come from DUT
      
      // Simulate the completion being received on RX side
      // (This would normally be done by the RX monitor detecting the completion)
      `uvm_info("REG_TEST_SEQ", "Simulating completion on RX side", UVM_HIGH)
    endtask
  endclass
  
  //=============================================================================
  // Test Case
  //=============================================================================
  
  class reg_checker_test extends uvm_test;
    `uvm_component_utils(reg_checker_test)
    
    reg_checker_env env;
    
    function new(string name = "reg_checker_test", uvm_component parent = null);
      super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      env = reg_checker_env::type_id::create("env", this);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
      reg_access_test_seq test_seq;
      
      phase.raise_objection(this);
      
      `uvm_info("TEST", "Starting register access checker test", UVM_LOW)
      
      // Configure checker
      env.reg_checker.set_timeout(500.0); // 500ns timeout
      env.reg_checker.enable_timeout_checking(1);
      
      // Run test sequence
      test_seq = reg_access_test_seq::type_id::create("test_seq");
      test_seq.start(env.tx_agent.sequencer);
      
      // Additional delay to let checker finish
      #2000ns;
      
      `uvm_info("TEST", "Register access checker test completed", UVM_LOW)
      
      phase.drop_objection(this);
    endtask
  endclass
  
  //=============================================================================
  // Testbench Setup
  //=============================================================================
  
  initial begin
    // Set interface in config DB
    uvm_config_db#(virtual ucie_sb_interface)::set(null, "*", "vif", sb_intf);
    
    // Run test
    run_test("reg_checker_test");
  end
  
  // Simple DUT simulation (for demonstration)
  // In real use, this would be your actual DUT
  initial begin
    forever begin
      @(posedge sb_intf.SBTX_CLK);
      // Simple loopback for demonstration
      sb_intf.SBRX_DATA <= sb_intf.SBTX_DATA;
    end
  end

endmodule

//=============================================================================
// Usage Instructions and Configuration Examples
//=============================================================================

/*

=== REGISTER ACCESS CHECKER USAGE ===

1. INSTANTIATION:
   ucie_sb_reg_access_checker reg_checker;
   reg_checker = ucie_sb_reg_access_checker::type_id::create("reg_checker", this);

2. CONNECTIONS:
   // Connect TX monitor to checker
   tx_agent.monitor.ap.connect(reg_checker.tx_imp);
   
   // Connect RX monitor to checker  
   rx_agent.monitor.ap.connect(reg_checker.rx_imp);

3. CONFIGURATION:
   reg_checker.set_timeout(1000.0);           // 1us timeout
   reg_checker.enable_timeout_checking(1);    // Enable timeout
   reg_checker.enable_statistics = 1;         // Enable stats

4. WHAT IT CHECKS:
   - TX register access requests are matched with RX completions
   - Tag consistency (same tag used for request and completion)
   - Source/destination ID swapping (completion returns to requester)
   - Data size consistency for read operations
   - Timeout detection for missing completions
   - Protocol compliance (no duplicate tags, proper opcodes)

5. STATISTICS REPORTED:
   - Number of requests sent
   - Number of completions received  
   - Number of matched transactions
   - Tag mismatches and protocol errors
   - Response time statistics (min/max/average)
   - Timeout errors

6. ERROR DETECTION:
   - Missing completions (timeout)
   - Unexpected completions (no matching request)
   - Tag reuse before completion
   - Source/destination ID mismatches
   - Data size mismatches for reads

=== INTEGRATION WITH EXISTING TESTBENCH ===

// In your environment's connect_phase:
virtual function void connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  
  // Existing connections
  tx_agent.monitor.ap.connect(scoreboard.tx_imp);
  rx_agent.monitor.ap.connect(scoreboard.rx_imp);
  
  // Add register access checker
  tx_agent.monitor.ap.connect(reg_checker.tx_imp);
  rx_agent.monitor.ap.connect(reg_checker.rx_imp);
endfunction

*/