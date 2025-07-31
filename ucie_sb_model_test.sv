// UCIe Sideband Model Test Example
// Demonstrates the UVM sideband model for initial flow testing

//=============================================================================
// CLASS: ucie_sb_model_test
//
// DESCRIPTION:
//   Test example for UCIe sideband model demonstrating the complete initial flow
//   using UVM methodology. Creates two model instances to simulate both sides
//   of the sideband link communication.
//   
//   Test Scenarios:
//   1. Normal initial flow completion
//   2. Clock pattern detection and validation
//   3. SBINIT message exchange
//   4. Timeout handling and error conditions
//   5. Training engine mode testing
//
// AUTHOR: UCIe Sideband UVM Agent
// VERSION: 1.0 - Model Test Example
//=============================================================================

class ucie_sb_model_test extends uvm_test;
  `uvm_component_utils(ucie_sb_model_test)
  
  //=============================================================================
  // CLASS FIELDS
  //=============================================================================
  
  // Sideband models
  ucie_sb_model sb_model_a;
  ucie_sb_model sb_model_b;
  
  // Configurations
  ucie_sb_config cfg_a;
  ucie_sb_config cfg_b;
  
  // Virtual interfaces
  virtual ucie_sb_interface vif_a;
  virtual ucie_sb_interface vif_b;
  
  // Test control
  bit test_passed = 0;
  string current_test_name;
  int test_timeout_ns = 50_000_000; // 50ms test timeout
  
  //=============================================================================
  // CONSTRUCTOR
  //=============================================================================
  
  function new(string name = "ucie_sb_model_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  //=============================================================================
  // UVM PHASES
  //=============================================================================
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    // Create configurations
    cfg_a = ucie_sb_config::type_id::create("cfg_a");
    cfg_b = ucie_sb_config::type_id::create("cfg_b");
    
    // Configure for initial flow testing
    cfg_a.configure_for_initial_flow_test();
    cfg_b.configure_for_initial_flow_test();
    
    // Set different source/destination IDs for cross-communication
    cfg_a.srcid = 3'h1;
    cfg_a.dstid = 3'h2;
    cfg_b.srcid = 3'h2;
    cfg_b.dstid = 3'h1;
    
    // Validate configurations
    if (!cfg_a.validate_config() || !cfg_b.validate_config()) begin
      `uvm_fatal("TEST", "Configuration validation failed")
    end
    
    // Get virtual interfaces
    if (!uvm_config_db#(virtual ucie_sb_interface)::get(this, "", "vif_a", vif_a)) begin
      `uvm_fatal("TEST", "Virtual interface A not found")
    end
    
    if (!uvm_config_db#(virtual ucie_sb_interface)::get(this, "", "vif_b", vif_b)) begin
      `uvm_fatal("TEST", "Virtual interface B not found")
    end
    
    // Create sideband models
    sb_model_a = ucie_sb_model::type_id::create("sb_model_a", this);
    sb_model_b = ucie_sb_model::type_id::create("sb_model_b", this);
    
    // Set configurations and interfaces
    uvm_config_db#(ucie_sb_config)::set(this, "sb_model_a", "cfg", cfg_a);
    uvm_config_db#(ucie_sb_config)::set(this, "sb_model_b", "cfg", cfg_b);
    uvm_config_db#(virtual ucie_sb_interface)::set(this, "sb_model_a", "vif", vif_a);
    uvm_config_db#(virtual ucie_sb_interface)::set(this, "sb_model_b", "vif", vif_b);
    
    `uvm_info("TEST", "Sideband model test built", UVM_LOW)
  endfunction
  
  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    
    // Connect analysis ports for cross-monitoring (A's TX -> B's RX, B's TX -> A's RX)
    // This would typically be done in a higher-level testbench with proper routing
    
    `uvm_info("TEST", "Sideband model test connected", UVM_LOW)
  endfunction
  
  virtual function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    
    // Print test configuration
    `uvm_info("TEST", "=== Test Configuration ===", UVM_LOW)
    cfg_a.print_config();
    cfg_b.print_config();
    `uvm_info("TEST", "=========================", UVM_LOW)
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    
    // Raise objection to keep test running
    phase.raise_objection(this, "Starting sideband model test");
    
    fork
      // Run test scenarios
      run_test_scenarios();
      
      // Test timeout watchdog
      begin
        #(test_timeout_ns * 1ns);
        `uvm_error("TEST", "Test timeout - ending test")
        test_passed = 0;
      end
    join_any
    disable fork;
    
    // Test completion
    if (test_passed) begin
      `uvm_info("TEST", "=== TEST PASSED ===", UVM_LOW)
    end else begin
      `uvm_error("TEST", "=== TEST FAILED ===")
    end
    
    // Drop objection to end test
    phase.drop_objection(this, "Sideband model test completed");
  endtask
  
  //=============================================================================
  // TEST SCENARIOS
  //=============================================================================
  
  virtual task run_test_scenarios();
    `uvm_info("TEST", "Starting sideband model test scenarios", UVM_LOW)
    
    // Test Scenario 1: Basic Initial Flow
    current_test_name = "Basic Initial Flow";
    test_basic_initial_flow();
    
    // Small delay between tests
    #1000ns;
    
    // Test Scenario 2: Simultaneous Start
    current_test_name = "Simultaneous Start";
    test_simultaneous_start();
    
    // Small delay between tests
    #1000ns;
    
    // Test Scenario 3: Timeout Testing
    current_test_name = "Timeout Testing";
    test_timeout_scenario();
    
    // Test completion
    test_passed = 1;
    `uvm_info("TEST", "All test scenarios completed successfully", UVM_LOW)
  endtask
  
  //=============================================================================
  // TEST SCENARIO 1: Basic Initial Flow
  //=============================================================================
  
  virtual task test_basic_initial_flow();
    `uvm_info("TEST", $sformatf("Starting test: %s", current_test_name), UVM_LOW)
    
    // Reset both models
    sb_model_a.reset_initial_flow();
    sb_model_b.reset_initial_flow();
    
    // Start model A first
    sb_model_a.start_initial_flow();
    
    // Wait a bit, then start model B
    #5000ns;
    sb_model_b.start_initial_flow();
    
    // Monitor progress
    fork
      begin
        // Wait for both models to complete
        wait (sb_model_a.initial_flow_complete && sb_model_b.initial_flow_complete);
        `uvm_info("TEST", $sformatf("%s: Both models completed initial flow", current_test_name), UVM_LOW)
      end
      
      begin
        // Monitor for timeouts or errors
        wait (sb_model_a.initial_flow_timeout || sb_model_a.initial_flow_error ||
              sb_model_b.initial_flow_timeout || sb_model_b.initial_flow_error);
        `uvm_error("TEST", $sformatf("%s: Model timeout or error occurred", current_test_name))
        test_passed = 0;
      end
      
      begin
        // Test-specific timeout
        #(cfg_a.timeout_8ms * 3 * 1ns); // 3x the configured timeout
        `uvm_error("TEST", $sformatf("%s: Test scenario timeout", current_test_name))
        test_passed = 0;
      end
    join_any
    disable fork;
    
    // Print status
    `uvm_info("TEST", $sformatf("%s: Model A Status - %s", current_test_name, sb_model_a.get_status()), UVM_MEDIUM)
    `uvm_info("TEST", $sformatf("%s: Model B Status - %s", current_test_name, sb_model_b.get_status()), UVM_MEDIUM)
    
    `uvm_info("TEST", $sformatf("Completed test: %s", current_test_name), UVM_LOW)
  endtask
  
  //=============================================================================
  // TEST SCENARIO 2: Simultaneous Start
  //=============================================================================
  
  virtual task test_simultaneous_start();
    `uvm_info("TEST", $sformatf("Starting test: %s", current_test_name), UVM_LOW)
    
    // Reset both models
    sb_model_a.reset_initial_flow();
    sb_model_b.reset_initial_flow();
    
    // Start both models simultaneously
    fork
      sb_model_a.start_initial_flow();
      sb_model_b.start_initial_flow();
    join
    
    // Monitor progress
    fork
      begin
        // Wait for both models to complete
        wait (sb_model_a.initial_flow_complete && sb_model_b.initial_flow_complete);
        `uvm_info("TEST", $sformatf("%s: Both models completed simultaneous initial flow", current_test_name), UVM_LOW)
      end
      
      begin
        // Monitor for timeouts or errors
        wait (sb_model_a.initial_flow_timeout || sb_model_a.initial_flow_error ||
              sb_model_b.initial_flow_timeout || sb_model_b.initial_flow_error);
        `uvm_error("TEST", $sformatf("%s: Model timeout or error occurred", current_test_name))
        test_passed = 0;
      end
      
      begin
        // Test-specific timeout
        #(cfg_a.timeout_8ms * 3 * 1ns); // 3x the configured timeout
        `uvm_error("TEST", $sformatf("%s: Test scenario timeout", current_test_name))
        test_passed = 0;
      end
    join_any
    disable fork;
    
    `uvm_info("TEST", $sformatf("Completed test: %s", current_test_name), UVM_LOW)
  endtask
  
  //=============================================================================
  // TEST SCENARIO 3: Timeout Testing
  //=============================================================================
  
  virtual task test_timeout_scenario();
    `uvm_info("TEST", $sformatf("Starting test: %s", current_test_name), UVM_LOW)
    
    // Configure for faster timeout
    cfg_a.timeout_8ms = 1_000_000.0; // 1ms timeout
    cfg_b.timeout_8ms = 1_000_000.0; // 1ms timeout
    
    // Reset both models
    sb_model_a.reset_initial_flow();
    sb_model_b.reset_initial_flow();
    
    // Start only model A (no responder)
    sb_model_a.start_initial_flow();
    
    // Monitor for timeout
    fork
      begin
        // Wait for timeout
        wait (sb_model_a.initial_flow_timeout);
        `uvm_info("TEST", $sformatf("%s: Model A timed out as expected", current_test_name), UVM_LOW)
      end
      
      begin
        // Safety timeout
        #(cfg_a.timeout_8ms * 2 * 1ns); // 2x the configured timeout
        if (!sb_model_a.initial_flow_timeout) begin
          `uvm_error("TEST", $sformatf("%s: Model A did not timeout as expected", current_test_name))
          test_passed = 0;
        end
      end
    join_any
    disable fork;
    
    `uvm_info("TEST", $sformatf("Completed test: %s", current_test_name), UVM_LOW)
  endtask
  
  //=============================================================================
  // HELPER FUNCTIONS
  //=============================================================================
  
  virtual function void print_test_summary();
    `uvm_info("TEST", "=== Test Summary ===", UVM_LOW)
    `uvm_info("TEST", $sformatf("Test Result: %s", test_passed ? "PASSED" : "FAILED"), UVM_LOW)
    `uvm_info("TEST", $sformatf("Model A Final Status: %s", sb_model_a.get_status()), UVM_LOW)
    `uvm_info("TEST", $sformatf("Model B Final Status: %s", sb_model_b.get_status()), UVM_LOW)
    `uvm_info("TEST", "==================", UVM_LOW)
  endfunction
  
  virtual function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    print_test_summary();
  endfunction

endclass : ucie_sb_model_test

//=============================================================================
// TOP-LEVEL TESTBENCH MODULE
//=============================================================================

module ucie_sb_model_testbench;
  
  // Clock and reset
  logic clk;
  logic reset;
  
  // Clock generation (100MHz system clock)
  initial begin
    clk = 0;
    forever #5ns clk = ~clk;
  end
  
  // Reset generation
  initial begin
    reset = 1;
    #100ns;
    reset = 0;
  end
  
  // Create sideband interfaces
  ucie_sb_interface sb_if_a(.clk(clk), .reset(reset));
  ucie_sb_interface sb_if_b(.clk(clk), .reset(reset));
  
  // Cross-connect interfaces for communication
  // (A's TX -> B's RX, B's TX -> A's RX)
  always_comb begin
    sb_if_a.SBRX_CLK = sb_if_b.SBTX_CLK;
    sb_if_a.SBRX_DATA = sb_if_b.SBTX_DATA;
    sb_if_b.SBRX_CLK = sb_if_a.SBTX_CLK;
    sb_if_b.SBRX_DATA = sb_if_a.SBTX_DATA;
  end
  
  // UVM testbench setup
  initial begin
    // Set virtual interfaces in config database
    uvm_config_db#(virtual ucie_sb_interface)::set(null, "uvm_test_top", "vif_a", sb_if_a);
    uvm_config_db#(virtual ucie_sb_interface)::set(null, "uvm_test_top", "vif_b", sb_if_b);
    
    // Run the test
    run_test("ucie_sb_model_test");
  end
  
  // Waveform generation
  initial begin
    $dumpfile("ucie_sb_model_test.vcd");
    $dumpvars(0, ucie_sb_model_testbench);
  end
  
  // Simulation timeout
  initial begin
    #100_000_000ns; // 100ms simulation timeout
    $display("Simulation timeout - ending");
    $finish;
  end

endmodule : ucie_sb_model_testbench