/*******************************************************************************
 * UCIe Sideband Link Training State Machine (LTSM) Example
 * 
 * OVERVIEW:
 *   Demonstration environment showing how to use the UCIe LTSM model for
 *   link training from RESET state to SBINIT state. Shows both initiator
 *   and target configurations with complete UVM integration.
 *
 * FEATURES:
 *   • Dual-agent setup (initiator and target)
 *   • Complete LTSM sequence demonstration
 *   • Comprehensive logging and analysis
 *   • UCIe 1.1 specification compliance
 *
 * USAGE:
 *   This example can be compiled and run to demonstrate the complete
 *   UCIe sideband link training sequence using the FSM-based model.
 *
 * AUTHOR: UCIe Sideband UVM Agent
 * VERSION: 1.0 - LTSM Example Implementation
 ******************************************************************************/

//=============================================================================
// LTSM Example Environment
//=============================================================================

class ucie_sb_ltsm_env extends uvm_env;
  `uvm_component_utils(ucie_sb_ltsm_env)
  
  // LTSM models for both sides
  ucie_sb_ltsm_model initiator_ltsm;
  ucie_sb_ltsm_model target_ltsm;
  
  // Virtual interfaces
  virtual ucie_sb_inf initiator_vif;
  virtual ucie_sb_inf target_vif;
  
  function new(string name = "ucie_sb_ltsm_env", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    // Get virtual interfaces
    if (!uvm_config_db#(virtual ucie_sb_inf)::get(this, "", "initiator_vif", initiator_vif)) begin
      `uvm_fatal("LTSM_ENV", "Initiator virtual interface not found")
    end
    
    if (!uvm_config_db#(virtual ucie_sb_inf)::get(this, "", "target_vif", target_vif)) begin
      `uvm_fatal("LTSM_ENV", "Target virtual interface not found")
    end
    
    // Create LTSM models
    initiator_ltsm = ucie_sb_ltsm_model::type_id::create("initiator_ltsm", this);
    target_ltsm = ucie_sb_ltsm_model::type_id::create("target_ltsm", this);
    
    // Configure initiator
    initiator_ltsm.is_initiator = 1;
    initiator_ltsm.enable_debug = 1;
    uvm_config_db#(virtual ucie_sb_inf)::set(this, "initiator_ltsm", "vif", initiator_vif);
    
    // Configure target
    target_ltsm.is_initiator = 0;
    target_ltsm.enable_debug = 1;
    uvm_config_db#(virtual ucie_sb_inf)::set(this, "target_ltsm", "vif", target_vif);
    
    `uvm_info("LTSM_ENV", "LTSM environment build phase complete", UVM_LOW)
  endfunction
  
  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    `uvm_info("LTSM_ENV", "LTSM environment connect phase complete", UVM_LOW)
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    
    `uvm_info("LTSM_ENV", "Starting UCIe LTSM link training demonstration", UVM_LOW)
    
    // Wait for both sides to complete training
    fork
      wait(initiator_ltsm.current_state == LTSM_ACTIVE || initiator_ltsm.current_state == LTSM_ERROR);
      wait(target_ltsm.current_state == LTSM_ACTIVE || target_ltsm.current_state == LTSM_ERROR);
    join
    
    // Check results
    if (initiator_ltsm.current_state == LTSM_ACTIVE && target_ltsm.current_state == LTSM_ACTIVE) begin
      `uvm_info("LTSM_ENV", "*** LTSM TRAINING SUCCESSFUL! ***", UVM_LOW)
      `uvm_info("LTSM_ENV", "Both initiator and target completed training to ACTIVE state", UVM_LOW)
    end else begin
      `uvm_error("LTSM_ENV", "*** LTSM TRAINING FAILED! ***")
      `uvm_error("LTSM_ENV", $sformatf("Initiator state: %s, Target state: %s", 
                 initiator_ltsm.current_state.name(), target_ltsm.current_state.name()))
    end
    
    print_training_summary();
  endtask
  
  virtual function void print_training_summary();
    `uvm_info("LTSM_ENV", "=== LTSM TRAINING SUMMARY ===", UVM_LOW)
    `uvm_info("LTSM_ENV", "Initiator Statistics:", UVM_LOW)
    initiator_ltsm.print_final_statistics();
    `uvm_info("LTSM_ENV", "Target Statistics:", UVM_LOW)
    target_ltsm.print_final_statistics();
    `uvm_info("LTSM_ENV", "=============================", UVM_LOW)
  endfunction
  
endclass : ucie_sb_ltsm_env

//=============================================================================
// LTSM Example Test
//=============================================================================

class ucie_sb_ltsm_test extends uvm_test;
  `uvm_component_utils(ucie_sb_ltsm_test)
  
  ucie_sb_ltsm_env env;
  
  function new(string name = "ucie_sb_ltsm_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    env = ucie_sb_ltsm_env::type_id::create("env", this);
    
    `uvm_info("LTSM_TEST", "LTSM test build phase complete", UVM_LOW)
  endfunction
  
  virtual function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    
    `uvm_info("LTSM_TEST", "=== UCIe LTSM Test Configuration ===", UVM_LOW)
    `uvm_info("LTSM_TEST", "Test: UCIe Sideband Link Training State Machine", UVM_LOW)
    `uvm_info("LTSM_TEST", "Sequence: RESET → DETECT → POLLING → CONFIG → SBINIT", UVM_LOW)
    `uvm_info("LTSM_TEST", "Roles: Initiator and Target", UVM_LOW)
    `uvm_info("LTSM_TEST", "Compliance: UCIe 1.1 specification", UVM_LOW)
    `uvm_info("LTSM_TEST", "===================================", UVM_LOW)
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    
    phase.raise_objection(this);
    
    `uvm_info("LTSM_TEST", "Starting LTSM training test", UVM_LOW)
    
    // Reset sequence
    reset_sequence();
    
    // Wait for training completion (timeout after 100ms)
    fork
      begin
        #100ms;
        `uvm_error("LTSM_TEST", "Test timeout - training did not complete within 100ms")
      end
      begin
        wait(env.initiator_ltsm.current_state == LTSM_ACTIVE || env.initiator_ltsm.current_state == LTSM_ERROR);
        wait(env.target_ltsm.current_state == LTSM_ACTIVE || env.target_ltsm.current_state == LTSM_ERROR);
      end
    join_any
    disable fork;
    
    `uvm_info("LTSM_TEST", "LTSM training test completed", UVM_LOW)
    
    phase.drop_objection(this);
  endtask
  
  virtual task reset_sequence();
    `uvm_info("LTSM_TEST", "Applying reset sequence", UVM_MEDIUM)
    
    // Assert reset on both interfaces
    env.initiator_vif.reset = 1;
    env.target_vif.reset = 1;
    
    // Hold reset for reset duration
    #1us;
    
    // Deassert reset
    env.initiator_vif.reset = 0;
    env.target_vif.reset = 0;
    
    `uvm_info("LTSM_TEST", "Reset sequence completed - starting link training", UVM_MEDIUM)
  endtask
  
  virtual function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    
    `uvm_info("LTSM_TEST", "=== FINAL TEST REPORT ===", UVM_LOW)
    
    if (env.initiator_ltsm.current_state == LTSM_ACTIVE && 
        env.target_ltsm.current_state == LTSM_ACTIVE) begin
      `uvm_info("LTSM_TEST", "TEST RESULT: PASSED", UVM_LOW)
      `uvm_info("LTSM_TEST", "UCIe LTSM training completed successfully", UVM_LOW)
    end else begin
      `uvm_error("LTSM_TEST", "TEST RESULT: FAILED")
      `uvm_error("LTSM_TEST", "UCIe LTSM training did not complete successfully")
    end
    
    `uvm_info("LTSM_TEST", "========================", UVM_LOW)
  endfunction
  
endclass : ucie_sb_ltsm_test

//=============================================================================
// LTSM Example Testbench Module
//=============================================================================

module ucie_sb_ltsm_testbench;
  
  // Clock generation
  logic clk = 0;
  always #625ps clk = ~clk; // 800MHz
  
  // Interface instances
  ucie_sb_inf initiator_if(clk);
  ucie_sb_inf target_if(clk);
  
  // Cross-connect the interfaces for loopback
  assign target_if.SBRX_CLK = initiator_if.SBTX_CLK;
  assign target_if.SBRX_DATA = initiator_if.SBTX_DATA;
  assign initiator_if.SBRX_CLK = target_if.SBTX_CLK;
  assign initiator_if.SBRX_DATA = target_if.SBTX_DATA;
  
  // Initialize interfaces
  initial begin
    initiator_if.reset = 1;
    target_if.reset = 1;
    
    // Set interfaces in config DB
    uvm_config_db#(virtual ucie_sb_inf)::set(null, "uvm_test_top.env", "initiator_vif", initiator_if);
    uvm_config_db#(virtual ucie_sb_inf)::set(null, "uvm_test_top.env", "target_vif", target_if);
    
    // Run UVM test
    run_test("ucie_sb_ltsm_test");
  end
  
  // Timeout watchdog
  initial begin
    #200ms;
    `uvm_fatal("TESTBENCH", "Simulation timeout - test did not complete within 200ms")
  end
  
  // Waveform generation
  initial begin
    $dumpfile("ucie_sb_ltsm_waves.vcd");
    $dumpvars(0, ucie_sb_ltsm_testbench);
  end
  
endmodule : ucie_sb_ltsm_testbench