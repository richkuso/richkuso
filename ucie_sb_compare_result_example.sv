/*******************************************************************************
 * UCIe Sideband Compare Result Model - Example Testbench
 * 
 * OVERVIEW:
 *   Comprehensive example testbench demonstrating the UCIe sideband compare
 *   result model functionality. Shows complete operational flow from array
 *   initialization through TX request processing and RX result handling.
 *
 * DEMONSTRATION FEATURES:
 *   • Array initialization with configurable expected ranges
 *   • TX request parameter processing and array access region setup
 *   • RX transaction interception and data rewriting
 *   • Parity recalculation and logging
 *   • Enable/disable control and pass-through mode
 *   • Statistics collection and reporting
 *
 * TEST SCENARIOS:
 *   1. Basic functionality with example parameters from specification
 *   2. Edge cases with boundary conditions
 *   3. Enable/disable control testing
 *   4. Pass-through mode verification
 *   5. Comprehensive logging demonstration
 *
 * COMPLIANCE:
 *   • IEEE 1800-2017 SystemVerilog
 *   • UVM 1.2 methodology
 *   • UCIe 1.1 specification
 *
 * AUTHOR: UCIe Sideband UVM Agent
 * VERSION: 1.0 - Compare Result Model Example
 ******************************************************************************/

/*-----------------------------------------------------------------------------
 * COMPARE RESULT MODEL TEST ENVIRONMENT
 * 
 * UVM test environment containing the compare result model and supporting
 * infrastructure for demonstration and validation.
 *-----------------------------------------------------------------------------*/

class ucie_sb_compare_result_env extends uvm_env;
  `uvm_component_utils(ucie_sb_compare_result_env)
  
  /*---------------------------------------------------------------------------
   * ENVIRONMENT COMPONENTS
   * Model under test and supporting infrastructure
   *---------------------------------------------------------------------------*/
  
  ucie_sb_compare_result_model compare_model;     // Model under test
  ucie_sb_agent rx_agent;                        // RX sideband agent
  ucie_sb_compare_result_config model_cfg;       // Model configuration
  
  /*---------------------------------------------------------------------------
   * ANALYSIS INFRASTRUCTURE
   * Scoreboards and analysis components for verification
   *---------------------------------------------------------------------------*/
  
  uvm_analysis_port #(ucie_sb_transaction) processed_rx_ap;
  
  /*---------------------------------------------------------------------------
   * CONSTRUCTOR - Initialize test environment
   *---------------------------------------------------------------------------*/
  function new(string name = "ucie_sb_compare_result_env", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  /*---------------------------------------------------------------------------
   * EXTERNAL METHOD DECLARATIONS
   * Environment implementation methods
   *---------------------------------------------------------------------------*/
  
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);

endclass : ucie_sb_compare_result_env

/*******************************************************************************
 * COMPARE RESULT MODEL TEST SEQUENCE
 * 
 * Comprehensive test sequence demonstrating all model functionality with
 * the example scenario from the specification.
 ******************************************************************************/

class ucie_sb_compare_result_test_sequence extends uvm_sequence #(ucie_sb_transaction);
  `uvm_object_utils(ucie_sb_compare_result_test_sequence)
  
  /*---------------------------------------------------------------------------
   * SEQUENCE CONFIGURATION
   * Test parameters and control variables
   *---------------------------------------------------------------------------*/
  
  ucie_sb_compare_result_model target_model;     // Reference to model under test
  int num_test_transactions = 20;                // Number of RX transactions to generate
  
  /*---------------------------------------------------------------------------
   * CONSTRUCTOR - Initialize test sequence
   *---------------------------------------------------------------------------*/
  function new(string name = "ucie_sb_compare_result_test_sequence");
    super.new(name);
  endfunction
  
  /*---------------------------------------------------------------------------
   * EXTERNAL METHOD DECLARATIONS
   * Sequence implementation methods
   *---------------------------------------------------------------------------*/
  
  extern virtual task body();
  extern virtual task test_basic_functionality();
  extern virtual task test_specification_example();
  extern virtual task test_edge_cases();
  extern virtual task test_enable_disable();
  extern virtual task test_pass_through_mode();
  extern virtual function ucie_sb_transaction create_tx_transaction(bit [23:0] addr);
  extern virtual function ucie_sb_transaction create_target_tx_transaction(int addr_index);
  extern virtual function ucie_sb_transaction create_rx_transaction(int tag, bit [31:0] data);
  extern virtual task send_tx_transaction(ucie_sb_transaction trans);
  extern virtual task send_rx_transaction(ucie_sb_transaction trans);

endclass : ucie_sb_compare_result_test_sequence

/*******************************************************************************
 * MAIN TEST CLASS
 * 
 * Primary test class orchestrating the complete demonstration of compare
 * result model functionality.
 ******************************************************************************/

class ucie_sb_compare_result_test extends uvm_test;
  `uvm_component_utils(ucie_sb_compare_result_test)
  
  /*---------------------------------------------------------------------------
   * TEST COMPONENTS
   * Test environment and configuration
   *---------------------------------------------------------------------------*/
  
  ucie_sb_compare_result_env test_env;           // Test environment
  ucie_sb_compare_result_config model_cfg;      // Model configuration
  
  /*---------------------------------------------------------------------------
   * CONSTRUCTOR - Initialize test
   *---------------------------------------------------------------------------*/
  function new(string name = "ucie_sb_compare_result_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  /*---------------------------------------------------------------------------
   * EXTERNAL METHOD DECLARATIONS
   * Test implementation methods
   *---------------------------------------------------------------------------*/
  
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void end_of_elaboration_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);

endclass : ucie_sb_compare_result_test

/*******************************************************************************
 * ENVIRONMENT IMPLEMENTATION
 ******************************************************************************/

/*---------------------------------------------------------------------------
 * ENVIRONMENT BUILD PHASE IMPLEMENTATION
 * 
 * Creates and configures all environment components.
 *---------------------------------------------------------------------------*/
function void ucie_sb_compare_result_env::build_phase(uvm_phase phase);
  super.build_phase(phase);
  
  // Create model configuration
  model_cfg = ucie_sb_compare_result_config::type_id::create("model_cfg");
  
  // Configure model with specification example parameters
  model_cfg.set_expected_range(10, 20, 29, 33);  // Example from specification
  model_cfg.set_logging_options(1, 1, "compare_result_example.log");
  model_cfg.set_operational_mode(1, 1, 0);
  
  // Set configuration in config DB
  uvm_config_db#(ucie_sb_compare_result_config)::set(this, "compare_model", "cfg", model_cfg);
  
  // Create compare result model
  compare_model = ucie_sb_compare_result_model::type_id::create("compare_model", this);
  
  // Create RX agent
  rx_agent = ucie_sb_agent::type_id::create("rx_agent", this);
  
  // Create analysis port
  processed_rx_ap = new("processed_rx_ap", this);
  
  `uvm_info("COMPARE_RESULT_ENV", "Environment build phase complete", UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * ENVIRONMENT CONNECT PHASE IMPLEMENTATION
 * 
 * Connects monitor analysis ports to model's TLM analysis FIFOs.
 *---------------------------------------------------------------------------*/
function void ucie_sb_compare_result_env::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  
  // Connect TX agent monitor to compare model TX FIFO
  // tx_agent.monitor.ap.connect(compare_model.tx_fifo.analysis_export);
  
  // Connect RX agent monitor to compare model RX FIFO
  rx_agent.monitor.ap.connect(compare_model.rx_fifo.analysis_export);
  
  // Connect compare model output to analysis port
  compare_model.processed_rx_ap.connect(processed_rx_ap);
  
  `uvm_info("COMPARE_RESULT_ENV", "Environment connect phase complete", UVM_LOW)
endfunction

/*******************************************************************************
 * TEST SEQUENCE IMPLEMENTATION
 ******************************************************************************/

/*---------------------------------------------------------------------------
 * SEQUENCE BODY IMPLEMENTATION
 * 
 * Main sequence execution orchestrating all test scenarios.
 *---------------------------------------------------------------------------*/
task ucie_sb_compare_result_test_sequence::body();
  `uvm_info("COMPARE_RESULT_SEQUENCE", "Starting compare result model test sequence", UVM_LOW)
  
  // Test 1: Basic functionality
  `uvm_info("COMPARE_RESULT_SEQUENCE", "=== TEST 1: Basic Functionality ===", UVM_LOW)
  test_basic_functionality();
  
  // Test 2: Specification example scenario
  `uvm_info("COMPARE_RESULT_SEQUENCE", "=== TEST 2: Specification Example ===", UVM_LOW)
  test_specification_example();
  
  // Test 3: Edge cases
  `uvm_info("COMPARE_RESULT_SEQUENCE", "=== TEST 3: Edge Cases ===", UVM_LOW)
  test_edge_cases();
  
  // Test 4: Enable/disable control
  `uvm_info("COMPARE_RESULT_SEQUENCE", "=== TEST 4: Enable/Disable Control ===", UVM_LOW)
  test_enable_disable();
  
  // Test 5: Pass-through mode
  `uvm_info("COMPARE_RESULT_SEQUENCE", "=== TEST 5: Pass-through Mode ===", UVM_LOW)
  test_pass_through_mode();
  
  `uvm_info("COMPARE_RESULT_SEQUENCE", "Compare result model test sequence complete", UVM_LOW)
endtask

/*---------------------------------------------------------------------------
 * BASIC FUNCTIONALITY TEST IMPLEMENTATION
 * 
 * Tests basic three-address group behavior with target addresses.
 *---------------------------------------------------------------------------*/
task ucie_sb_compare_result_test_sequence::test_basic_functionality();
  ucie_sb_transaction tx_trans, rx_trans;
  
  `uvm_info("COMPARE_RESULT_SEQUENCE", "Testing basic three-address group functionality...", UVM_MEDIUM)
  
  // Test one complete group of three addresses
  for (int group = 0; group < 2; group++) begin
    `uvm_info("COMPARE_RESULT_SEQUENCE", $sformatf("Starting group %0d (uses array[%0d])", group, group), UVM_MEDIUM)
    
    // Send three TX/RX pairs for each group (all use same array index)
    for (int addr_idx = 0; addr_idx < 3; addr_idx++) begin
      // Create and send target TX transaction
      tx_trans = create_target_tx_transaction(addr_idx);
      send_tx_transaction(tx_trans);
      
      // Create and send corresponding RX transaction
      rx_trans = create_rx_transaction(100 + group*3 + addr_idx, 32'h12345678 + addr_idx);
      send_rx_transaction(rx_trans);
      
      `uvm_info("COMPARE_RESULT_SEQUENCE", $sformatf("Sent TX addr=0x%06h, RX data=0x%08h", 
                tx_trans.addr, rx_trans.data[31:0]), UVM_HIGH)
      
      #20ns;  // Allow processing time
    end
    
    `uvm_info("COMPARE_RESULT_SEQUENCE", $sformatf("Completed group %0d", group), UVM_MEDIUM)
  end
  
  `uvm_info("COMPARE_RESULT_SEQUENCE", "Basic functionality test complete", UVM_MEDIUM)
endtask

/*---------------------------------------------------------------------------
 * SPECIFICATION EXAMPLE TEST IMPLEMENTATION
 * 
 * Tests the linear index mapping and three-address group behavior.
 *---------------------------------------------------------------------------*/
task ucie_sb_compare_result_test_sequence::test_specification_example();
  ucie_sb_transaction tx_trans, rx_trans;
  
  `uvm_info("COMPARE_RESULT_SEQUENCE", "Testing specification example scenario...", UVM_MEDIUM)
  
  // Test configuration:
  // - Array initialized with exp_volt_min=10, exp_volt_max=20, exp_clk_phase_min=29, exp_clk_phase_max=33
  // - Initial index params: volt_min=10, volt_max=11, clk_phase=1
  // - Expected valid indices: Y[10:11], X[30:32] = 6 indices total
  // - Linear mapping: index = y*63 + x
  
  `uvm_info("COMPARE_RESULT_SEQUENCE", "Array fill region: Y[10:20], X[29:33] (PASS values)", UVM_MEDIUM)
  `uvm_info("COMPARE_RESULT_SEQUENCE", "Valid indices: Y[10:11], X[30:32] (6 indices)", UVM_MEDIUM)
  `uvm_info("COMPARE_RESULT_SEQUENCE", "Expected sequence: index 660,661,662,693,694,695", UVM_MEDIUM)
  
  // Test multiple groups to show index advancement
  for (int group = 0; group < 3; group++) begin
    `uvm_info("COMPARE_RESULT_SEQUENCE", $sformatf("=== GROUP %0d (should use array[%0d]) ===", group, group), UVM_MEDIUM)
    
    // Send three TX/RX pairs for this group
    for (int addr_idx = 0; addr_idx < 3; addr_idx++) begin
      // Create and send target TX transaction
      tx_trans = create_target_tx_transaction(addr_idx);
      send_tx_transaction(tx_trans);
      
      // Create and send corresponding RX transaction
      rx_trans = create_rx_transaction(200 + group*3 + addr_idx, 32'hABCDEF00 + group*16 + addr_idx);
      send_rx_transaction(rx_trans);
      
      `uvm_info("COMPARE_RESULT_SEQUENCE", $sformatf("Group %0d, Addr %0d: TX=0x%06h, RX=0x%08h", 
                group, addr_idx, tx_trans.addr, rx_trans.data[31:0]), UVM_HIGH)
      
      #15ns;  // Allow processing time
    end
    
    `uvm_info("COMPARE_RESULT_SEQUENCE", $sformatf("=== GROUP %0d COMPLETE ===", group), UVM_MEDIUM)
    #10ns;
  end
  
  `uvm_info("COMPARE_RESULT_SEQUENCE", "Specification example test complete", UVM_MEDIUM)
endtask

/*---------------------------------------------------------------------------
 * EDGE CASES TEST IMPLEMENTATION
 * 
 * Tests boundary conditions and edge cases.
 *---------------------------------------------------------------------------*/
task ucie_sb_compare_result_test_sequence::test_edge_cases();
  ucie_sb_transaction rx_trans;
  
  `uvm_info("COMPARE_RESULT_SEQUENCE", "Testing edge cases...", UVM_MEDIUM)
  
  // Test 1: Maximum ranges
  target_model.process_tx_request(0, 63, 31);  // Full Y range, full X range
  
  rx_trans = create_rx_transaction(200, 32'hEDGE0001);
  send_rx_transaction(rx_trans);
  #10ns;
  
  // Test 2: Minimum ranges
  target_model.process_tx_request(31, 31, 0);  // Single Y, minimal X range
  
  rx_trans = create_rx_transaction(201, 32'hEDGE0002);
  send_rx_transaction(rx_trans);
  #10ns;
  
  // Test 3: Boundary clk_phase values
  target_model.process_tx_request(15, 18, 31);  // clk_phase at center
  
  rx_trans = create_rx_transaction(202, 32'hEDGE0003);
  send_rx_transaction(rx_trans);
  #10ns;
  
  `uvm_info("COMPARE_RESULT_SEQUENCE", "Edge cases test complete", UVM_MEDIUM)
endtask

/*---------------------------------------------------------------------------
 * ENABLE/DISABLE CONTROL TEST IMPLEMENTATION
 * 
 * Tests model enable/disable functionality.
 *---------------------------------------------------------------------------*/
task ucie_sb_compare_result_test_sequence::test_enable_disable();
  ucie_sb_transaction rx_trans;
  
  `uvm_info("COMPARE_RESULT_SEQUENCE", "Testing enable/disable control...", UVM_MEDIUM)
  
  // Set up TX request
  target_model.process_tx_request(15, 17, 5);
  
  // Test with model enabled (should process normally)
  target_model.cfg.enable_model = 1;
  rx_trans = create_rx_transaction(300, 32'hENABLE01);
  send_rx_transaction(rx_trans);
  #10ns;
  
  // Test with model disabled (should drop RX transactions)
  target_model.cfg.enable_model = 0;
  `uvm_info("COMPARE_RESULT_SEQUENCE", "Disabling model - next RX should be dropped", UVM_MEDIUM)
  rx_trans = create_rx_transaction(301, 32'hDISABLE1);
  send_rx_transaction(rx_trans);
  #10ns;
  
  // Re-enable model
  target_model.cfg.enable_model = 1;
  rx_trans = create_rx_transaction(302, 32'hENABLE02);
  send_rx_transaction(rx_trans);
  #10ns;
  
  `uvm_info("COMPARE_RESULT_SEQUENCE", "Enable/disable test complete", UVM_MEDIUM)
endtask

/*---------------------------------------------------------------------------
 * PASS-THROUGH MODE TEST IMPLEMENTATION
 * 
 * Tests pass-through mode functionality.
 *---------------------------------------------------------------------------*/
task ucie_sb_compare_result_test_sequence::test_pass_through_mode();
  ucie_sb_transaction rx_trans;
  
  `uvm_info("COMPARE_RESULT_SEQUENCE", "Testing pass-through mode...", UVM_MEDIUM)
  
  // Set up TX request
  target_model.process_tx_request(20, 25, 10);
  
  // Test normal mode first
  target_model.cfg.pass_through_mode = 0;
  rx_trans = create_rx_transaction(400, 32'hNORMAL01);
  send_rx_transaction(rx_trans);
  #10ns;
  
  // Enable pass-through mode
  target_model.cfg.pass_through_mode = 1;
  `uvm_info("COMPARE_RESULT_SEQUENCE", "Enabling pass-through mode - RX should be unchanged", UVM_MEDIUM)
  rx_trans = create_rx_transaction(401, 32'hPASSTHRU);
  send_rx_transaction(rx_trans);
  #10ns;
  
  // Disable pass-through mode
  target_model.cfg.pass_through_mode = 0;
  rx_trans = create_rx_transaction(402, 32'hNORMAL02);
  send_rx_transaction(rx_trans);
  #10ns;
  
  `uvm_info("COMPARE_RESULT_SEQUENCE", "Pass-through mode test complete", UVM_MEDIUM)
endtask

/*---------------------------------------------------------------------------
 * TX TRANSACTION CREATION IMPLEMENTATION
 * 
 * Creates TX transaction with specific target address.
 *---------------------------------------------------------------------------*/
function ucie_sb_transaction ucie_sb_compare_result_test_sequence::create_tx_transaction(bit [23:0] addr);
  ucie_sb_transaction trans;
  
  trans = ucie_sb_transaction::type_id::create("tx_trans");
  
  // Set transaction parameters
  trans.opcode = CFG_READ_32B;    // TX request opcode
  trans.addr = addr;              // Use specific target address
  trans.srcid = 3'h1;
  trans.dstid = 3'h2;
  
  // Update packet info to ensure consistency
  trans.update_packet_info();
  
  return trans;
endfunction

/*---------------------------------------------------------------------------
 * TX TRANSACTION CREATION FOR TARGET ADDRESSES
 * 
 * Creates TX transactions for the three target addresses.
 *---------------------------------------------------------------------------*/
function ucie_sb_transaction ucie_sb_compare_result_test_sequence::create_target_tx_transaction(int addr_index);
  bit [23:0] target_addr;
  
  case (addr_index)
    0: target_addr = target_model.cfg.TARGET_ADDR_0;  // 0x013140
    1: target_addr = target_model.cfg.TARGET_ADDR_1;  // 0x013144
    2: target_addr = target_model.cfg.TARGET_ADDR_2;  // 0x013148
    default: target_addr = 24'h000000;
  endcase
  
  return create_tx_transaction(target_addr);
endfunction

/*---------------------------------------------------------------------------
 * RX TRANSACTION CREATION IMPLEMENTATION
 * 
 * Creates RX transaction with specified parameters.
 *---------------------------------------------------------------------------*/
function ucie_sb_transaction ucie_sb_compare_result_test_sequence::create_rx_transaction(int tag, bit [31:0] data);
  ucie_sb_transaction trans;
  
  trans = ucie_sb_transaction::type_id::create("rx_trans");
  
  // Set transaction parameters
  trans.opcode = COMPLETION_32B;  // RX completion opcode
  trans.tag = tag;
  trans.data[31:0] = data;
  trans.srcid = 3'h2;
  trans.dstid = 3'h1;
  trans.dp = 1'b0;  // Will be recalculated by model
  
  // Update packet info to ensure consistency
  trans.update_packet_info();
  
  return trans;
endfunction

/*---------------------------------------------------------------------------
 * TX TRANSACTION TRANSMISSION IMPLEMENTATION
 * 
 * Sends TX transaction to model's TX FIFO for processing.
 *---------------------------------------------------------------------------*/
task ucie_sb_compare_result_test_sequence::send_tx_transaction(ucie_sb_transaction trans);
  // Send transaction directly to model's TX FIFO
  target_model.tx_fifo.write(trans);
  
  if (target_model.cfg.enable_debug) begin
    `uvm_info("COMPARE_RESULT_SEQUENCE", $sformatf("Sent TX to FIFO: addr=0x%06h, tag=%0d", 
              trans.addr, trans.tag), UVM_HIGH)
  end
endtask

/*---------------------------------------------------------------------------
 * RX TRANSACTION TRANSMISSION IMPLEMENTATION
 * 
 * Sends RX transaction to model's RX FIFO for processing.
 *---------------------------------------------------------------------------*/
task ucie_sb_compare_result_test_sequence::send_rx_transaction(ucie_sb_transaction trans);
  // Send transaction directly to model's RX FIFO
  target_model.rx_fifo.write(trans);
  
  if (target_model.cfg.enable_debug) begin
    `uvm_info("COMPARE_RESULT_SEQUENCE", $sformatf("Sent RX to FIFO: tag=%0d, data=0x%08h", 
              trans.tag, trans.data[31:0]), UVM_HIGH)
  end
endtask

/*******************************************************************************
 * MAIN TEST IMPLEMENTATION
 ******************************************************************************/

/*---------------------------------------------------------------------------
 * TEST BUILD PHASE IMPLEMENTATION
 * 
 * Creates test environment and configuration.
 *---------------------------------------------------------------------------*/
function void ucie_sb_compare_result_test::build_phase(uvm_phase phase);
  super.build_phase(phase);
  
  // Create model configuration
  model_cfg = ucie_sb_compare_result_config::type_id::create("model_cfg");
  
  // Configure with specification example parameters
  model_cfg.set_expected_range(10, 20, 29, 33);
  model_cfg.set_logging_options(1, 1, "compare_result_test.log");
  model_cfg.set_operational_mode(1, 1, 0);
  
  // Set configuration in config DB
  uvm_config_db#(ucie_sb_compare_result_config)::set(this, "*", "cfg", model_cfg);
  
  // Create test environment
  test_env = ucie_sb_compare_result_env::type_id::create("test_env", this);
  
  `uvm_info("COMPARE_RESULT_TEST", "Test build phase complete", UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * TEST END OF ELABORATION PHASE IMPLEMENTATION
 * 
 * Final test setup and configuration validation.
 *---------------------------------------------------------------------------*/
function void ucie_sb_compare_result_test::end_of_elaboration_phase(uvm_phase phase);
  super.end_of_elaboration_phase(phase);
  
  // Print test configuration
  `uvm_info("COMPARE_RESULT_TEST", "=== Test Configuration ===", UVM_LOW)
  model_cfg.print_config();
  
  `uvm_info("COMPARE_RESULT_TEST", "Test end of elaboration phase complete", UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * TEST RUN PHASE IMPLEMENTATION
 * 
 * Main test execution.
 *---------------------------------------------------------------------------*/
task ucie_sb_compare_result_test::run_phase(uvm_phase phase);
  ucie_sb_compare_result_test_sequence test_seq;
  
  phase.raise_objection(this);
  
  `uvm_info("COMPARE_RESULT_TEST", "Starting compare result model test", UVM_LOW)
  
  // Create and configure test sequence
  test_seq = ucie_sb_compare_result_test_sequence::type_id::create("test_seq");
  test_seq.target_model = test_env.compare_model;
  
  // Start test sequence
  test_seq.start(null);  // No sequencer needed for direct model testing
  
  // Wait for all processing to complete
  #100ns;
  
  `uvm_info("COMPARE_RESULT_TEST", "Compare result model test complete", UVM_LOW)
  
  phase.drop_objection(this);
endtask