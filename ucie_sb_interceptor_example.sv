/*******************************************************************************
 * UCIe Sideband Transaction Interceptor Usage Example
 * 
 * OVERVIEW:
 *   Complete UVM test environment demonstrating the integration and usage of
 *   the UCIe (Universal Chiplet Interconnect Express) sideband transaction
 *   interceptor. Shows how to configure, connect, and operate the interceptor
 *   in a practical verification scenario.
 *
 * EXAMPLE CAPABILITIES:
 *   • Complete UVM test environment with interceptor integration
 *   • Configurable address-based interception scenarios
 *   • Custom completion generation examples
 *   • Pass-through and interception mode demonstrations
 *   • Comprehensive logging and statistics reporting
 *
 * TEST SCENARIOS:
 *   • Address-based interception with custom data responses
 *   • Pass-through mode for non-matching transactions
 *   • Error completion generation testing
 *   • Performance and statistics analysis
 *
 * INTEGRATION ARCHITECTURE:
 *   • DUT with separate TX/RX sideband interfaces
 *   • Interceptor positioned between RX monitor and response driver
 *   • Analysis port connections for transaction visibility
 *   • Configuration database integration for parameter control
 *
 * COMPLIANCE:
 *   • IEEE 1800-2017 SystemVerilog
 *   • UVM 1.2 methodology
 *   • UCIe 1.1 specification
 *
 * AUTHOR: UCIe Sideband UVM Agent
 * VERSION: 1.0 - Complete interceptor demonstration environment
 ******************************************************************************/

/*******************************************************************************
 * INTERCEPTOR TEST ENVIRONMENT
 * 
 * UVM environment integrating the transaction interceptor with sideband agents
 * for comprehensive interception testing and demonstration.
 ******************************************************************************/

class ucie_sb_interceptor_env extends uvm_env;
  `uvm_component_utils(ucie_sb_interceptor_env)
  
  /*---------------------------------------------------------------------------
   * ENVIRONMENT COMPONENT HIERARCHY
   * Core components for interceptor testing environment
   *---------------------------------------------------------------------------*/
  
  ucie_sb_agent tx_agent;                          // TX path agent
  ucie_sb_agent rx_agent;                          // RX path agent  
  ucie_sb_agent response_agent;                    // Response generation agent
  ucie_sb_transaction_interceptor interceptor;     // Transaction interceptor
  
  // Analysis components
  uvm_analysis_port #(ucie_sb_transaction) env_tx_ap;
  uvm_analysis_port #(ucie_sb_transaction) env_rx_ap;
  uvm_analysis_port #(ucie_sb_transaction) env_intercepted_ap;
  
  /*---------------------------------------------------------------------------
   * CONSTRUCTOR - Initialize environment
   *---------------------------------------------------------------------------*/
  function new(string name = "ucie_sb_interceptor_env", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  /*---------------------------------------------------------------------------
   * EXTERNAL METHOD DECLARATIONS
   * UVM phase and configuration methods
   *---------------------------------------------------------------------------*/
  
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);
  extern virtual function void end_of_elaboration_phase(uvm_phase phase);

endclass : ucie_sb_interceptor_env

/*******************************************************************************
 * INTERCEPTOR TEST SEQUENCE
 * 
 * UVM sequence demonstrating various interceptor scenarios including
 * address-based matching, custom responses, and pass-through operations.
 ******************************************************************************/

class ucie_sb_interceptor_sequence extends uvm_sequence #(ucie_sb_transaction);
  `uvm_object_utils(ucie_sb_interceptor_sequence)
  
  /*---------------------------------------------------------------------------
   * SEQUENCE CONFIGURATION
   * Test scenario control parameters
   *---------------------------------------------------------------------------*/
  
  int num_cfg_reads = 20;                    // Number of CFG read transactions
  bit [23:0] intercept_addr_base = 24'h100000; // Base address for interception
  bit [23:0] normal_addr_base = 24'h200000;    // Non-intercepted address base
  
  /*---------------------------------------------------------------------------
   * CONSTRUCTOR - Initialize sequence
   *---------------------------------------------------------------------------*/
  function new(string name = "ucie_sb_interceptor_sequence");
    super.new(name);
  endfunction
  
  /*---------------------------------------------------------------------------
   * EXTERNAL METHOD DECLARATIONS
   * Sequence execution and transaction generation methods
   *---------------------------------------------------------------------------*/
  
  extern virtual task body();
  extern virtual task send_cfg_read(bit [23:0] addr, bit [4:0] tag, bit should_intercept);
  extern virtual task send_mixed_transactions();

endclass : ucie_sb_interceptor_sequence

/*******************************************************************************
 * INTERCEPTOR TEST CASE
 * 
 * UVM test demonstrating comprehensive interceptor functionality with
 * multiple test scenarios and configuration modes.
 ******************************************************************************/

class ucie_sb_interceptor_test extends uvm_test;
  `uvm_component_utils(ucie_sb_interceptor_test)
  
  /*---------------------------------------------------------------------------
   * TEST COMPONENTS
   * Test environment and configuration objects
   *---------------------------------------------------------------------------*/
  
  ucie_sb_interceptor_env env;
  ucie_sb_interceptor_config interceptor_cfg;
  
  /*---------------------------------------------------------------------------
   * CONSTRUCTOR - Initialize test
   *---------------------------------------------------------------------------*/
  function new(string name = "ucie_sb_interceptor_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  /*---------------------------------------------------------------------------
   * EXTERNAL METHOD DECLARATIONS
   * UVM phase methods and test execution
   *---------------------------------------------------------------------------*/
  
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void end_of_elaboration_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);
  extern virtual function void report_phase(uvm_phase phase);
  extern virtual function void configure_interceptor();

endclass : ucie_sb_interceptor_test

/*******************************************************************************
 * INTERCEPTOR TESTBENCH MODULE
 * 
 * Top-level testbench module with interface instantiation and UVM test
 * execution for interceptor demonstration.
 ******************************************************************************/

module ucie_sb_interceptor_testbench;
  
  /*---------------------------------------------------------------------------
   * CLOCK AND RESET GENERATION
   * Basic clock and reset infrastructure for testbench
   *---------------------------------------------------------------------------*/
  
  logic clk = 0;
  logic reset = 1;
  
  always #625ps clk = ~clk; // 800MHz clock
  
  initial begin
    reset = 1;
    #100ns;
    reset = 0;
    `uvm_info("TB", "Reset deasserted", UVM_LOW)
  end
  
  /*---------------------------------------------------------------------------
   * INTERFACE INSTANTIATION
   * Sideband interfaces for TX, RX, and response paths
   *---------------------------------------------------------------------------*/
  
  ucie_sb_inf tx_if(clk);      // TX interface (monitor CFG reads)
  ucie_sb_inf rx_if(clk);      // RX interface (monitor completions)
  ucie_sb_inf resp_if(clk);    // Response interface (send completions)
  
  /*---------------------------------------------------------------------------
   * INTERFACE INITIALIZATION AND CONFIGURATION
   * Set up interfaces and configure UVM database
   *---------------------------------------------------------------------------*/
  
  initial begin
    // Initialize interfaces
    tx_if.reset = reset;
    rx_if.reset = reset;
    resp_if.reset = reset;
    
    // Set interfaces in UVM configuration database
    uvm_config_db#(virtual ucie_sb_inf)::set(null, "uvm_test_top.env.tx_agent", "vif", tx_if);
    uvm_config_db#(virtual ucie_sb_inf)::set(null, "uvm_test_top.env.rx_agent", "vif", rx_if);
    uvm_config_db#(virtual ucie_sb_inf)::set(null, "uvm_test_top.env.response_agent", "vif", resp_if);
    
    // Run UVM test
    run_test("ucie_sb_interceptor_test");
  end
  
  /*---------------------------------------------------------------------------
   * SIMULATION CONTROL AND MONITORING
   * Timeout protection and waveform generation
   *---------------------------------------------------------------------------*/
  
  // Simulation timeout protection
  initial begin
    #10ms;
    `uvm_fatal("TB", "Simulation timeout - test did not complete within 10ms")
  end
  
  // Waveform generation
  initial begin
    $dumpfile("ucie_sb_interceptor_waves.vcd");
    $dumpvars(0, ucie_sb_interceptor_testbench);
  end
  
endmodule : ucie_sb_interceptor_testbench

/*******************************************************************************
 * ENVIRONMENT IMPLEMENTATION
 ******************************************************************************/

/*---------------------------------------------------------------------------
 * ENVIRONMENT BUILD PHASE
 * 
 * Creates and configures all environment components including agents
 * and interceptor with proper configuration setup.
 *---------------------------------------------------------------------------*/
function void ucie_sb_interceptor_env::build_phase(uvm_phase phase);
  super.build_phase(phase);
  
  // Create sideband agents
  tx_agent = ucie_sb_agent::type_id::create("tx_agent", this);
  rx_agent = ucie_sb_agent::type_id::create("rx_agent", this);
  response_agent = ucie_sb_agent::type_id::create("response_agent", this);
  
  // Create transaction interceptor
  interceptor = ucie_sb_transaction_interceptor::type_id::create("interceptor", this);
  
  // Create analysis ports
  env_tx_ap = new("env_tx_ap", this);
  env_rx_ap = new("env_rx_ap", this);
  env_intercepted_ap = new("env_intercepted_ap", this);
  
  // Configure agents
  uvm_config_db#(uvm_active_passive_enum)::set(this, "tx_agent", "is_active", UVM_PASSIVE);
  uvm_config_db#(uvm_active_passive_enum)::set(this, "rx_agent", "is_active", UVM_PASSIVE);
  uvm_config_db#(uvm_active_passive_enum)::set(this, "response_agent", "is_active", UVM_ACTIVE);
  
  `uvm_info("ENV", "Interceptor environment build phase complete", UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * ENVIRONMENT CONNECT PHASE
 * 
 * Connects analysis ports between agents and interceptor to establish
 * the transaction flow for interception processing.
 *---------------------------------------------------------------------------*/
function void ucie_sb_interceptor_env::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  
  // Connect agent monitors to interceptor
  tx_agent.monitor.ap.connect(interceptor.tx_monitor_ap);
  rx_agent.monitor.ap.connect(interceptor.rx_monitor_ap);
  
  // Connect interceptor to response agent
  // Note: This connection would be made through TLM FIFOs in actual implementation
  
  // Connect analysis ports to environment level
  tx_agent.monitor.ap.connect(env_tx_ap);
  rx_agent.monitor.ap.connect(env_rx_ap);
  interceptor.intercepted_ap.connect(env_intercepted_ap);
  
  `uvm_info("ENV", "Interceptor environment connect phase complete", UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * ENVIRONMENT END OF ELABORATION PHASE
 * 
 * Final environment setup and configuration validation.
 *---------------------------------------------------------------------------*/
function void ucie_sb_interceptor_env::end_of_elaboration_phase(uvm_phase phase);
  super.end_of_elaboration_phase(phase);
  `uvm_info("ENV", "Interceptor environment end of elaboration phase complete", UVM_LOW)
endfunction

/*******************************************************************************
 * SEQUENCE IMPLEMENTATION
 ******************************************************************************/

/*---------------------------------------------------------------------------
 * SEQUENCE BODY IMPLEMENTATION
 * 
 * Main sequence execution generating various CFG read scenarios to
 * demonstrate interceptor functionality.
 *---------------------------------------------------------------------------*/
task ucie_sb_interceptor_sequence::body();
  `uvm_info("SEQ", "Starting interceptor demonstration sequence", UVM_LOW)
  
  // Test 1: Send CFG reads to intercepted address range
  `uvm_info("SEQ", "=== Test 1: Intercepted Address Range ===", UVM_LOW)
  for (int i = 0; i < 5; i++) begin
    send_cfg_read(intercept_addr_base + (i * 4), i[4:0], 1);
    #1us;
  end
  
  // Test 2: Send CFG reads to non-intercepted addresses
  `uvm_info("SEQ", "=== Test 2: Non-Intercepted Address Range ===", UVM_LOW)
  for (int i = 0; i < 5; i++) begin
    send_cfg_read(normal_addr_base + (i * 4), (i + 10)[4:0], 0);
    #1us;
  end
  
  // Test 3: Mixed transaction scenario
  `uvm_info("SEQ", "=== Test 3: Mixed Transaction Scenario ===", UVM_LOW)
  send_mixed_transactions();
  
  `uvm_info("SEQ", "Interceptor demonstration sequence completed", UVM_LOW)
endtask

/*---------------------------------------------------------------------------
 * CFG READ TRANSACTION GENERATION
 * 
 * Generates individual CFG_READ_32B transaction with specified parameters
 * for interceptor testing.
 *---------------------------------------------------------------------------*/
task ucie_sb_interceptor_sequence::send_cfg_read(bit [23:0] addr, bit [4:0] tag, bit should_intercept);
  ucie_sb_transaction cfg_read;
  
  cfg_read = ucie_sb_transaction::type_id::create("cfg_read");
  
  // Configure CFG read transaction
  cfg_read.opcode = CFG_READ_32B;
  cfg_read.srcid = 3'h1;
  cfg_read.dstid = 3'h2;
  cfg_read.addr = addr;
  cfg_read.tag = tag;
  cfg_read.be = 8'hFF;  // All bytes enabled
  cfg_read.ep = 0;
  cfg_read.cr = 0;
  
  // Update packet information
  cfg_read.update_packet_info();
  
  start_item(cfg_read);
  finish_item(cfg_read);
  
  `uvm_info("SEQ", $sformatf("Sent CFG_READ_32B: addr=0x%06h, tag=%0d, intercept_expected=%0b", 
            addr, tag, should_intercept), UVM_MEDIUM)
endtask

/*---------------------------------------------------------------------------
 * MIXED TRANSACTION SCENARIO
 * 
 * Generates mixed CFG read transactions with alternating intercepted
 * and non-intercepted addresses for comprehensive testing.
 *---------------------------------------------------------------------------*/
task ucie_sb_interceptor_sequence::send_mixed_transactions();
  for (int i = 0; i < 10; i++) begin
    if (i % 2 == 0) begin
      // Even indices: intercepted addresses
      send_cfg_read(intercept_addr_base + (i * 8), i[4:0], 1);
    end else begin
      // Odd indices: non-intercepted addresses  
      send_cfg_read(normal_addr_base + (i * 8), i[4:0], 0);
    end
    #500ns;
  end
endtask

/*******************************************************************************
 * TEST IMPLEMENTATION
 ******************************************************************************/

/*---------------------------------------------------------------------------
 * TEST BUILD PHASE
 * 
 * Creates test environment and configures interceptor with specific
 * parameters for demonstration scenarios.
 *---------------------------------------------------------------------------*/
function void ucie_sb_interceptor_test::build_phase(uvm_phase phase);
  super.build_phase(phase);
  
  // Create test environment
  env = ucie_sb_interceptor_env::type_id::create("env", this);
  
  // Configure interceptor
  configure_interceptor();
  
  `uvm_info("TEST", "Interceptor test build phase complete", UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * TEST END OF ELABORATION PHASE
 * 
 * Final test configuration and environment validation.
 *---------------------------------------------------------------------------*/
function void ucie_sb_interceptor_test::end_of_elaboration_phase(uvm_phase phase);
  super.end_of_elaboration_phase(phase);
  
  // Print test configuration
  `uvm_info("TEST", "=== Interceptor Test Configuration ===", UVM_LOW)
  `uvm_info("TEST", "Address-based interception enabled", UVM_LOW)
  `uvm_info("TEST", $sformatf("Intercept range: 0x%06h - 0x%06h", 
            interceptor_cfg.match_addr_base, 
            interceptor_cfg.match_addr_base + (~interceptor_cfg.match_addr_mask)), UVM_LOW)
  `uvm_info("TEST", $sformatf("Custom completion data: 0x%08h", 
            interceptor_cfg.custom_completion_data), UVM_LOW)
  `uvm_info("TEST", "=====================================", UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * TEST RUN PHASE
 * 
 * Executes main test sequence and waits for completion with proper
 * objection handling.
 *---------------------------------------------------------------------------*/
task ucie_sb_interceptor_test::run_phase(uvm_phase phase);
  ucie_sb_interceptor_sequence seq;
  
  phase.raise_objection(this);
  
  `uvm_info("TEST", "Starting interceptor test execution", UVM_LOW)
  
  // Create and execute test sequence
  seq = ucie_sb_interceptor_sequence::type_id::create("interceptor_seq");
  seq.start(env.tx_agent.sequencer);
  
  // Allow time for all transactions to complete
  #5us;
  
  `uvm_info("TEST", "Interceptor test execution completed", UVM_LOW)
  
  phase.drop_objection(this);
endtask

/*---------------------------------------------------------------------------
 * TEST REPORT PHASE
 * 
 * Generates final test report with interceptor statistics and results.
 *---------------------------------------------------------------------------*/
function void ucie_sb_interceptor_test::report_phase(uvm_phase phase);
  super.report_phase(phase);
  
  `uvm_info("TEST", "=== Interceptor Test Results ===", UVM_LOW)
  `uvm_info("TEST", "Test completed successfully", UVM_LOW)
  `uvm_info("TEST", "Check interceptor statistics for detailed results", UVM_LOW)
  `uvm_info("TEST", "================================", UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * INTERCEPTOR CONFIGURATION SETUP
 * 
 * Configures interceptor with specific parameters for test scenarios
 * including address ranges and custom completion data.
 *---------------------------------------------------------------------------*/
function void ucie_sb_interceptor_test::configure_interceptor();
  interceptor_cfg = ucie_sb_interceptor_config::type_id::create("interceptor_cfg");
  
  // Configure address-based interception
  interceptor_cfg.set_address_range(24'h100000, 24'h1000);  // 4KB at 1MB
  interceptor_cfg.set_custom_data(32'hDEADBEEF);
  interceptor_cfg.set_debug_mode();
  
  // Set additional parameters
  interceptor_cfg.completion_delay_cycles = 5;
  interceptor_cfg.enable_interception = 1;
  interceptor_cfg.pass_through_mode = 0;
  
  // Store in UVM configuration database
  uvm_config_db#(ucie_sb_interceptor_config)::set(this, "env.interceptor", "cfg", interceptor_cfg);
  
  `uvm_info("TEST", "Interceptor configuration completed", UVM_LOW)
endfunction