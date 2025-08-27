/*******************************************************************************
 * UCIe Sideband Compare Result Model
 * 
 * OVERVIEW:
 *   Advanced UVM model for UCIe sideband TX/RX compare result handling.
 *   Acts as a gatekeeper and rewriter for sideband RX transactions, providing
 *   configurable compare result data based on a 2D array lookup mechanism.
 *
 * FUNCTIONALITY:
 *   • Gatekeeper: All sideband RX transactions pass through this model
 *   • Rewriter: Overwrites RX data field with compare result from array
 *   • Pass-through: Forwards unmodified RX when rewriting not needed
 *   • Enable Control: Can be disabled to simulate timeout/failure scenarios
 *   • Logger: Comprehensive logging of all operations and array accesses
 *
 * COMPARE RESULT ARRAY:
 *   • Structure: 64 rows (Y) × 63 columns (X)
 *   • Element Width: 32-bit values
 *   • Values: 32'hFFFF_FFFF (pass) or 32'h0000_0000 (fail)
 *   • Initialization: Based on expected voltage/clock phase ranges
 *   • Access: Sequential consumption based on DUT TX request parameters
 *
 * OPERATIONAL FLOW:
 *   1. DUT transmits data over mainband
 *   2. Remote DUT performs comparison
 *   3. DUT sends sideband TX request (volt_min, volt_max, clk_phase)
 *   4. Model intercepts RX and determines array region to read
 *   5. RX.data overwritten with array value, parity recalculated
 *   6. Processed RX sent to sequencer → driver → DUT
 *   7. DUT receives result and completes handshake
 *
 * COMPLIANCE:
 *   • IEEE 1800-2017 SystemVerilog
 *   • UVM 1.2 methodology
 *   • UCIe 1.1 specification
 *
 * AUTHOR: UCIe Sideband UVM Agent
 * VERSION: 1.0 - Compare Result Handling Model
 ******************************************************************************/

/*-----------------------------------------------------------------------------
 * COMPARE RESULT MODEL CONFIGURATION CLASS
 * 
 * Configuration management for compare result array initialization and
 * operational control parameters.
 *-----------------------------------------------------------------------------*/

class ucie_sb_compare_result_config extends uvm_object;
  `uvm_object_utils(ucie_sb_compare_result_config)
  
  /*---------------------------------------------------------------------------
   * OPERATIONAL MODE CONTROL
   * Model behavior and enable/disable control
   *---------------------------------------------------------------------------*/
  
  bit enable_model = 1;                    // Enable/disable model operation
  bit enable_debug = 1;                    // Enable debug messages
  bit enable_logging = 1;                  // Enable comprehensive logging
  bit pass_through_mode = 0;               // Pass-through mode (no rewriting)
  
  /*---------------------------------------------------------------------------
   * ARRAY INITIALIZATION PARAMETERS
   * Expected voltage and clock phase ranges for array fill logic
   *---------------------------------------------------------------------------*/
  
  int exp_volt_min = 10;                   // Expected voltage minimum (Y-axis)
  int exp_volt_max = 20;                   // Expected voltage maximum (Y-axis)
  int exp_clk_phase_min = 29;              // Expected clock phase minimum (X-axis)
  int exp_clk_phase_max = 33;              // Expected clock phase maximum (X-axis)
  
  /*---------------------------------------------------------------------------
   * INITIAL INDEX SELECTION PARAMETERS
   * Testbench-defined parameters for initial valid index range
   *---------------------------------------------------------------------------*/
  
  int volt_min = 10;                       // Initial voltage minimum for index selection
  int volt_max = 11;                       // Initial voltage maximum for index selection
  int clk_phase = 1;                       // Initial clock phase for X range calculation
  
  /*---------------------------------------------------------------------------
   * TARGET ADDRESS CONSTANTS
   * Specific CFG_READ_32B addresses that trigger rewriting
   *---------------------------------------------------------------------------*/
  
  parameter bit [23:0] TARGET_ADDR_0 = 24'h013140;  // First target address
  parameter bit [23:0] TARGET_ADDR_1 = 24'h013144;  // Second target address
  parameter bit [23:0] TARGET_ADDR_2 = 24'h013148;  // Third target address
  
  /*---------------------------------------------------------------------------
   * ARRAY STRUCTURE CONSTANTS
   * Fixed array dimensions and value definitions
   *---------------------------------------------------------------------------*/
  
  parameter int ARRAY_ROWS = 64;           // Y-axis: voltage range
  parameter int ARRAY_COLS = 63;           // X-axis: clock phase range
  parameter bit [31:0] PASS_VALUE = 32'hFFFF_FFFF;  // Compare pass result
  parameter bit [31:0] FAIL_VALUE = 32'h0000_0000;  // Compare fail result
  
  /*---------------------------------------------------------------------------
   * FIFO CONFIGURATION PARAMETERS
   * FIFO sizing and processing control
   *---------------------------------------------------------------------------*/
  
  int tx_fifo_size = 16;                   // TX FIFO depth
  int rx_fifo_size = 16;                   // RX FIFO depth
  real processing_delay_ns = 10.0;         // Processing delay between transactions
  
  /*---------------------------------------------------------------------------
   * LOGGING CONTROL PARAMETERS
   * Logging verbosity and file output control
   *---------------------------------------------------------------------------*/
  
  string log_file_name = "compare_result_model.log";  // Log file name
  bit log_to_file = 0;                     // Enable file logging
  bit log_array_init = 1;                  // Log array initialization
  bit log_runtime_access = 1;              // Log runtime array accesses
  
  /*---------------------------------------------------------------------------
   * CONSTRUCTOR - Initialize configuration with defaults
   *---------------------------------------------------------------------------*/
  function new(string name = "ucie_sb_compare_result_config");
    super.new(name);
  endfunction
  
  /*---------------------------------------------------------------------------
   * CONFIGURATION METHOD DECLARATIONS
   * External methods for configuration management
   *---------------------------------------------------------------------------*/
  
  extern function void set_expected_range(int volt_min, int volt_max, int clk_min, int clk_max);
  extern function void set_logging_options(bit enable_log, bit log_file, string file_name);
  extern function void set_operational_mode(bit enable, bit debug, bit pass_through);
  extern function void set_fifo_sizes(int tx_size, int rx_size);
  extern function void set_initial_index_params(int v_min, int v_max, int clk_ph);
  extern function bit is_target_address(bit [23:0] addr);
  extern function void print_config();
  extern function bit validate_config();

endclass : ucie_sb_compare_result_config

/*******************************************************************************
 * COMPARE RESULT MODEL MAIN CLASS
 * 
 * Main model component implementing gatekeeper, rewriter, and logging
 * functionality for UCIe sideband compare result handling.
 ******************************************************************************/

class ucie_sb_compare_result_model extends uvm_component;
  `uvm_component_utils(ucie_sb_compare_result_model)
  
  /*---------------------------------------------------------------------------
   * FIFO-BASED RECEIVER INFRASTRUCTURE
   * TLM Analysis FIFOs for transaction collection from monitors
   *---------------------------------------------------------------------------*/
  
  uvm_tlm_analysis_fifo #(ucie_sb_transaction) tx_fifo;  // TX requests from DUT monitor
  uvm_tlm_analysis_fifo #(ucie_sb_transaction) rx_fifo;  // RX responses from remote DUT monitor
  
  /*---------------------------------------------------------------------------
   * OUTPUT ANALYSIS PORT
   * Output analysis port for processed transactions
   *---------------------------------------------------------------------------*/
  
  uvm_analysis_port #(ucie_sb_transaction) processed_rx_ap;
  
  /*---------------------------------------------------------------------------
   * SEQUENCER INTERFACE
   * Output sequencer for processed RX transactions
   *---------------------------------------------------------------------------*/
  
  ucie_sb_sequencer rx_sequencer;          // RX sequencer for output
  
  /*---------------------------------------------------------------------------
   * COMPARE RESULT ARRAY
   * 2D array with linear index mapping (index = y*63 + x)
   *---------------------------------------------------------------------------*/
  
  bit [31:0] compare_result_array[64][63]; // 64 rows × 63 columns array
  bit array_initialized = 0;               // Array initialization status
  
  /*---------------------------------------------------------------------------
   * LINEAR INDEX ACCESS SYSTEM
   * Index-based access following row-major mapping (X first, then Y)
   *---------------------------------------------------------------------------*/
  
  int current_index = 0;                   // Current linear array index
  int valid_indices[$];                    // Queue of valid indices for current session
  int valid_index_ptr = 0;                 // Pointer to current valid index
  bit indices_initialized = 0;             // Valid indices initialization status
  
  /*---------------------------------------------------------------------------
   * THREE-ADDRESS GROUP TRACKING
   * State tracking for the three-address group logic
   *---------------------------------------------------------------------------*/
  
  int group_address_count = 0;             // Count of addresses processed in current group (0-2)
  bit [23:0] last_processed_addresses[3];  // Track last 3 processed addresses
  bit group_in_progress = 0;               // Flag indicating group processing active
  
  /*---------------------------------------------------------------------------
   * CONFIGURATION AND CONNECTIVITY
   * Configuration management and component connectivity
   *---------------------------------------------------------------------------*/
  
  ucie_sb_compare_result_config cfg;
  
  /*---------------------------------------------------------------------------
   * STATISTICS AND LOGGING INFRASTRUCTURE
   * Performance monitoring and operation logging
   *---------------------------------------------------------------------------*/
  
  // Transaction counters
  int tx_transactions_received = 0;        // TX transactions received via analysis port
  int rx_transactions_received = 0;        // RX transactions received via analysis port
  int tx_requests_processed = 0;           // TX requests processed for array setup
  int rx_transactions_processed = 0;       // RX transactions processed/rewritten
  int rx_transactions_passed_through = 0;  // RX transactions passed through unchanged
  int array_accesses_total = 0;            // Total array accesses performed
  int pass_results_returned = 0;           // PASS values returned to DUT
  int fail_results_returned = 0;           // FAIL values returned to DUT
  
  // Logging infrastructure
  int log_file_handle = 0;                 // Log file handle
  string log_buffer[$];                    // Log message buffer
  
  /*---------------------------------------------------------------------------
   * CONSTRUCTOR - Initialize compare result model component
   *---------------------------------------------------------------------------*/
  function new(string name = "ucie_sb_compare_result_model", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  /*---------------------------------------------------------------------------
   * EXTERNAL METHOD DECLARATIONS
   * All implementation methods declared as extern for clean interface
   *---------------------------------------------------------------------------*/
  
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);
  extern virtual function void end_of_elaboration_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);
  extern virtual function void report_phase(uvm_phase phase);
  extern virtual task process_transactions();
  extern virtual function void initialize_compare_array();
  extern virtual function void initialize_valid_indices();
  extern virtual task process_tx_transaction(ucie_sb_transaction tx_trans);
  extern virtual function ucie_sb_transaction process_rx_transaction(ucie_sb_transaction rx_trans);
  extern virtual function bit is_target_tx_transaction(ucie_sb_transaction tx_trans);
  extern virtual function bit [31:0] get_array_value_by_index(int index);
  extern virtual function void get_coordinates_from_index(int index, output int x, output int y);
  extern virtual function int get_index_from_coordinates(int x, int y);
  extern virtual function void update_parity(ucie_sb_transaction trans);
  extern virtual function void advance_group_state();
  extern virtual function void log_initialization();
  extern virtual function void log_tx_request(bit [4:0] opcode, bit [23:0] addr);
  extern virtual function void log_rx_processing(ucie_sb_transaction original, ucie_sb_transaction processed, int index, int x, int y);
  extern virtual function void log_message(string message, uvm_verbosity verbosity = UVM_LOW);
  extern virtual function void set_default_config();
  extern virtual function void print_statistics();
  extern virtual function void print_array_contents();

endclass : ucie_sb_compare_result_model

/*******************************************************************************
 * CONFIGURATION CLASS IMPLEMENTATION
 ******************************************************************************/

/*---------------------------------------------------------------------------
 * SET EXPECTED RANGE CONFIGURATION
 * 
 * Configures expected voltage and clock phase ranges for array initialization.
 *---------------------------------------------------------------------------*/
function void ucie_sb_compare_result_config::set_expected_range(int volt_min, int volt_max, int clk_min, int clk_max);
  exp_volt_min = volt_min;
  exp_volt_max = volt_max;
  exp_clk_phase_min = clk_min;
  exp_clk_phase_max = clk_max;
  `uvm_info("COMPARE_RESULT_CONFIG", $sformatf("Set expected range: volt[%0d:%0d], clk_phase[%0d:%0d]", 
            volt_min, volt_max, clk_min, clk_max), UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * SET LOGGING OPTIONS CONFIGURATION
 * 
 * Configures logging behavior and file output options.
 *---------------------------------------------------------------------------*/
function void ucie_sb_compare_result_config::set_logging_options(bit enable_log, bit log_file, string file_name);
  enable_logging = enable_log;
  log_to_file = log_file;
  log_file_name = file_name;
  `uvm_info("COMPARE_RESULT_CONFIG", $sformatf("Set logging: enable=%0b, file=%0b, name=%s", 
            enable_log, log_file, file_name), UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * SET OPERATIONAL MODE CONFIGURATION
 * 
 * Configures model operational behavior and debug settings.
 *---------------------------------------------------------------------------*/
function void ucie_sb_compare_result_config::set_operational_mode(bit enable, bit debug, bit pass_through);
  enable_model = enable;
  enable_debug = debug;
  pass_through_mode = pass_through;
  `uvm_info("COMPARE_RESULT_CONFIG", $sformatf("Set operational mode: enable=%0b, debug=%0b, pass_through=%0b", 
            enable, debug, pass_through), UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * SET FIFO SIZES CONFIGURATION
 * 
 * Configures TX and RX FIFO depths for transaction buffering.
 *---------------------------------------------------------------------------*/
function void ucie_sb_compare_result_config::set_fifo_sizes(int tx_size, int rx_size);
  tx_fifo_size = tx_size;
  rx_fifo_size = rx_size;
  `uvm_info("COMPARE_RESULT_CONFIG", $sformatf("Set FIFO sizes: TX=%0d, RX=%0d", tx_size, rx_size), UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * SET INITIAL INDEX PARAMETERS CONFIGURATION
 * 
 * Configures testbench-defined parameters for initial valid index range.
 *---------------------------------------------------------------------------*/
function void ucie_sb_compare_result_config::set_initial_index_params(int v_min, int v_max, int clk_ph);
  volt_min = v_min;
  volt_max = v_max;
  clk_phase = clk_ph;
  `uvm_info("COMPARE_RESULT_CONFIG", $sformatf("Set initial index params: volt[%0d:%0d], clk_phase=%0d", 
            v_min, v_max, clk_ph), UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * TARGET ADDRESS CHECK
 * 
 * Checks if given address is one of the three target addresses.
 *---------------------------------------------------------------------------*/
function bit ucie_sb_compare_result_config::is_target_address(bit [23:0] addr);
  return (addr == TARGET_ADDR_0) || (addr == TARGET_ADDR_1) || (addr == TARGET_ADDR_2);
endfunction

/*---------------------------------------------------------------------------
 * CONFIGURATION VALIDATION
 * 
 * Validates configuration parameters for correctness and consistency.
 *---------------------------------------------------------------------------*/
function bit ucie_sb_compare_result_config::validate_config();
  bit valid = 1;
  
  // Validate voltage range
  if (exp_volt_min < 0 || exp_volt_max >= ARRAY_ROWS || exp_volt_min > exp_volt_max) begin
    `uvm_error("COMPARE_RESULT_CONFIG", $sformatf("Invalid voltage range: [%0d:%0d], must be in [0:%0d]", 
               exp_volt_min, exp_volt_max, ARRAY_ROWS-1))
    valid = 0;
  end
  
  // Validate clock phase range
  if (exp_clk_phase_min < 0 || exp_clk_phase_max >= ARRAY_COLS || exp_clk_phase_min > exp_clk_phase_max) begin
    `uvm_error("COMPARE_RESULT_CONFIG", $sformatf("Invalid clock phase range: [%0d:%0d], must be in [0:%0d]", 
               exp_clk_phase_min, exp_clk_phase_max, ARRAY_COLS-1))
    valid = 0;
  end
  
  return valid;
endfunction

/*---------------------------------------------------------------------------
 * CONFIGURATION DEBUG REPORTING
 * 
 * Generates comprehensive configuration summary for debugging.
 *---------------------------------------------------------------------------*/
function void ucie_sb_compare_result_config::print_config();
  `uvm_info("COMPARE_RESULT_CONFIG", "=== Compare Result Model Configuration ===", UVM_LOW)
  `uvm_info("COMPARE_RESULT_CONFIG", $sformatf("Model enabled: %0b", enable_model), UVM_LOW)
  `uvm_info("COMPARE_RESULT_CONFIG", $sformatf("Debug enabled: %0b", enable_debug), UVM_LOW)
  `uvm_info("COMPARE_RESULT_CONFIG", $sformatf("Pass-through mode: %0b", pass_through_mode), UVM_LOW)
  `uvm_info("COMPARE_RESULT_CONFIG", $sformatf("Expected voltage range: [%0d:%0d]", exp_volt_min, exp_volt_max), UVM_LOW)
  `uvm_info("COMPARE_RESULT_CONFIG", $sformatf("Expected clock phase range: [%0d:%0d]", exp_clk_phase_min, exp_clk_phase_max), UVM_LOW)
  `uvm_info("COMPARE_RESULT_CONFIG", $sformatf("Array dimensions: %0d × %0d", ARRAY_ROWS, ARRAY_COLS), UVM_LOW)
  `uvm_info("COMPARE_RESULT_CONFIG", $sformatf("Logging enabled: %0b, file: %0b (%s)", enable_logging, log_to_file, log_file_name), UVM_LOW)
  `uvm_info("COMPARE_RESULT_CONFIG", "=============================================", UVM_LOW)
endfunction

/*******************************************************************************
 * MAIN MODEL IMPLEMENTATION
 ******************************************************************************/

/*---------------------------------------------------------------------------
 * UVM BUILD PHASE IMPLEMENTATION
 * 
 * Component construction, analysis FIFO creation, and configuration retrieval.
 *---------------------------------------------------------------------------*/
function void ucie_sb_compare_result_model::build_phase(uvm_phase phase);
  super.build_phase(phase);
  
  // Get model configuration or create default
  if (!uvm_config_db#(ucie_sb_compare_result_config)::get(this, "", "cfg", cfg)) begin
    set_default_config();
  end
  
  // Validate configuration
  if (!cfg.validate_config()) begin
    `uvm_fatal("COMPARE_RESULT_MODEL", "Invalid configuration parameters")
  end
  
  // Create TLM Analysis FIFOs with configured sizes
  tx_fifo = new("tx_fifo", this, cfg.tx_fifo_size);
  rx_fifo = new("rx_fifo", this, cfg.rx_fifo_size);
  
  // Create output analysis port
  processed_rx_ap = new("processed_rx_ap", this);
  
  // Create sequencer
  rx_sequencer = ucie_sb_sequencer::type_id::create("rx_sequencer", this);
  
  `uvm_info("COMPARE_RESULT_MODEL", "Compare result model build phase complete", UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * UVM CONNECT PHASE IMPLEMENTATION
 * 
 * Component connectivity establishment.
 *---------------------------------------------------------------------------*/
function void ucie_sb_compare_result_model::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  `uvm_info("COMPARE_RESULT_MODEL", "Compare result model connect phase complete", UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * UVM END OF ELABORATION PHASE IMPLEMENTATION
 * 
 * Final initialization and array setup.
 *---------------------------------------------------------------------------*/
function void ucie_sb_compare_result_model::end_of_elaboration_phase(uvm_phase phase);
  super.end_of_elaboration_phase(phase);
  
  // Initialize compare result array
  initialize_compare_array();
  
  // Initialize valid indices based on testbench parameters
  initialize_valid_indices();
  
  // Print configuration if debug enabled
  if (cfg.enable_debug) begin
    cfg.print_config();
  end
  
  // Initialize logging
  if (cfg.enable_logging && cfg.log_to_file) begin
    log_file_handle = $fopen(cfg.log_file_name, "w");
    if (log_file_handle == 0) begin
      `uvm_warning("COMPARE_RESULT_MODEL", $sformatf("Failed to open log file: %s", cfg.log_file_name))
    end
  end
  
  `uvm_info("COMPARE_RESULT_MODEL", "Compare result model end of elaboration phase complete", UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * UVM RUN PHASE IMPLEMENTATION
 * 
 * Main model execution phase. Starts FIFO-based transaction processing.
 *---------------------------------------------------------------------------*/
task ucie_sb_compare_result_model::run_phase(uvm_phase phase);
  super.run_phase(phase);
  
  `uvm_info("COMPARE_RESULT_MODEL", "Starting compare result model run phase", UVM_LOW)
  
  // Start FIFO-based transaction processing
  process_transactions();
endtask

/*---------------------------------------------------------------------------
 * UVM REPORT PHASE IMPLEMENTATION
 * 
 * Final statistics and status reporting.
 *---------------------------------------------------------------------------*/
function void ucie_sb_compare_result_model::report_phase(uvm_phase phase);
  super.report_phase(phase);
  
  if (cfg.enable_logging) begin
    print_statistics();
  end
  
  // Close log file if opened
  if (log_file_handle != 0) begin
    $fclose(log_file_handle);
  end
endfunction



/*---------------------------------------------------------------------------
 * MAIN TRANSACTION PROCESSING IMPLEMENTATION
 * 
 * FIFO-based receiver that blocks on FIFO get() to process transactions
 * in-order. Implements gatekeeper functionality for all RX transactions.
 *---------------------------------------------------------------------------*/
task ucie_sb_compare_result_model::process_transactions();
  ucie_sb_transaction tx_trans, rx_trans;
  realtime start_time, process_time;
  
  forever begin
    // Block on TX FIFO get() - collects TX requests from DUT
    tx_fifo.get(tx_trans);
    tx_transactions_received++;
    start_time = $realtime;
    
    if (cfg.enable_debug) begin
      `uvm_info("COMPARE_RESULT_MODEL", $sformatf("Received TX transaction: opcode=%0d, addr=0x%06h", 
                tx_trans.opcode, tx_trans.addr), UVM_HIGH)
    end
    
    // Process TX transaction - check if it's a target address
    process_tx_transaction(tx_trans);
    
    // Block on RX FIFO get() - collects RX responses from remote DUT (before modification)
    rx_fifo.get(rx_trans);
    rx_transactions_received++;
    
    if (cfg.enable_debug) begin
      `uvm_info("COMPARE_RESULT_MODEL", $sformatf("Received RX transaction: opcode=%0d, data=0x%08h", 
                rx_trans.opcode, rx_trans.data[31:0]), UVM_HIGH)
    end
    
    // Process RX transaction based on model configuration
    if (!cfg.enable_model) begin
      // Model disabled - RX transactions pass-through directly
      rx_sequencer.send_request(rx_trans);
      processed_rx_ap.write(rx_trans);
      rx_transactions_passed_through++;
      
      log_message($sformatf("Model disabled - RX pass-through"), UVM_MEDIUM);
      
    end else begin
      // Model enabled - check if TX was a target address for rewriting
      bit should_rewrite = is_target_tx_transaction(tx_trans) && (rx_trans.opcode == COMPLETION_32B);
      
      if (should_rewrite) begin
        // Rewrite RX data with array value and recalculate parity
        ucie_sb_transaction processed_trans = process_rx_transaction(rx_trans);
        
        // Send processed transaction to sequencer → driver → DUT
        rx_sequencer.send_request(processed_trans);
        processed_rx_ap.write(processed_trans);
        
        rx_transactions_processed++;
        
        // Advance group state after processing
        advance_group_state();
        
      end else begin
        // Pass-through: RX transaction passes unchanged
        rx_sequencer.send_request(rx_trans);
        processed_rx_ap.write(rx_trans);
        rx_transactions_passed_through++;
        
        if (cfg.enable_debug) begin
          `uvm_info("COMPARE_RESULT_MODEL", $sformatf("Non-target TX or non-COMPLETION RX - pass-through"), UVM_HIGH)
        end
      end
    end
    
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
 * Processes TX transactions to extract request parameters and set up
 * array access region for subsequent RX processing.
 *---------------------------------------------------------------------------*/
task ucie_sb_compare_result_model::process_tx_transaction(ucie_sb_transaction tx_trans);
  tx_requests_processed++;
  
  if (cfg.enable_debug) begin
    `uvm_info("COMPARE_RESULT_MODEL", $sformatf("TX processed: opcode=%0d, addr=0x%06h", 
              tx_trans.opcode, tx_trans.addr), UVM_MEDIUM)
  end
  
  // Log TX request
  if (cfg.enable_logging) begin
    log_tx_request(tx_trans.opcode, tx_trans.addr);
  end
endtask

/*---------------------------------------------------------------------------
 * COMPARE ARRAY INITIALIZATION IMPLEMENTATION
 * 
 * Initializes the 64×63 compare result array based on expected ranges.
 * Fills specified region with PASS values, elsewhere with FAIL values.
 *---------------------------------------------------------------------------*/
function void ucie_sb_compare_result_model::initialize_compare_array();
  int pass_count = 0;
  int fail_count = 0;
  
  `uvm_info("COMPARE_RESULT_MODEL", "Initializing compare result array...", UVM_LOW)
  
  // Initialize entire array to FAIL values first
  for (int y = 0; y < cfg.ARRAY_ROWS; y++) begin
    for (int x = 0; x < cfg.ARRAY_COLS; x++) begin
      compare_result_array[y][x] = cfg.FAIL_VALUE;
      fail_count++;
    end
  end
  
  // Fill expected region with PASS values
  for (int y = cfg.exp_volt_min; y <= cfg.exp_volt_max; y++) begin
    for (int x = cfg.exp_clk_phase_min; x <= cfg.exp_clk_phase_max; x++) begin
      if (y >= 0 && y < cfg.ARRAY_ROWS && x >= 0 && x < cfg.ARRAY_COLS) begin
        compare_result_array[y][x] = cfg.PASS_VALUE;
        pass_count++;
        fail_count--;
      end
    end
  end
  
  array_initialized = 1;
  
  `uvm_info("COMPARE_RESULT_MODEL", $sformatf("Array initialized: %0d PASS, %0d FAIL values", 
            pass_count, fail_count), UVM_LOW)
  
  // Log initialization details
  if (cfg.enable_logging) begin
    log_initialization();
  end
  
  if (cfg.enable_debug) begin
    print_array_contents();
  end
endfunction

/*---------------------------------------------------------------------------
 * TX REQUEST PROCESSING IMPLEMENTATION
 * 
 * Processes DUT TX request parameters to set up array access region.
 * Determines Y and X ranges for sequential array access.
 *---------------------------------------------------------------------------*/
function void ucie_sb_compare_result_model::process_tx_request(int volt_min, int volt_max, int clk_phase);
  latest_volt_min = volt_min;
  latest_volt_max = volt_max;
  latest_clk_phase = clk_phase;
  
  // Set Y range directly from voltage parameters
  access_y_min = volt_min;
  access_y_max = volt_max;
  
  // Set X range based on clk_phase around center 31
  access_x_min = 31 - clk_phase;
  access_x_max = 31 + clk_phase;
  
  // Clamp to valid array bounds
  if (access_y_min < 0) access_y_min = 0;
  if (access_y_max >= cfg.ARRAY_ROWS) access_y_max = cfg.ARRAY_ROWS - 1;
  if (access_x_min < 0) access_x_min = 0;
  if (access_x_max >= cfg.ARRAY_COLS) access_x_max = cfg.ARRAY_COLS - 1;
  
  // Initialize sequential access position
  current_y_pos = access_y_min;
  current_x_pos = access_x_min;
  tx_request_pending = 1;
  
  if (cfg.enable_debug) begin
    `uvm_info("COMPARE_RESULT_MODEL", $sformatf("TX request processed: volt[%0d:%0d], clk_phase=%0d", 
              volt_min, volt_max, clk_phase), UVM_MEDIUM)
    `uvm_info("COMPARE_RESULT_MODEL", $sformatf("Access region: Y[%0d:%0d], X[%0d:%0d]", 
              access_y_min, access_y_max, access_x_min, access_x_max), UVM_MEDIUM)
  end
  
  // Log TX request
  if (cfg.enable_logging) begin
    log_tx_request(volt_min, volt_max, clk_phase);
  end
endfunction

/*---------------------------------------------------------------------------
 * RX TRANSACTION PROCESSING IMPLEMENTATION
 * 
 * Rewriter: Only data field of RX is rewritten with array value.
 * After rewriting data, parity is recalculated. Other fields remain unchanged.
 * Logger: Logs original RX data/parity, rewritten RX data/parity, and array index.
 *---------------------------------------------------------------------------*/
function ucie_sb_transaction ucie_sb_compare_result_model::process_rx_transaction(ucie_sb_transaction rx_trans);
  ucie_sb_transaction processed_trans;
  bit [31:0] original_data;
  bit [31:0] new_data;
  bit original_parity;
  bit new_parity;
  int access_x, access_y;
  
  // Create copy of original transaction (other fields remain unchanged)
  processed_trans = rx_trans.copy();
  original_data = rx_trans.data[31:0];
  original_parity = rx_trans.dp;  // Assuming dp is data parity field
  
  // Get array value using current index and capture coordinates
  new_data = get_array_value_by_index(current_index);
  get_coordinates_from_index(current_index, access_x, access_y);
  
  // Rewriter: Only data field is rewritten
  processed_trans.data[31:0] = new_data;
  
  // Recalculate parity to ensure validity
  update_parity(processed_trans);
  new_parity = processed_trans.dp;
  
  // Update statistics
  if (new_data == cfg.PASS_VALUE) begin
    pass_results_returned++;
  end else begin
    fail_results_returned++;
  end
  
  array_accesses_total++;
  
  // Logger: Whenever rewriting occurs, log original/rewritten data/parity and array index
  if (cfg.enable_logging) begin
    log_rx_processing(rx_trans, processed_trans, current_index, access_x, access_y);
  end
  
  if (cfg.enable_debug) begin
    `uvm_info("COMPARE_RESULT_MODEL", $sformatf("RX rewritten: index=%0d, array[%0d][%0d]=0x%08h, data: 0x%08h→0x%08h, parity: %0b→%0b", 
              current_index, access_y, access_x, new_data, original_data, new_data, original_parity, new_parity), UVM_MEDIUM)
  end
  
  return processed_trans;
endfunction



/*---------------------------------------------------------------------------
 * PARITY UPDATE IMPLEMENTATION
 * 
 * Recalculates parity for transaction after data field modification.
 *---------------------------------------------------------------------------*/
function void ucie_sb_compare_result_model::update_parity(ucie_sb_transaction trans);
  // Call transaction's built-in parity update method
  // This assumes the transaction class has an update_packet_info() method
  trans.update_packet_info();
endfunction

/*---------------------------------------------------------------------------
 * INITIALIZATION LOGGING IMPLEMENTATION
 * 
 * Logs array initialization details including parameters and fill results.
 *---------------------------------------------------------------------------*/
function void ucie_sb_compare_result_model::log_initialization();
  string msg;
  
  msg = $sformatf("=== ARRAY INITIALIZATION ===");
  log_message(msg, UVM_LOW);
  
  msg = $sformatf("Expected ranges: volt[%0d:%0d], clk_phase[%0d:%0d]", 
                  cfg.exp_volt_min, cfg.exp_volt_max, cfg.exp_clk_phase_min, cfg.exp_clk_phase_max);
  log_message(msg, UVM_LOW);
  
  msg = $sformatf("Array dimensions: %0d × %0d", cfg.ARRAY_ROWS, cfg.ARRAY_COLS);
  log_message(msg, UVM_LOW);
  
  msg = $sformatf("PASS value: 0x%08h, FAIL value: 0x%08h", cfg.PASS_VALUE, cfg.FAIL_VALUE);
  log_message(msg, UVM_LOW);
  
  // Calculate and log fill statistics
  int pass_elements = (cfg.exp_volt_max - cfg.exp_volt_min + 1) * (cfg.exp_clk_phase_max - cfg.exp_clk_phase_min + 1);
  int total_elements = cfg.ARRAY_ROWS * cfg.ARRAY_COLS;
  int fail_elements = total_elements - pass_elements;
  
  msg = $sformatf("Fill result: %0d PASS elements, %0d FAIL elements", pass_elements, fail_elements);
  log_message(msg, UVM_LOW);
  
  msg = $sformatf("=============================");
  log_message(msg, UVM_LOW);
endfunction

/*---------------------------------------------------------------------------
 * TX REQUEST LOGGING IMPLEMENTATION
 * 
 * Logs TX request parameters and calculated access region.
 *---------------------------------------------------------------------------*/
function void ucie_sb_compare_result_model::log_tx_request(bit [4:0] opcode, bit [23:0] addr);
  string msg;
  
  msg = $sformatf("=== TX REQUEST ===");
  log_message(msg, UVM_MEDIUM);
  
  msg = $sformatf("TX opcode: %0d (0x%02h)", opcode, opcode);
  log_message(msg, UVM_MEDIUM);
  
  msg = $sformatf("TX addr: 0x%06h", addr);
  log_message(msg, UVM_MEDIUM);
  
  if (cfg.is_target_address(addr)) begin
    msg = $sformatf("Target address: YES (will trigger rewriting)");
  end else begin
    msg = $sformatf("Target address: NO (will pass-through)");
  end
  log_message(msg, UVM_MEDIUM);
  
  msg = $sformatf("==================");
  log_message(msg, UVM_MEDIUM);
endfunction

/*---------------------------------------------------------------------------
 * RX PROCESSING LOGGING IMPLEMENTATION
 * 
 * Logger: Whenever rewriting occurs, logs:
 * - Original RX data/parity
 * - Rewritten RX data/parity  
 * - Array index (Y, X) used for substitution
 *---------------------------------------------------------------------------*/
function void ucie_sb_compare_result_model::log_rx_processing(ucie_sb_transaction original, ucie_sb_transaction processed, int index, int x, int y);
  string msg;
  
  msg = $sformatf("RX_REWRITE: array index=%0d, coordinates(%0d,%0d) used for substitution", index, x, y);
  log_message(msg, UVM_MEDIUM);
  
  msg = $sformatf("  Original RX data/parity: 0x%08h / %0b", original.data[31:0], original.dp);
  log_message(msg, UVM_MEDIUM);
  
  msg = $sformatf("  Rewritten RX data/parity: 0x%08h / %0b", processed.data[31:0], processed.dp);
  log_message(msg, UVM_MEDIUM);
endfunction

/*---------------------------------------------------------------------------
 * GENERAL LOGGING IMPLEMENTATION
 * 
 * General purpose logging method supporting both UVM and file output.
 *---------------------------------------------------------------------------*/
function void ucie_sb_compare_result_model::log_message(string message, uvm_verbosity verbosity = UVM_LOW);
  // Always log to UVM
  `uvm_info("COMPARE_RESULT_MODEL", message, verbosity)
  
  // Log to file if enabled and file is open
  if (cfg.log_to_file && log_file_handle != 0) begin
    $fwrite(log_file_handle, "[%0t] %s\n", $time, message);
    $fflush(log_file_handle);
  end
  
  // Add to buffer for potential later use
  log_buffer.push_back($sformatf("[%0t] %s", $time, message));
endfunction

/*---------------------------------------------------------------------------
 * DEFAULT CONFIGURATION SETUP IMPLEMENTATION
 * 
 * Creates default model configuration when none provided.
 *---------------------------------------------------------------------------*/
function void ucie_sb_compare_result_model::set_default_config();
  cfg = ucie_sb_compare_result_config::type_id::create("cfg");
  cfg.set_expected_range(10, 20, 29, 33);  // Example values from specification
  cfg.set_logging_options(1, 0, "compare_result_model.log");
  cfg.set_operational_mode(1, 1, 0);
  `uvm_info("COMPARE_RESULT_MODEL", "Using default compare result model configuration", UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * STATISTICS REPORTING IMPLEMENTATION
 * 
 * Generates comprehensive statistics report.
 *---------------------------------------------------------------------------*/
function void ucie_sb_compare_result_model::print_statistics();
  `uvm_info("COMPARE_RESULT_MODEL", "=== Compare Result Model Statistics ===", UVM_LOW)
  `uvm_info("COMPARE_RESULT_MODEL", $sformatf("RX transactions received: %0d", rx_transactions_received), UVM_LOW)
  `uvm_info("COMPARE_RESULT_MODEL", $sformatf("RX transactions processed: %0d", rx_transactions_processed), UVM_LOW)
  `uvm_info("COMPARE_RESULT_MODEL", $sformatf("RX transactions passed through: %0d", rx_transactions_passed_through), UVM_LOW)
  `uvm_info("COMPARE_RESULT_MODEL", $sformatf("Array accesses total: %0d", array_accesses_total), UVM_LOW)
  `uvm_info("COMPARE_RESULT_MODEL", $sformatf("PASS results returned: %0d", pass_results_returned), UVM_LOW)
  `uvm_info("COMPARE_RESULT_MODEL", $sformatf("FAIL results returned: %0d", fail_results_returned), UVM_LOW)
  `uvm_info("COMPARE_RESULT_MODEL", $sformatf("Array initialized: %0b", array_initialized), UVM_LOW)
  `uvm_info("COMPARE_RESULT_MODEL", $sformatf("Current access position: [%0d][%0d]", current_y_pos, current_x_pos), UVM_LOW)
  `uvm_info("COMPARE_RESULT_MODEL", "=======================================", UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * ARRAY CONTENTS DISPLAY IMPLEMENTATION
 * 
 * Displays compare result array contents for debugging (abbreviated view).
 *---------------------------------------------------------------------------*/
function void ucie_sb_compare_result_model::print_array_contents();
  string row_str;
  int pass_count, fail_count;
  
  `uvm_info("COMPARE_RESULT_MODEL", "=== Compare Result Array Contents (Summary) ===", UVM_LOW)
  
  // Count pass/fail values in expected region
  for (int y = cfg.exp_volt_min; y <= cfg.exp_volt_max; y++) begin
    for (int x = cfg.exp_clk_phase_min; x <= cfg.exp_clk_phase_max; x++) begin
      if (compare_result_array[y][x] == cfg.PASS_VALUE) pass_count++;
      else fail_count++;
    end
  end
  
  `uvm_info("COMPARE_RESULT_MODEL", $sformatf("Expected region [%0d:%0d][%0d:%0d]: %0d PASS, %0d FAIL", 
            cfg.exp_volt_min, cfg.exp_volt_max, cfg.exp_clk_phase_min, cfg.exp_clk_phase_max,
            pass_count, fail_count), UVM_LOW)
  
  // Show a few sample rows from expected region
  for (int y = cfg.exp_volt_min; y <= cfg.exp_volt_min + 2 && y <= cfg.exp_volt_max; y++) begin
    row_str = $sformatf("Row[%02d]: ", y);
    for (int x = cfg.exp_clk_phase_min; x <= cfg.exp_clk_phase_max; x++) begin
      if (compare_result_array[y][x] == cfg.PASS_VALUE) begin
        row_str = {row_str, "P "};
      end else begin
        row_str = {row_str, "F "};
      end
    end
    `uvm_info("COMPARE_RESULT_MODEL", row_str, UVM_LOW)
  end
  
  `uvm_info("COMPARE_RESULT_MODEL", "============================================", UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * INITIALIZE VALID INDICES IMPLEMENTATION
 * 
 * Initializes the valid indices queue based on testbench parameters.
 * Uses linear index mapping: index = y*63 + x
 *---------------------------------------------------------------------------*/
function void ucie_sb_compare_result_model::initialize_valid_indices();
  int y_min, y_max, x_min, x_max;
  int index;
  
  // Calculate Y range from testbench parameters
  y_min = cfg.volt_max;  // Note: spec shows volt_max as minimum Y
  y_max = cfg.volt_min;  // Note: spec shows volt_min as maximum Y
  
  // Calculate X range from clk_phase around center 31
  x_min = 31 - cfg.clk_phase;
  x_max = 31 + cfg.clk_phase;
  
  // Clamp to valid array bounds
  if (y_min < 0) y_min = 0;
  if (y_max >= cfg.ARRAY_ROWS) y_max = cfg.ARRAY_ROWS - 1;
  if (x_min < 0) x_min = 0;
  if (x_max >= cfg.ARRAY_COLS) x_max = cfg.ARRAY_COLS - 1;
  
  // Clear existing valid indices
  valid_indices.delete();
  
  // Generate valid indices in X-major then Y order
  for (int y = y_min; y <= y_max; y++) begin
    for (int x = x_min; x <= x_max; x++) begin
      index = get_index_from_coordinates(x, y);
      valid_indices.push_back(index);
    end
  end
  
  // Reset pointer
  valid_index_ptr = 0;
  current_index = (valid_indices.size() > 0) ? valid_indices[0] : 0;
  indices_initialized = 1;
  
  if (cfg.enable_debug) begin
    `uvm_info("COMPARE_RESULT_MODEL", $sformatf("Initialized %0d valid indices: Y[%0d:%0d], X[%0d:%0d]", 
              valid_indices.size(), y_min, y_max, x_min, x_max), UVM_LOW)
  end
  
  if (cfg.enable_logging) begin
    log_message($sformatf("Valid indices initialized: %0d entries, starting index=%0d", 
                valid_indices.size(), current_index), UVM_MEDIUM);
  end
endfunction

/*---------------------------------------------------------------------------
 * TARGET TX TRANSACTION CHECK IMPLEMENTATION
 * 
 * Checks if TX transaction matches target conditions for rewriting.
 *---------------------------------------------------------------------------*/
function bit ucie_sb_compare_result_model::is_target_tx_transaction(ucie_sb_transaction tx_trans);
  return (tx_trans.opcode == CFG_READ_32B) && cfg.is_target_address(tx_trans.addr);
endfunction

/*---------------------------------------------------------------------------
 * GET ARRAY VALUE BY INDEX IMPLEMENTATION
 * 
 * Retrieves array value using linear index mapping.
 *---------------------------------------------------------------------------*/
function bit [31:0] ucie_sb_compare_result_model::get_array_value_by_index(int index);
  int x, y;
  get_coordinates_from_index(index, x, y);
  return compare_result_array[y][x];
endfunction

/*---------------------------------------------------------------------------
 * GET COORDINATES FROM INDEX IMPLEMENTATION
 * 
 * Converts linear index to (x, y) coordinates using index = y*63 + x.
 *---------------------------------------------------------------------------*/
function void ucie_sb_compare_result_model::get_coordinates_from_index(int index, output int x, output int y);
  y = index / cfg.ARRAY_COLS;
  x = index % cfg.ARRAY_COLS;
endfunction

/*---------------------------------------------------------------------------
 * GET INDEX FROM COORDINATES IMPLEMENTATION
 * 
 * Converts (x, y) coordinates to linear index using index = y*63 + x.
 *---------------------------------------------------------------------------*/
function int ucie_sb_compare_result_model::get_index_from_coordinates(int x, int y);
  return y * cfg.ARRAY_COLS + x;
endfunction

/*---------------------------------------------------------------------------
 * ADVANCE GROUP STATE IMPLEMENTATION
 * 
 * Advances the three-address group state and increments array index.
 *---------------------------------------------------------------------------*/
function void ucie_sb_compare_result_model::advance_group_state();
  group_address_count++;
  
  if (group_address_count >= 3) begin
    // Completed a group of three addresses - advance to next array index
    group_address_count = 0;
    valid_index_ptr++;
    
    if (valid_index_ptr < valid_indices.size()) begin
      current_index = valid_indices[valid_index_ptr];
      
      if (cfg.enable_debug) begin
        int x, y;
        get_coordinates_from_index(current_index, x, y);
        `uvm_info("COMPARE_RESULT_MODEL", $sformatf("Advanced to next group: index=%0d, coords(%0d,%0d)", 
                  current_index, x, y), UVM_MEDIUM)
      end
    end else begin
      `uvm_warning("COMPARE_RESULT_MODEL", "All valid indices have been used - wrapping to start")
      valid_index_ptr = 0;
      current_index = (valid_indices.size() > 0) ? valid_indices[0] : 0;
    end
  end
  
  if (cfg.enable_debug) begin
    `uvm_info("COMPARE_RESULT_MODEL", $sformatf("Group state: address_count=%0d/3, index=%0d", 
              group_address_count, current_index), UVM_HIGH)
  end
endfunction