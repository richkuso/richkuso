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
   * ANALYSIS PORT INTERFACES
   * Input analysis ports for TX and RX transaction collection from monitors
   *---------------------------------------------------------------------------*/
  
  uvm_analysis_imp_tx #(ucie_sb_transaction, ucie_sb_compare_result_model) tx_analysis_imp;
  uvm_analysis_imp_rx #(ucie_sb_transaction, ucie_sb_compare_result_model) rx_analysis_imp;
  uvm_analysis_port #(ucie_sb_transaction) processed_rx_ap;
  
  /*---------------------------------------------------------------------------
   * FIFO INFRASTRUCTURE
   * TLM FIFOs for transaction storage and processing
   *---------------------------------------------------------------------------*/
  
  uvm_tlm_fifo #(ucie_sb_transaction) tx_fifo;     // TX transaction FIFO from monitor
  uvm_tlm_fifo #(ucie_sb_transaction) rx_fifo;     // RX transaction FIFO from monitor
  
  /*---------------------------------------------------------------------------
   * SEQUENCER INTERFACE
   * Output sequencer for processed RX transactions
   *---------------------------------------------------------------------------*/
  
  ucie_sb_sequencer rx_sequencer;          // RX sequencer for output
  
  /*---------------------------------------------------------------------------
   * COMPARE RESULT ARRAY
   * 2D array storing compare results with access tracking
   *---------------------------------------------------------------------------*/
  
  bit [31:0] compare_result_array[64][63]; // 64 rows × 63 columns array
  int current_y_pos = 0;                   // Current Y position for sequential access
  int current_x_pos = 0;                   // Current X position for sequential access
  int access_y_min = 0;                    // Current access Y range minimum
  int access_y_max = 0;                    // Current access Y range maximum
  int access_x_min = 0;                    // Current access X range minimum
  int access_x_max = 0;                    // Current access X range maximum
  bit array_initialized = 0;               // Array initialization status
  
  /*---------------------------------------------------------------------------
   * TX REQUEST PARAMETERS
   * Latest TX request parameters for array access control
   *---------------------------------------------------------------------------*/
  
  int latest_volt_min = 0;                 // Latest voltage minimum from TX
  int latest_volt_max = 0;                 // Latest voltage maximum from TX
  int latest_clk_phase = 0;                // Latest clock phase from TX
  bit tx_request_pending = 0;              // TX request pending processing
  
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
  extern virtual function void write_tx(ucie_sb_transaction trans);
  extern virtual function void write_rx(ucie_sb_transaction trans);
  extern virtual task process_transactions();
  extern virtual function void initialize_compare_array();
  extern virtual task process_tx_transaction(ucie_sb_transaction tx_trans);
  extern virtual function ucie_sb_transaction process_rx_transaction(ucie_sb_transaction rx_trans);
  extern virtual function bit [31:0] get_next_array_value();
  extern virtual function void update_parity(ucie_sb_transaction trans);
  extern virtual function void log_initialization();
  extern virtual function void log_tx_request(int volt_min, int volt_max, int clk_phase);
  extern virtual function void log_rx_processing(ucie_sb_transaction original, ucie_sb_transaction processed, int y, int x);
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
 * Component construction, FIFO creation, and configuration retrieval.
 *---------------------------------------------------------------------------*/
function void ucie_sb_compare_result_model::build_phase(uvm_phase phase);
  super.build_phase(phase);
  
  // Create analysis port implementations
  tx_analysis_imp = new("tx_analysis_imp", this);
  rx_analysis_imp = new("rx_analysis_imp", this);
  processed_rx_ap = new("processed_rx_ap", this);
  
  // Get model configuration or create default
  if (!uvm_config_db#(ucie_sb_compare_result_config)::get(this, "", "cfg", cfg)) begin
    set_default_config();
  end
  
  // Validate configuration
  if (!cfg.validate_config()) begin
    `uvm_fatal("COMPARE_RESULT_MODEL", "Invalid configuration parameters")
  end
  
  // Create FIFOs with configured sizes
  tx_fifo = new("tx_fifo", this, cfg.tx_fifo_size);
  rx_fifo = new("rx_fifo", this, cfg.rx_fifo_size);
  
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
 * TX TRANSACTION WRITE IMPLEMENTATION
 * 
 * Receives TX transactions from sideband TX monitor and pushes to TX FIFO.
 *---------------------------------------------------------------------------*/
function void ucie_sb_compare_result_model::write_tx(ucie_sb_transaction trans);
  tx_transactions_received++;
  
  if (cfg.enable_debug) begin
    `uvm_info("COMPARE_RESULT_MODEL", $sformatf("Received TX transaction: opcode=%0d, addr=0x%06h, tag=%0d", 
              trans.opcode, trans.addr, trans.tag), UVM_HIGH)
  end
  
  // Push to TX FIFO
  if (!tx_fifo.try_put(trans)) begin
    `uvm_error("COMPARE_RESULT_MODEL", "TX FIFO full - dropping transaction")
  end
endfunction

/*---------------------------------------------------------------------------
 * RX TRANSACTION WRITE IMPLEMENTATION
 * 
 * Receives RX transactions from sideband RX monitor and pushes to RX FIFO.
 *---------------------------------------------------------------------------*/
function void ucie_sb_compare_result_model::write_rx(ucie_sb_transaction trans);
  rx_transactions_received++;
  
  if (cfg.enable_debug) begin
    `uvm_info("COMPARE_RESULT_MODEL", $sformatf("Received RX transaction: opcode=%0d, tag=%0d, data=0x%08h", 
              trans.opcode, trans.tag, trans.data[31:0]), UVM_HIGH)
  end
  
  // Push to RX FIFO
  if (!rx_fifo.try_put(trans)) begin
    `uvm_error("COMPARE_RESULT_MODEL", "RX FIFO full - dropping transaction")
  end
endfunction

/*---------------------------------------------------------------------------
 * MAIN TRANSACTION PROCESSING IMPLEMENTATION
 * 
 * Main processing loop that handles TX and RX FIFO processing according
 * to the compare result model specification.
 *---------------------------------------------------------------------------*/
task ucie_sb_compare_result_model::process_transactions();
  ucie_sb_transaction tx_trans, rx_trans;
  realtime start_time, process_time;
  
  forever begin
    // Get TX transaction from FIFO
    tx_fifo.get(tx_trans);
    start_time = $realtime;
    
    // Process TX transaction to set up array access parameters
    process_tx_transaction(tx_trans);
    
    // Get RX transaction from FIFO
    rx_fifo.get(rx_trans);
    
    // Process RX transaction based on model configuration
    if (!cfg.enable_model) begin
      // Model disabled - drop RX transaction (simulate timeout/failure)
      log_message($sformatf("Model disabled - dropping RX transaction (tag=%0d)", rx_trans.tag), UVM_MEDIUM);
      
    end else if (cfg.pass_through_mode) begin
      // Pass through unchanged
      rx_sequencer.send_request(rx_trans);
      processed_rx_ap.write(rx_trans);
      rx_transactions_passed_through++;
      
      if (cfg.enable_debug) begin
        `uvm_info("COMPARE_RESULT_MODEL", $sformatf("Pass-through mode: forwarded RX unchanged (tag=%0d)", rx_trans.tag), UVM_HIGH)
      end
      
    end else begin
      // Process RX transaction with compare result rewriting
      ucie_sb_transaction processed_trans = process_rx_transaction(rx_trans);
      
      // Send processed transaction to sequencer and analysis port
      rx_sequencer.send_request(processed_trans);
      processed_rx_ap.write(processed_trans);
      
      rx_transactions_processed++;
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
  // Extract TX request parameters for array access setup
  // This assumes TX transaction contains volt_min, volt_max, clk_phase information
  // The exact extraction method depends on how these parameters are encoded in the transaction
  
  // For demonstration, assume parameters are encoded in specific fields:
  int volt_min = tx_trans.addr[15:8];      // Example: volt_min in addr bits [15:8]
  int volt_max = tx_trans.addr[7:0];       // Example: volt_max in addr bits [7:0]
  int clk_phase = tx_trans.tag;            // Example: clk_phase in tag field
  
  // Process TX request to set up array access region
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
  tx_requests_processed++;
  
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
 * Main processing logic for RX transactions. Overwrites data field
 * with array value and recalculates parity.
 *---------------------------------------------------------------------------*/
function ucie_sb_transaction ucie_sb_compare_result_model::process_rx_transaction(ucie_sb_transaction rx_trans);
  ucie_sb_transaction processed_trans;
  bit [31:0] original_data;
  bit [31:0] new_data;
  bit original_parity;
  bit new_parity;
  int access_y, access_x;
  
  // Create copy of original transaction
  processed_trans = rx_trans.copy();
  original_data = rx_trans.data[31:0];
  original_parity = rx_trans.dp;  // Assuming dp is data parity field
  
  // Get next array value
  new_data = get_next_array_value();
  access_y = current_y_pos;
  access_x = current_x_pos;
  
  // Overwrite data field
  processed_trans.data[31:0] = new_data;
  
  // Recalculate parity
  update_parity(processed_trans);
  new_parity = processed_trans.dp;
  
  // Update statistics
  if (new_data == cfg.PASS_VALUE) begin
    pass_results_returned++;
  end else begin
    fail_results_returned++;
  end
  
  array_accesses_total++;
  
  // Log processing details
  if (cfg.enable_logging) begin
    log_rx_processing(rx_trans, processed_trans, access_y, access_x);
  end
  
  if (cfg.enable_debug) begin
    `uvm_info("COMPARE_RESULT_MODEL", $sformatf("RX processed: tag=%0d, array[%0d][%0d]=0x%08h, parity: %0b→%0b", 
              rx_trans.tag, access_y, access_x, new_data, original_parity, new_parity), UVM_MEDIUM)
  end
  
  return processed_trans;
endfunction

/*---------------------------------------------------------------------------
 * ARRAY VALUE RETRIEVAL IMPLEMENTATION
 * 
 * Sequentially retrieves next value from compare result array based on
 * current access region and position.
 *---------------------------------------------------------------------------*/
function bit [31:0] ucie_sb_compare_result_model::get_next_array_value();
  bit [31:0] value;
  
  // Check if array is initialized
  if (!array_initialized) begin
    `uvm_error("COMPARE_RESULT_MODEL", "Array not initialized")
    return cfg.FAIL_VALUE;
  end
  
  // Check bounds
  if (current_y_pos < 0 || current_y_pos >= cfg.ARRAY_ROWS ||
      current_x_pos < 0 || current_x_pos >= cfg.ARRAY_COLS) begin
    `uvm_error("COMPARE_RESULT_MODEL", $sformatf("Array access out of bounds: [%0d][%0d]", 
               current_y_pos, current_x_pos))
    return cfg.FAIL_VALUE;
  end
  
  // Get value from array
  value = compare_result_array[current_y_pos][current_x_pos];
  
  // Advance to next position (row-major order)
  current_x_pos++;
  if (current_x_pos > access_x_max) begin
    current_x_pos = access_x_min;
    current_y_pos++;
    if (current_y_pos > access_y_max) begin
      // Wrap around to beginning of region
      current_y_pos = access_y_min;
    end
  end
  
  return value;
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
function void ucie_sb_compare_result_model::log_tx_request(int volt_min, int volt_max, int clk_phase);
  string msg;
  
  msg = $sformatf("=== TX REQUEST ===");
  log_message(msg, UVM_MEDIUM);
  
  msg = $sformatf("DUT parameters: volt_min=%0d, volt_max=%0d, clk_phase=%0d", volt_min, volt_max, clk_phase);
  log_message(msg, UVM_MEDIUM);
  
  msg = $sformatf("Access region: Y[%0d:%0d], X[%0d:%0d]", access_y_min, access_y_max, access_x_min, access_x_max);
  log_message(msg, UVM_MEDIUM);
  
  int region_size = (access_y_max - access_y_min + 1) * (access_x_max - access_x_min + 1);
  msg = $sformatf("Region size: %0d elements", region_size);
  log_message(msg, UVM_MEDIUM);
  
  msg = $sformatf("==================");
  log_message(msg, UVM_MEDIUM);
endfunction

/*---------------------------------------------------------------------------
 * RX PROCESSING LOGGING IMPLEMENTATION
 * 
 * Logs detailed RX processing information including before/after values.
 *---------------------------------------------------------------------------*/
function void ucie_sb_compare_result_model::log_rx_processing(ucie_sb_transaction original, ucie_sb_transaction processed, int y, int x);
  string msg;
  
  msg = $sformatf("RX_PROCESS: tag=%0d, array[%0d][%0d], data: 0x%08h → 0x%08h, parity: %0b → %0b", 
                  original.tag, y, x, original.data[31:0], processed.data[31:0], original.dp, processed.dp);
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