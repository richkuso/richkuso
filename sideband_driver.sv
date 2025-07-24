// UCIe Sideband Driver Class
// Converts UVM transactions to serial bit stream on TX path

//------------------------------------------
// Driver Configuration Class
//------------------------------------------

class sideband_driver_config extends uvm_object;
  `uvm_object_utils(sideband_driver_config)
  
  //------------------------------------------
  // Configuration Parameters
  //------------------------------------------
  
  // Clock timing parameters
  real clock_period = 1.25;       // ns (800MHz default)
  real clock_high_time = 0.625;   // ns (50% duty cycle)
  real clock_low_time = 0.625;    // ns (50% duty cycle)
  
  // Protocol parameters
  int min_gap_cycles = 32;        // Minimum gap between packets
  bit enable_protocol_checking = 1;
  bit enable_statistics = 1;
  
  // Timing parameters
  real setup_time = 0.1;          // ns - data setup time before clock edge
  real hold_time = 0.1;           // ns - data hold time after clock edge
  real gap_time = 0.0;            // ns - additional time during gaps
  
  //------------------------------------------
  // Extern Function Declarations
  //------------------------------------------
  
  extern function new(string name = "sideband_driver_config");
  extern function void set_frequency(real freq_hz);
  extern function void set_duty_cycle(real duty_percent);

endclass

//------------------------------------------
// Main Driver Class
//------------------------------------------

class sideband_driver extends uvm_driver #(sideband_transaction);
  `uvm_component_utils(sideband_driver)
  
  //------------------------------------------
  // Class Members
  //------------------------------------------
  
  // Configuration and interface
  virtual sideband_interface vif;
  sideband_driver_config cfg;
  
  // Parameters based on UCIe specification
  parameter int MIN_GAP_CYCLES = 32;
  parameter int PACKET_SIZE_BITS = 64;
  
  // Statistics
  int packets_driven = 0;
  int bits_driven = 0;
  int errors_detected = 0;
  time last_packet_time;
  
  //------------------------------------------
  // Constructor
  //------------------------------------------
  
  extern function new(string name = "sideband_driver", uvm_component parent = null);
  
  //------------------------------------------
  // Extern Function/Task Declarations
  //------------------------------------------
  
  // UVM Phases (remove virtual keyword from extern declarations)
  extern function void build_phase(uvm_phase phase);
  extern task run_phase(uvm_phase phase);
  extern function void report_phase(uvm_phase phase);
  extern function void final_phase(uvm_phase phase);
  
  // Core Driver Tasks (remove virtual keyword from extern declarations)
  extern task drive_transaction(sideband_transaction trans);
  extern function bit drive_packet_with_clock(bit [63:0] packet);
  extern task drive_gap(int num_cycles = MIN_GAP_CYCLES);
  
  // Reset and Initialization
  extern task wait_for_reset_release();
  
  // Validation and Protocol Checking
  extern function bit validate_transaction(sideband_transaction trans);
  
  // Statistics and Utility
  extern task update_statistics();
  extern function void get_statistics(output int pkts, output int bits, output int errs, output time last_time);
  extern function bit get_tx_clk_state();
  extern function bit get_tx_data_state();
  extern task drive_debug_pattern(bit [63:0] pattern, string pattern_name = "DEBUG");

endclass
    sideband_transaction trans;
// Implementation Section
//------------------------------------------

// Configuration class implementations
function sideband_driver_config::new(string name = "sideband_driver_config");
  super.new(name);
endfunction

// Helper function to set frequency
function void sideband_driver_config::set_frequency(real freq_hz);
  clock_period = (1.0 / freq_hz) * 1e9; // Convert to ns
  clock_high_time = clock_period / 2.0;
  clock_low_time = clock_period / 2.0;
  `uvm_info("CONFIG", $sformatf("Set frequency to %.1f MHz (period=%.3f ns)", freq_hz/1e6, clock_period), UVM_LOW)
endfunction

// Helper function to set duty cycle
function void sideband_driver_config::set_duty_cycle(real duty_percent);
  clock_high_time = clock_period * (duty_percent / 100.0);
  clock_low_time = clock_period - clock_high_time;
endfunction

// Driver class constructor
function sideband_driver::new(string name = "sideband_driver", uvm_component parent = null);
  super.new(name, parent);
endfunction