// UCIe Sideband Agent Class - Refactored with extern methods
// Container for sideband driver, monitor, and sequencer

class sideband_agent extends uvm_agent;
  `uvm_component_utils(sideband_agent)
  
  //=============================================================================
  // CLASS FIELDS
  //=============================================================================
  
  // Agent components
  sideband_driver driver;
  sideband_monitor monitor;
  sideband_sequencer sequencer;
  
  // Configuration
  sideband_agent_config cfg;
  
  // Analysis port for monitor transactions
  uvm_analysis_port #(sideband_transaction) ap;
  
  //=============================================================================
  // CONSTRUCTOR
  //=============================================================================

  function new(string name = "sideband_agent", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  //=============================================================================
  // EXTERN FUNCTION/TASK DECLARATIONS
  //=============================================================================
  
  // UVM phase methods
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);
  extern virtual function void end_of_elaboration_phase(uvm_phase phase);
  extern virtual function void report_phase(uvm_phase phase);
  
  // Configuration methods
  extern virtual function void configure_components();
  extern virtual function void set_default_config();
  
  // Utility methods
  extern virtual function void print_config();

endclass : sideband_agent

//=============================================================================
// AGENT CONFIGURATION CLASS
//=============================================================================

class sideband_agent_config extends uvm_object;
  `uvm_object_utils(sideband_agent_config)
  
  //=============================================================================
  // CONFIGURATION FIELDS
  //=============================================================================
  
  // Agent mode
  uvm_active_passive_enum is_active = UVM_ACTIVE;
  
  // Interface handle
  virtual sideband_interface vif;
  
  // Driver configuration
  sideband_driver_config driver_cfg;
  
  // Feature enables
  bit enable_coverage = 1;
  bit enable_protocol_checking = 1;
  bit enable_statistics = 1;
  
  //=============================================================================
  // CONSTRUCTOR
  //=============================================================================
  
  function new(string name = "sideband_agent_config");
    super.new(name);
    // Create default driver configuration
    driver_cfg = sideband_driver_config::type_id::create("driver_cfg");
  endfunction
  
  //=============================================================================
  // EXTERN FUNCTION DECLARATIONS
  //=============================================================================
  
  extern function void set_800mhz_config();
  extern function void set_400mhz_config();
  extern function void print_config();

endclass : sideband_agent_config

//=============================================================================
// AGENT IMPLEMENTATION
//=============================================================================

// UVM phase methods
virtual function void sideband_agent::build_phase(uvm_phase phase);
  super.build_phase(phase);
  
  // Get or create agent configuration
  if (!uvm_config_db#(sideband_agent_config)::get(this, "", "cfg", cfg)) begin
    cfg = sideband_agent_config::type_id::create("cfg");
    set_default_config();
    `uvm_info("AGENT", "Using default agent configuration", UVM_MEDIUM)
  end
  
  // Create analysis port
  ap = new("ap", this);
  
  // Always create monitor
  monitor = sideband_monitor::type_id::create("monitor", this);
  
  // Create driver and sequencer only in active mode
  if (cfg.is_active == UVM_ACTIVE) begin
    driver = sideband_driver::type_id::create("driver", this);
    sequencer = sideband_sequencer::type_id::create("sequencer", this);
    
    `uvm_info("AGENT", "Created active agent with driver and sequencer", UVM_LOW)
  end else begin
    `uvm_info("AGENT", "Created passive agent with monitor only", UVM_LOW)
  end
  
  // Configure components
  configure_components();
endfunction

virtual function void sideband_agent::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  
  // Connect monitor analysis port to agent analysis port
  monitor.ap.connect(ap);
  
  // Connect driver to sequencer in active mode
  if (cfg.is_active == UVM_ACTIVE) begin
    driver.seq_item_port.connect(sequencer.seq_item_export);
    `uvm_info("AGENT", "Connected driver to sequencer", UVM_LOW)
  end
  
  `uvm_info("AGENT", "Agent connections completed", UVM_LOW)
endfunction

virtual function void sideband_agent::end_of_elaboration_phase(uvm_phase phase);
  super.end_of_elaboration_phase(phase);
  
  // Print configuration for debugging
  if (cfg.enable_statistics) begin
    print_config();
  end
  
  `uvm_info("AGENT", "Agent elaboration completed", UVM_LOW)
endfunction

virtual function void sideband_agent::report_phase(uvm_phase phase);
  super.report_phase(phase);
  
  if (cfg.enable_statistics) begin
    `uvm_info("AGENT", "=== Agent Report ===", UVM_LOW)
    `uvm_info("AGENT", $sformatf("Mode: %s", cfg.is_active.name()), UVM_LOW)
    `uvm_info("AGENT", $sformatf("Coverage enabled: %0b", cfg.enable_coverage), UVM_LOW)
    `uvm_info("AGENT", $sformatf("Protocol checking: %0b", cfg.enable_protocol_checking), UVM_LOW)
    `uvm_info("AGENT", "====================", UVM_LOW)
  end
endfunction

// Configuration methods
virtual function void sideband_agent::configure_components();
  // Set virtual interface for all components
  if (cfg.vif != null) begin
    uvm_config_db#(virtual sideband_interface)::set(this, "*", "vif", cfg.vif);
  end else begin
    `uvm_fatal("AGENT", "Virtual interface not provided in agent configuration")
  end
  
  // Configure driver if in active mode
  if (cfg.is_active == UVM_ACTIVE && driver != null) begin
    uvm_config_db#(sideband_driver_config)::set(this, "driver", "cfg", cfg.driver_cfg);
  end
  
  // Set feature enables
  uvm_config_db#(bit)::set(this, "*", "enable_protocol_checking", cfg.enable_protocol_checking);
  uvm_config_db#(bit)::set(this, "*", "enable_statistics", cfg.enable_statistics);
  uvm_config_db#(bit)::set(this, "*", "enable_coverage", cfg.enable_coverage);
  
  `uvm_info("AGENT", "Component configuration completed", UVM_LOW)
endfunction

virtual function void sideband_agent::set_default_config();
  cfg.is_active = UVM_ACTIVE;
  cfg.enable_coverage = 1;
  cfg.enable_protocol_checking = 1;
  cfg.enable_statistics = 1;
  
  // Set default 800MHz configuration
  cfg.driver_cfg.set_frequency(800e6);
  cfg.driver_cfg.min_gap_cycles = 32;
  cfg.driver_cfg.enable_protocol_checking = 1;
  cfg.driver_cfg.enable_statistics = 1;
  
  `uvm_info("AGENT", "Default configuration applied", UVM_MEDIUM)
endfunction

// Utility methods
virtual function void sideband_agent::print_config();
  `uvm_info("AGENT", "=== Agent Configuration ===", UVM_LOW)
  `uvm_info("AGENT", $sformatf("Mode: %s", cfg.is_active.name()), UVM_LOW)
  `uvm_info("AGENT", $sformatf("Coverage enabled: %0b", cfg.enable_coverage), UVM_LOW)
  `uvm_info("AGENT", $sformatf("Protocol checking: %0b", cfg.enable_protocol_checking), UVM_LOW)
  `uvm_info("AGENT", $sformatf("Statistics enabled: %0b", cfg.enable_statistics), UVM_LOW)
  
  if (cfg.driver_cfg != null) begin
    `uvm_info("AGENT", $sformatf("Driver frequency: %.1f MHz", 1000.0/cfg.driver_cfg.clock_period), UVM_LOW)
    `uvm_info("AGENT", $sformatf("Driver gap cycles: %0d", cfg.driver_cfg.min_gap_cycles), UVM_LOW)
  end
  
  `uvm_info("AGENT", "==============================", UVM_LOW)
endfunction

//=============================================================================
// AGENT CONFIGURATION IMPLEMENTATION
//=============================================================================

function void sideband_agent_config::set_800mhz_config();
  driver_cfg.set_frequency(800e6);
  driver_cfg.set_duty_cycle(50.0);
  driver_cfg.min_gap_cycles = 32;
  `uvm_info("AGENT_CONFIG", "Set 800MHz configuration", UVM_LOW)
endfunction

function void sideband_agent_config::set_400mhz_config();
  driver_cfg.set_frequency(400e6);
  driver_cfg.set_duty_cycle(50.0);
  driver_cfg.min_gap_cycles = 32;
  `uvm_info("AGENT_CONFIG", "Set 400MHz configuration", UVM_LOW)
endfunction

function void sideband_agent_config::print_config();
  `uvm_info("AGENT_CONFIG", "=== Agent Config ===", UVM_LOW)
  `uvm_info("AGENT_CONFIG", $sformatf("Mode: %s", is_active.name()), UVM_LOW)
  `uvm_info("AGENT_CONFIG", $sformatf("Coverage: %0b", enable_coverage), UVM_LOW)
  `uvm_info("AGENT_CONFIG", $sformatf("Protocol check: %0b", enable_protocol_checking), UVM_LOW)
  `uvm_info("AGENT_CONFIG", $sformatf("Statistics: %0b", enable_statistics), UVM_LOW)
  if (driver_cfg != null) begin
    `uvm_info("AGENT_CONFIG", $sformatf("Driver freq: %.1f MHz", 1000.0/driver_cfg.clock_period), UVM_LOW)
  end
  `uvm_info("AGENT_CONFIG", "====================", UVM_LOW)
endfunction