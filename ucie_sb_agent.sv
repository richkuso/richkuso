// UCIe Sideband Agent Class - Refactored with extern methods
// Container for sideband driver, monitor, and sequencer

//=============================================================================
// CLASS: ucie_sb_agent
//
// DESCRIPTION:
//   UCIe sideband agent that serves as a container for driver, monitor, and
//   sequencer components. Supports both active and passive modes with
//   comprehensive configuration management and component orchestration.
//
// FEATURES:
//   - Active/passive mode support
//   - Automatic component creation and connection
//   - Centralized configuration management
//   - Statistics collection and reporting
//   - Interface distribution to sub-components
//   - Feature enable/disable controls
//
// AUTHOR: UCIe Sideband UVM Agent
// VERSION: 1.0
//=============================================================================

class ucie_sb_agent extends uvm_agent;
  `uvm_component_utils(ucie_sb_agent)
  
  //=============================================================================
  // CLASS FIELDS
  //=============================================================================
  
  // Agent components
  ucie_sb_driver driver;
  ucie_sb_monitor monitor;
  ucie_sb_sequencer sequencer;
  
  // Configuration
  ucie_sb_agent_config cfg;
  
  // Analysis port for monitor transactions
  uvm_analysis_port #(ucie_sb_transaction) ap;
  
  //=============================================================================
  // CONSTRUCTOR
  //=============================================================================

  //-----------------------------------------------------------------------------
  // FUNCTION: new
  // Creates a new sideband agent component
  //
  // PARAMETERS:
  //   name   - Component name for UVM hierarchy
  //   parent - Parent component reference
  //-----------------------------------------------------------------------------
  function new(string name = "ucie_sb_agent", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  //=============================================================================
  // EXTERN FUNCTION/TASK DECLARATIONS
  //=============================================================================
  
  //-----------------------------------------------------------------------------
  // FUNCTION: build_phase
  // UVM build phase - creates components and configures them
  //
  // PARAMETERS:
  //   phase - UVM phase object
  //-----------------------------------------------------------------------------
  extern virtual function void build_phase(uvm_phase phase);
  
  //-----------------------------------------------------------------------------
  // FUNCTION: connect_phase
  // UVM connect phase - connects components together
  //
  // PARAMETERS:
  //   phase - UVM phase object
  //-----------------------------------------------------------------------------
  extern virtual function void connect_phase(uvm_phase phase);
  
  //-----------------------------------------------------------------------------
  // FUNCTION: end_of_elaboration_phase
  // UVM end of elaboration phase - final setup and validation
  //
  // PARAMETERS:
  //   phase - UVM phase object
  //-----------------------------------------------------------------------------
  extern virtual function void end_of_elaboration_phase(uvm_phase phase);
  
  //-----------------------------------------------------------------------------
  // FUNCTION: report_phase
  // UVM report phase - prints agent statistics and configuration
  //
  // PARAMETERS:
  //   phase - UVM phase object
  //-----------------------------------------------------------------------------
  extern virtual function void report_phase(uvm_phase phase);
  
  //-----------------------------------------------------------------------------
  // FUNCTION: configure_components
  // Distributes configuration to all sub-components
  //-----------------------------------------------------------------------------
  extern virtual function void configure_components();
  
  //-----------------------------------------------------------------------------
  // FUNCTION: set_default_config
  // Sets default configuration values for the agent
  //-----------------------------------------------------------------------------
  extern virtual function void set_default_config();
  
  //-----------------------------------------------------------------------------
  // FUNCTION: print_config
  // Prints current agent configuration for debugging
  //-----------------------------------------------------------------------------
  extern virtual function void print_config();

endclass : ucie_sb_agent

//=============================================================================
// AGENT CONFIGURATION CLASS
//=============================================================================

//=============================================================================
// CLASS: ucie_sb_agent_config
//
// DESCRIPTION:
//   Configuration class for the UCIe sideband agent containing all settings
//   for agent operation, component enables, and driver configuration.
//   Provides helper functions for common configuration scenarios.
//
// FEATURES:
//   - Active/passive mode control
//   - Driver configuration management
//   - Feature enable/disable controls
//   - Pre-defined frequency configurations
//   - Interface handle management
//
// AUTHOR: UCIe Sideband UVM Agent
// VERSION: 1.0
//=============================================================================

class ucie_sb_agent_config extends uvm_object;
  `uvm_object_utils(ucie_sb_agent_config)
  
  //=============================================================================
  // CONFIGURATION FIELDS
  //=============================================================================
  
  // Agent mode
  uvm_active_passive_enum is_active = UVM_ACTIVE;
  
  // Interface handle
  virtual ucie_sb_inf vif;
  
  // Driver configuration
  ucie_sb_driver_config driver_cfg;
  
  // Feature enables
  bit enable_coverage = 1;
  bit enable_protocol_checking = 1;
  bit enable_statistics = 1;
  
  //=============================================================================
  // CONSTRUCTOR
  //=============================================================================
  
  //-----------------------------------------------------------------------------
  // FUNCTION: new
  // Creates a new agent configuration object with default driver config
  //
  // PARAMETERS:
  //   name - Object name for UVM hierarchy
  //-----------------------------------------------------------------------------
  function new(string name = "ucie_sb_agent_config");
    super.new(name);
    // Create default driver configuration
    driver_cfg = ucie_sb_driver_config::type_id::create("driver_cfg");
  endfunction
  
  //=============================================================================
  // EXTERN FUNCTION DECLARATIONS
  //=============================================================================
  
  //-----------------------------------------------------------------------------
  // FUNCTION: set_800mhz_config
  // Configures driver for 800MHz operation with UCIe defaults
  //-----------------------------------------------------------------------------
  extern function void set_800mhz_config();
  
  //-----------------------------------------------------------------------------
  // FUNCTION: set_400mhz_config
  // Configures driver for 400MHz operation (for testing/debug)
  //-----------------------------------------------------------------------------
  extern function void set_400mhz_config();
  
  //-----------------------------------------------------------------------------
  // FUNCTION: print_config
  // Prints current configuration settings for debugging
  //-----------------------------------------------------------------------------
  extern function void print_config();

endclass : ucie_sb_agent_config

//=============================================================================
// AGENT IMPLEMENTATION
//=============================================================================

//-----------------------------------------------------------------------------
// FUNCTION: build_phase
// UVM build phase - creates components and configures them
//-----------------------------------------------------------------------------
virtual function void ucie_sb_agent::build_phase(uvm_phase phase);
  super.build_phase(phase);
  
  // Get or create agent configuration
  if (!uvm_config_db#(ucie_sb_agent_config)::get(this, "", "cfg", cfg)) begin
    cfg = ucie_sb_agent_config::type_id::create("cfg");
    set_default_config();
    `uvm_info("AGENT", "Using default agent configuration", UVM_MEDIUM)
  end
  
  // Create analysis port
  ap = new("ap", this);
  
  // Always create monitor
  monitor = ucie_sb_monitor::type_id::create("monitor", this);
  
  // Create driver and sequencer only in active mode
  if (cfg.is_active == UVM_ACTIVE) begin
    driver = ucie_sb_driver::type_id::create("driver", this);
    sequencer = ucie_sb_sequencer::type_id::create("sequencer", this);
    
    `uvm_info("AGENT", "Created active agent with driver and sequencer", UVM_LOW)
  end else begin
    `uvm_info("AGENT", "Created passive agent with monitor only", UVM_LOW)
  end
  
  // Configure components
  configure_components();
endfunction

//-----------------------------------------------------------------------------
// FUNCTION: connect_phase
// UVM connect phase - connects components together
//-----------------------------------------------------------------------------
virtual function void ucie_sb_agent::connect_phase(uvm_phase phase);
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

//-----------------------------------------------------------------------------
// FUNCTION: end_of_elaboration_phase
// UVM end of elaboration phase - final setup and validation
//-----------------------------------------------------------------------------
virtual function void ucie_sb_agent::end_of_elaboration_phase(uvm_phase phase);
  super.end_of_elaboration_phase(phase);
  
  // Print configuration for debugging
  if (cfg.enable_statistics) begin
    print_config();
  end
  
  `uvm_info("AGENT", "Agent elaboration completed", UVM_LOW)
endfunction

//-----------------------------------------------------------------------------
// FUNCTION: report_phase
// UVM report phase - prints agent statistics and configuration
//-----------------------------------------------------------------------------
virtual function void ucie_sb_agent::report_phase(uvm_phase phase);
  super.report_phase(phase);
  
  if (cfg.enable_statistics) begin
    `uvm_info("AGENT", "=== Agent Report ===", UVM_LOW)
    `uvm_info("AGENT", $sformatf("Mode: %s", cfg.is_active.name()), UVM_LOW)
    `uvm_info("AGENT", $sformatf("Coverage enabled: %0b", cfg.enable_coverage), UVM_LOW)
    `uvm_info("AGENT", $sformatf("Protocol checking: %0b", cfg.enable_protocol_checking), UVM_LOW)
    `uvm_info("AGENT", "====================", UVM_LOW)
  end
endfunction

//-----------------------------------------------------------------------------
// FUNCTION: configure_components
// Distributes configuration to all sub-components
//-----------------------------------------------------------------------------
virtual function void ucie_sb_agent::configure_components();
  // Virtual interface is set directly by testbench to all components via wildcard
  // No interface handling needed at agent level
  
  // Configure driver if in active mode
  if (cfg.is_active == UVM_ACTIVE && driver != null) begin
    uvm_config_db#(ucie_sb_driver_config)::set(this, "driver", "cfg", cfg.driver_cfg);
  end
  
  // Set feature enables for sub-components
  uvm_config_db#(bit)::set(this, "*", "enable_protocol_checking", cfg.enable_protocol_checking);
  uvm_config_db#(bit)::set(this, "*", "enable_statistics", cfg.enable_statistics);
  uvm_config_db#(bit)::set(this, "*", "enable_coverage", cfg.enable_coverage);
  
  `uvm_info("AGENT", "Component configuration completed", UVM_LOW)
endfunction

//-----------------------------------------------------------------------------
// FUNCTION: set_default_config
// Sets default configuration values for the agent
//-----------------------------------------------------------------------------
virtual function void ucie_sb_agent::set_default_config();
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

//-----------------------------------------------------------------------------
// FUNCTION: print_config
// Prints current agent configuration for debugging
//-----------------------------------------------------------------------------
virtual function void ucie_sb_agent::print_config();
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

//-----------------------------------------------------------------------------
// FUNCTION: set_800mhz_config
// Configures driver for 800MHz operation with UCIe defaults
//-----------------------------------------------------------------------------
function void ucie_sb_agent_config::set_800mhz_config();
  driver_cfg.set_frequency(800e6);
  driver_cfg.set_duty_cycle(50.0);
  driver_cfg.min_gap_cycles = 32;
  `uvm_info("AGENT_CONFIG", "Set 800MHz configuration", UVM_LOW)
endfunction

//-----------------------------------------------------------------------------
// FUNCTION: set_400mhz_config
// Configures driver for 400MHz operation (for testing/debug)
//-----------------------------------------------------------------------------
function void ucie_sb_agent_config::set_400mhz_config();
  driver_cfg.set_frequency(400e6);
  driver_cfg.set_duty_cycle(50.0);
  driver_cfg.min_gap_cycles = 32;
  `uvm_info("AGENT_CONFIG", "Set 400MHz configuration", UVM_LOW)
endfunction

//-----------------------------------------------------------------------------
// FUNCTION: print_config
// Prints current configuration settings for debugging
//-----------------------------------------------------------------------------
function void ucie_sb_agent_config::print_config();
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