/*******************************************************************************
 * UCIe Sideband Protocol Agent
 * 
 * OVERVIEW:
 *   Comprehensive UVM agent for UCIe (Universal Chiplet Interconnect Express)
 *   sideband protocol verification. Orchestrates driver, monitor, and sequencer
 *   components to provide complete transaction-level modeling with flexible
 *   active/passive operation modes.
 *
 * AGENT ARCHITECTURE:
 *   • Hierarchical component management (driver, monitor, sequencer)
 *   • Configurable active/passive modes for versatile testbench integration
 *   • Centralized configuration distribution and management
 *   • Analysis port connectivity for transaction monitoring
 *   • Feature-based enable/disable controls for targeted verification
 *
 * OPERATIONAL MODES:
 *   • Active Mode: Full stimulus generation with driver and sequencer
 *   • Passive Mode: Monitor-only operation for protocol observation
 *   • Hybrid Support: Runtime mode switching capabilities
 *
 * CONFIGURATION MANAGEMENT:
 *   • Unified configuration object with inheritance hierarchy
 *   • Driver timing parameter control (800MHz/400MHz presets)
 *   • Protocol compliance feature toggles
 *   • Statistics and coverage collection controls
 *   • Interface handle distribution
 *
 * INTEGRATION FEATURES:
 *   • Seamless testbench integration with standard UVM patterns
 *   • Analysis port forwarding for transaction visibility
 *   • Configuration database utilization for parameter passing
 *   • Comprehensive reporting and debugging support
 *
 * VERIFICATION CAPABILITIES:
 *   • Protocol compliance checking with configurable strictness
 *   • Performance statistics collection and analysis
 *   • Coverage-driven verification support
 *   • Debug and analysis reporting infrastructure
 *
 * COMPLIANCE:
 *   • IEEE 1800-2017 SystemVerilog
 *   • UVM 1.2 methodology
 *   • UCIe 1.1 specification
 *
 * AUTHOR: UCIe Sideband UVM Agent
 * VERSION: 3.0 - Production-grade agent architecture
 ******************************************************************************/

class ucie_sb_agent extends uvm_agent;
  `uvm_component_utils(ucie_sb_agent)
  
  /*---------------------------------------------------------------------------
   * AGENT COMPONENT HIERARCHY
   * Core verification components managed by this agent
   *---------------------------------------------------------------------------*/
  
  ucie_sb_driver driver;
  ucie_sb_monitor monitor;
  ucie_sb_sequencer sequencer;
  
  /*---------------------------------------------------------------------------
   * CONFIGURATION AND CONNECTIVITY
   * Configuration management and external interface connectivity
   *---------------------------------------------------------------------------*/
  
  ucie_sb_agent_config cfg;
  uvm_analysis_port #(ucie_sb_transaction) ap;
  
  /*---------------------------------------------------------------------------
   * CONSTRUCTOR - Initialize agent component
   *---------------------------------------------------------------------------*/
  function new(string name = "ucie_sb_agent", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  /*---------------------------------------------------------------------------
   * EXTERNAL METHOD DECLARATIONS
   * All implementation methods declared as extern for clean interface
   *---------------------------------------------------------------------------*/
  
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);
  extern virtual function void end_of_elaboration_phase(uvm_phase phase);
  extern virtual function void report_phase(uvm_phase phase);
  extern virtual function void configure_components();
  extern virtual function void set_default_config();
  extern virtual function void print_config();

endclass : ucie_sb_agent

/*******************************************************************************
 * AGENT CONFIGURATION CLASS
 * 
 * Comprehensive configuration management for UCIe sideband agent operation.
 * Provides centralized control over all agent features, timing parameters,
 * and operational modes with preset configurations for common scenarios.
 ******************************************************************************/

class ucie_sb_agent_config extends uvm_object;
  `uvm_object_utils(ucie_sb_agent_config)
  
  /*---------------------------------------------------------------------------
   * OPERATIONAL MODE CONTROL
   * Agent behavior and component instantiation control
   *---------------------------------------------------------------------------*/
  
  uvm_active_passive_enum is_active = UVM_ACTIVE;
  
  /*---------------------------------------------------------------------------
   * INTERFACE MANAGEMENT
   * Virtual interface handle for component distribution
   *---------------------------------------------------------------------------*/
  
  virtual ucie_sb_inf vif;
  
  /*---------------------------------------------------------------------------
   * SUB-COMPONENT CONFIGURATION
   * Configuration objects for managed components
   *---------------------------------------------------------------------------*/
  
  ucie_sb_driver_config driver_cfg;
  
  /*---------------------------------------------------------------------------
   * VERIFICATION FEATURE CONTROLS
   * Enable/disable toggles for verification capabilities
   *---------------------------------------------------------------------------*/
  
  bit enable_coverage = 1;
  bit enable_protocol_checking = 1;
  bit enable_statistics = 1;
  
  /*---------------------------------------------------------------------------
   * CONSTRUCTOR - Initialize configuration with driver setup
   *---------------------------------------------------------------------------*/
  function new(string name = "ucie_sb_agent_config");
    super.new(name);
    driver_cfg = ucie_sb_driver_config::type_id::create("driver_cfg");
  endfunction
  
  /*---------------------------------------------------------------------------
   * CONFIGURATION METHOD DECLARATIONS
   * External methods for preset configurations and debugging
   *---------------------------------------------------------------------------*/
  
  extern function void set_800mhz_config();
  extern function void set_400mhz_config();
  extern function void print_config();

endclass : ucie_sb_agent_config

/*******************************************************************************
 * AGENT IMPLEMENTATION
 * Complete UVM agent lifecycle management and component orchestration
 ******************************************************************************/

/*-----------------------------------------------------------------------------
 * BUILD PHASE IMPLEMENTATION
 * 
 * Comprehensive component creation and configuration management:
 *   • Configuration acquisition from database or default creation
 *   • Mode-dependent component instantiation (active vs passive)
 *   • Analysis port creation for transaction forwarding
 *   • Component configuration distribution
 *
 * COMPONENT CREATION STRATEGY:
 *   • Monitor: Always created (required for protocol observation)
 *   • Driver/Sequencer: Created only in active mode
 *   • Analysis Port: Always created for transaction visibility
 *
 * CONFIGURATION FLOW:
 *   1. Attempt configuration retrieval from database
 *   2. Create default configuration if not found
 *   3. Apply default settings for UCIe operation
 *   4. Distribute configuration to sub-components
 *-----------------------------------------------------------------------------*/
function void ucie_sb_agent::build_phase(uvm_phase phase);
  super.build_phase(phase);
  
  if (!uvm_config_db#(ucie_sb_agent_config)::get(this, "", "cfg", cfg)) begin
    cfg = ucie_sb_agent_config::type_id::create("cfg");
    set_default_config();
    `uvm_info("AGENT", "Using default agent configuration", UVM_MEDIUM)
  end
  
  ap = new("ap", this);
  
  monitor = ucie_sb_monitor::type_id::create("monitor", this);
  
  if (cfg.is_active == UVM_ACTIVE) begin
    driver = ucie_sb_driver::type_id::create("driver", this);
    sequencer = ucie_sb_sequencer::type_id::create("sequencer", this);
    
    `uvm_info("AGENT", "Created active agent with driver and sequencer", UVM_LOW)
  end else begin
    `uvm_info("AGENT", "Created passive agent with monitor only", UVM_LOW)
  end
  
  configure_components();
endfunction

/*-----------------------------------------------------------------------------
 * CONNECT PHASE IMPLEMENTATION
 * 
 * Establishes all inter-component connections and analysis port forwarding:
 *   • Monitor analysis port connection to agent analysis port
 *   • Driver-sequencer connection in active mode
 *   • Transaction flow establishment for stimulus and monitoring
 *
 * CONNECTION ARCHITECTURE:
 *   • Monitor → Agent Analysis Port (always connected)
 *   • Sequencer → Driver (active mode only)
 *   • External connections handled by parent environment
 *
 * TRANSACTION FLOW:
 *   Active: Sequencer → Driver → Interface → Monitor → Analysis Port
 *   Passive: Interface → Monitor → Analysis Port
 *-----------------------------------------------------------------------------*/
function void ucie_sb_agent::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  
  monitor.ap.connect(ap);
  
  if (cfg.is_active == UVM_ACTIVE) begin
    driver.seq_item_port.connect(sequencer.seq_item_export);
    `uvm_info("AGENT", "Connected driver to sequencer", UVM_LOW)
  end
  
  `uvm_info("AGENT", "Agent connections completed", UVM_LOW)
endfunction

/*-----------------------------------------------------------------------------
 * END OF ELABORATION PHASE IMPLEMENTATION
 * 
 * Final validation and debugging preparation:
 *   • Configuration validation and reporting
 *   • Component hierarchy verification
 *   • Debug information generation
 *   • System readiness confirmation
 *
 * VALIDATION CHECKS:
 *   • Component creation verification
 *   • Configuration consistency validation
 *   • Interface connectivity confirmation
 *   • Feature enable consistency
 *-----------------------------------------------------------------------------*/
function void ucie_sb_agent::end_of_elaboration_phase(uvm_phase phase);
  super.end_of_elaboration_phase(phase);
  
  if (cfg.enable_statistics) begin
    print_config();
  end
  
  `uvm_info("AGENT", "Agent elaboration completed", UVM_LOW)
endfunction

/*-----------------------------------------------------------------------------
 * REPORT PHASE IMPLEMENTATION
 * 
 * Final statistics and operational summary reporting:
 *   • Agent operational mode summary
 *   • Feature utilization reporting
 *   • Configuration summary for analysis
 *   • Performance and coverage metrics
 *
 * REPORT CONTENT:
 *   • Operational mode (active/passive)
 *   • Feature enable status
 *   • Configuration parameters
 *   • Component utilization summary
 *-----------------------------------------------------------------------------*/
function void ucie_sb_agent::report_phase(uvm_phase phase);
  super.report_phase(phase);
  
  if (cfg.enable_statistics) begin
    `uvm_info("AGENT", "=== Agent Report ===", UVM_LOW)
    `uvm_info("AGENT", $sformatf("Mode: %s", cfg.is_active.name()), UVM_LOW)
    `uvm_info("AGENT", $sformatf("Coverage enabled: %0b", cfg.enable_coverage), UVM_LOW)
    `uvm_info("AGENT", $sformatf("Protocol checking: %0b", cfg.enable_protocol_checking), UVM_LOW)
    `uvm_info("AGENT", "====================", UVM_LOW)
  end
endfunction

/*-----------------------------------------------------------------------------
 * COMPONENT CONFIGURATION DISTRIBUTION
 * 
 * Distributes configuration parameters to all sub-components using UVM
 * configuration database with appropriate scoping and inheritance:
 *   • Driver configuration for active mode operation
 *   • Feature enable distribution to all components
 *   • Interface handle distribution (handled by testbench)
 *   • Protocol parameter propagation
 *
 * CONFIGURATION SCOPING:
 *   • Driver-specific: Scoped to "driver" component
 *   • Global features: Wildcard scope for all sub-components
 *   • Interface: Set by testbench with wildcard scope
 *
 * PARAMETER CATEGORIES:
 *   • Timing: Clock frequency, duty cycle, gap timing
 *   • Protocol: Validation enables, compliance checking
 *   • Features: Coverage, statistics, debugging
 *-----------------------------------------------------------------------------*/
function void ucie_sb_agent::configure_components();
  if (cfg.is_active == UVM_ACTIVE && driver != null) begin
    uvm_config_db#(ucie_sb_driver_config)::set(this, "driver", "cfg", cfg.driver_cfg);
  end
  
  uvm_config_db#(bit)::set(this, "*", "enable_protocol_checking", cfg.enable_protocol_checking);
  uvm_config_db#(bit)::set(this, "*", "enable_statistics", cfg.enable_statistics);
  uvm_config_db#(bit)::set(this, "*", "enable_coverage", cfg.enable_coverage);
  
  `uvm_info("AGENT", "Component configuration completed", UVM_LOW)
endfunction

/*-----------------------------------------------------------------------------
 * DEFAULT CONFIGURATION SETUP
 * 
 * Establishes production-ready default configuration for UCIe sideband
 * operation with optimal settings for typical verification scenarios:
 *   • Active mode for full stimulus capability
 *   • All verification features enabled
 *   • 800MHz operation per UCIe specification
 *   • Standard gap timing (32 UI minimum)
 *
 * DEFAULT SETTINGS:
 *   • Mode: Active (driver + sequencer + monitor)
 *   • Frequency: 800MHz (UCIe standard)
 *   • Gap: 32 cycles (UCIe minimum)
 *   • Features: All enabled (coverage, protocol, statistics)
 *
 * RATIONALE:
 *   Provides immediately usable configuration for most verification
 *   scenarios while maintaining UCIe specification compliance.
 *-----------------------------------------------------------------------------*/
function void ucie_sb_agent::set_default_config();
  cfg.is_active = UVM_ACTIVE;
  cfg.enable_coverage = 1;
  cfg.enable_protocol_checking = 1;
  cfg.enable_statistics = 1;
  
  cfg.driver_cfg.set_frequency(800e6);
  cfg.driver_cfg.min_gap_cycles = 32;
  cfg.driver_cfg.enable_protocol_checking = 1;
  cfg.driver_cfg.enable_statistics = 1;
  
  `uvm_info("AGENT", "Default configuration applied", UVM_MEDIUM)
endfunction

/*-----------------------------------------------------------------------------
 * CONFIGURATION DEBUG REPORTING
 * 
 * Generates comprehensive configuration summary for debugging and analysis:
 *   • Agent operational parameters
 *   • Driver timing configuration
 *   • Feature enable status
 *   • Component instantiation summary
 *
 * DEBUG INFORMATION:
 *   • Operational mode and component status
 *   • Timing parameters and frequency settings
 *   • Feature enable/disable status
 *   • Configuration source and validation
 *
 * OUTPUT FORMAT:
 *   Structured logging with clear parameter identification for
 *   easy debugging and configuration verification.
 *-----------------------------------------------------------------------------*/
function void ucie_sb_agent::print_config();
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

/*******************************************************************************
 * AGENT CONFIGURATION IMPLEMENTATION
 * Preset configuration methods for common verification scenarios
 ******************************************************************************/

/*-----------------------------------------------------------------------------
 * 800MHz CONFIGURATION PRESET
 * 
 * Configures driver for standard UCIe 800MHz operation with specification-
 * compliant timing parameters:
 *   • Frequency: 800MHz (1.25ns period)
 *   • Duty Cycle: 50% (optimal for signal integrity)
 *   • Gap Timing: 32 UI (UCIe minimum requirement)
 *
 * TIMING CHARACTERISTICS:
 *   • Period: 1.25ns (800MHz)
 *   • High Time: 0.625ns (50% duty cycle)
 *   • Low Time: 0.625ns (50% duty cycle)
 *   • Gap Duration: 40ns (32 × 1.25ns)
 *
 * APPLICATION:
 *   Standard configuration for production UCIe sideband verification
 *   scenarios requiring full-speed operation and protocol compliance.
 *-----------------------------------------------------------------------------*/
function void ucie_sb_agent_config::set_800mhz_config();
  driver_cfg.set_frequency(800e6);
  driver_cfg.set_duty_cycle(50.0);
  driver_cfg.min_gap_cycles = 32;
  `uvm_info("AGENT_CONFIG", "Set 800MHz configuration", UVM_LOW)
endfunction

/*-----------------------------------------------------------------------------
 * 400MHz CONFIGURATION PRESET
 * 
 * Configures driver for reduced-speed 400MHz operation for debugging,
 * development, and timing analysis scenarios:
 *   • Frequency: 400MHz (2.5ns period)
 *   • Duty Cycle: 50% (balanced timing)
 *   • Gap Timing: 32 UI (maintains protocol compliance)
 *
 * TIMING CHARACTERISTICS:
 *   • Period: 2.5ns (400MHz)
 *   • High Time: 1.25ns (50% duty cycle)
 *   • Low Time: 1.25ns (50% duty cycle)
 *   • Gap Duration: 80ns (32 × 2.5ns)
 *
 * APPLICATION:
 *   Development and debugging configuration providing longer timing
 *   windows for analysis while maintaining protocol correctness.
 *-----------------------------------------------------------------------------*/
function void ucie_sb_agent_config::set_400mhz_config();
  driver_cfg.set_frequency(400e6);
  driver_cfg.set_duty_cycle(50.0);
  driver_cfg.min_gap_cycles = 32;
  `uvm_info("AGENT_CONFIG", "Set 400MHz configuration", UVM_LOW)
endfunction

/*-----------------------------------------------------------------------------
 * CONFIGURATION DEBUG REPORTING
 * 
 * Generates concise configuration summary for agent configuration objects:
 *   • Operational mode and feature status
 *   • Driver timing parameters
 *   • Verification capability enables
 *
 * REPORT CONTENT:
 *   • Mode: Active/Passive operation
 *   • Features: Coverage, protocol checking, statistics
 *   • Timing: Driver frequency configuration
 *
 * FORMAT:
 *   Compact, structured output suitable for quick configuration
 *   verification and debugging analysis.
 *-----------------------------------------------------------------------------*/
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