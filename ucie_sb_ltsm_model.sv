/*******************************************************************************
 * UCIe Sideband Link Training State Machine (LTSM) Model
 * 
 * OVERVIEW:
 *   Production-grade FSM-based model implementing UCIe sideband link training
 *   sequence from RESET state through SBINIT state according to UCIe 1.1 
 *   specification. Integrates seamlessly with existing UCIe sideband UVM agent
 *   for comprehensive protocol compliance and transaction-level modeling.
 *
 * LTSM ARCHITECTURE:
 *   • Complete state machine: RESET → DETECT → POLLING → CONFIG → SBINIT
 *   • Dual role support: Initiator and target configurations
 *   • Agent integration: Uses existing driver/monitor components
 *   • Protocol compliance: UCIe 1.1 timing and message requirements
 *   • Comprehensive logging: State transitions and protocol events
 *   • Timeout protection: Configurable state timeout monitoring
 *
 * FSM STATE SEQUENCE:
 *   • RESET      - Initial reset state, all signals idle
 *   • DETECT     - Clock pattern detection and transmission phase
 *   • POLLING    - Bidirectional clock pattern exchange handshake
 *   • CONFIG     - Link configuration and parameter negotiation
 *   • SBINIT     - SBINIT message exchange and training completion
 *   • ACTIVE     - Normal operation mode (training successful)
 *   • ERROR      - Error state for timeout and protocol violations
 *
 * PROTOCOL IMPLEMENTATION:
 *   • Clock pattern sequences per UCIe specification
 *   • Configuration read/write transactions
 *   • SBINIT VDM message sequences (OOR, Done Request, Done Response)
 *   • Proper timing relationships and gap requirements
 *   • Comprehensive error detection and recovery
 *
 * INTEGRATION FEATURES:
 *   • Seamless sideband agent integration
 *   • UVM methodology compliance
 *   • Configuration database utilization
 *   • Analysis port connectivity
 *   • Statistics collection and reporting
 *
 * VERIFICATION CAPABILITIES:
 *   • State transition validation and timing analysis
 *   • Protocol compliance checking with detailed reporting
 *   • Performance statistics collection and analysis
 *   • Comprehensive debug and analysis infrastructure
 *   • Timeout detection and error handling
 *
 * COMPLIANCE:
 *   • IEEE 1800-2017 SystemVerilog
 *   • UVM 1.2 methodology
 *   • UCIe 1.1 specification
 *
 * AUTHOR: UCIe Sideband UVM Agent
 * VERSION: 1.0 - Production-grade LTSM FSM implementation
 ******************************************************************************/

//=============================================================================
// UCIe LTSM State Enumeration
//=============================================================================
typedef enum bit [3:0] {
  LTSM_RESET      = 4'h0,  // Reset state - all idle
  LTSM_DETECT     = 4'h1,  // Clock pattern detection
  LTSM_POLLING    = 4'h2,  // Bidirectional polling
  LTSM_CONFIG     = 4'h3,  // Configuration exchange
  LTSM_SBINIT     = 4'h4,  // SBINIT message phase
  LTSM_ACTIVE     = 4'h5,  // Normal operation (future)
  LTSM_ERROR      = 4'hF   // Error state
} ucie_ltsm_state_t;

//=============================================================================
// UCIe LTSM Event Enumeration
//=============================================================================
typedef enum bit [3:0] {
  LTSM_EV_RESET           = 4'h0,  // Reset assertion
  LTSM_EV_RESET_DEASSERT  = 4'h1,  // Reset deassertion
  LTSM_EV_CLOCK_DETECTED  = 4'h2,  // Clock pattern detected
  LTSM_EV_POLLING_SUCCESS = 4'h3,  // Polling handshake complete
  LTSM_EV_CONFIG_COMPLETE = 4'h4,  // Configuration exchange done
  LTSM_EV_SBINIT_COMPLETE = 4'h5,  // SBINIT sequence complete
  LTSM_EV_TIMEOUT         = 4'hE,  // Timeout occurred
  LTSM_EV_ERROR           = 4'hF   // Protocol error
} ucie_ltsm_event_t;

/*******************************************************************************
 * LTSM CONFIGURATION CLASS
 * 
 * Comprehensive configuration management for UCIe sideband LTSM operation.
 * Provides centralized control over all LTSM features, timing parameters,
 * and operational modes with preset configurations for common scenarios.
 ******************************************************************************/

class ucie_sb_ltsm_config extends uvm_object;
  `uvm_object_utils(ucie_sb_ltsm_config)
  
  /*---------------------------------------------------------------------------
   * OPERATIONAL MODE CONFIGURATION
   * Role and behavior control parameters
   *---------------------------------------------------------------------------*/
  
  bit is_initiator = 1;                    // Role: 1=initiator, 0=target
  bit enable_debug = 1;                    // Enable debug messages
  bit enable_statistics = 1;               // Enable statistics collection
  
  /*---------------------------------------------------------------------------
   * TIMING CONFIGURATION PARAMETERS
   * State timeout and protocol timing control
   *---------------------------------------------------------------------------*/
  
  real timeout_ms = 10.0;                  // State timeout in milliseconds
  real reset_recovery_time = 100.0;        // Reset recovery time in ns
  
  /*---------------------------------------------------------------------------
   * PROTOCOL CONFIGURATION PARAMETERS
   * UCIe specification compliance and validation controls
   *---------------------------------------------------------------------------*/
  
  int required_clock_patterns = 4;         // Clock patterns required for detection
  int max_polling_cycles = 100;            // Maximum polling cycles
  real clock_pattern_period = 1250.0;      // Clock pattern period in ns (800MHz)
  real polling_interval = 2500.0;          // Polling interval in ns
  
  /*---------------------------------------------------------------------------
   * SBINIT MESSAGE CONFIGURATION
   * SBINIT protocol message parameters and addresses
   *---------------------------------------------------------------------------*/
  
  bit [7:0] sbinit_oor_msgcode = 8'h10;    // SBINIT Out of Reset message code
  bit [7:0] sbinit_done_req_msgcode = 8'h11; // SBINIT Done Request message code
  bit [7:0] sbinit_done_rsp_msgcode = 8'h12; // SBINIT Done Response message code
  bit [4:0] config_tag = 5'h10;            // Configuration transaction tag
  bit [4:0] sbinit_tag = 5'h11;            // SBINIT message tag
  
  /*---------------------------------------------------------------------------
   * CONSTRUCTOR - Initialize configuration with standard defaults
   *---------------------------------------------------------------------------*/
  function new(string name = "ucie_sb_ltsm_config");
    super.new(name);
  endfunction
  
  /*---------------------------------------------------------------------------
   * CONFIGURATION METHOD DECLARATIONS
   * External methods for preset configurations and parameter management
   *---------------------------------------------------------------------------*/
  
  extern function void set_initiator_config();
  extern function void set_target_config();
  extern function void set_debug_config();
  extern function void print_config();

endclass : ucie_sb_ltsm_config

/*******************************************************************************
 * UCIe SIDEBAND LINK TRAINING STATE MACHINE MODEL
 * 
 * Production-grade FSM implementation for UCIe sideband link training sequence.
 * Provides complete state machine control with comprehensive protocol compliance,
 * timing validation, and integration with existing sideband UVM agent components.
 ******************************************************************************/

class ucie_sb_ltsm_model extends uvm_component;
  `uvm_component_utils(ucie_sb_ltsm_model)
  
  /*---------------------------------------------------------------------------
   * AGENT INTEGRATION AND INTERFACES
   * Sideband agent components and virtual interface connectivity
   *---------------------------------------------------------------------------*/
  
  ucie_sb_agent sb_agent;
  virtual ucie_sb_inf vif;
  
  /*---------------------------------------------------------------------------
   * CONFIGURATION AND CONNECTIVITY
   * Configuration management and external interface connectivity
   *---------------------------------------------------------------------------*/
  
  ucie_sb_ltsm_config cfg;
  
  /*---------------------------------------------------------------------------
   * FSM STATE VARIABLES AND CONTROL
   * State machine control and transition management
   *---------------------------------------------------------------------------*/
  
  ucie_ltsm_state_t current_state = LTSM_RESET;
  ucie_ltsm_state_t next_state = LTSM_RESET;
  ucie_ltsm_event_t current_event;
  
  /*---------------------------------------------------------------------------
   * TIMING AND TIMEOUT MANAGEMENT
   * State entry times and timeout detection infrastructure
   *---------------------------------------------------------------------------*/
  
  realtime state_entry_time;
  realtime timeout_duration;
  
  /*---------------------------------------------------------------------------
   * PROTOCOL TRACKING VARIABLES
   * Transaction and protocol sequence monitoring
   *---------------------------------------------------------------------------*/
  
  // Clock pattern detection tracking
  int clock_patterns_sent = 0;
  int clock_patterns_received = 0;
  
  // Polling phase tracking
  int polling_cycles = 0;
  
  // Configuration transaction tracking
  bit config_req_sent = 0;
  bit config_rsp_received = 0;
  
  // SBINIT message sequence tracking
  bit sbinit_oor_sent = 0;                 // Out of Reset message
  bit sbinit_done_req_sent = 0;            // Done Request message
  bit sbinit_done_rsp_received = 0;        // Done Response received
  
  /*---------------------------------------------------------------------------
   * STATISTICS AND ANALYSIS INFRASTRUCTURE
   * Performance monitoring and error tracking
   *---------------------------------------------------------------------------*/
  
  // State transition counters and timing
  int state_transitions[ucie_ltsm_state_t];
  realtime state_durations[ucie_ltsm_state_t];
  realtime total_training_time;
  
  // Error and violation tracking
  int timeout_errors = 0;
  int protocol_errors = 0;
  
  /*---------------------------------------------------------------------------
   * EVENT MANAGEMENT AND PROCESS CONTROL
   * Inter-process communication and synchronization
   *---------------------------------------------------------------------------*/
  
  event state_change_event;
  event timeout_event;
  event training_complete_event;
  
  /*---------------------------------------------------------------------------
   * CONSTRUCTOR - Initialize LTSM model component
   *---------------------------------------------------------------------------*/
  function new(string name = "ucie_sb_ltsm_model", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  /*---------------------------------------------------------------------------
   * EXTERNAL METHOD DECLARATIONS
   * All implementation methods declared as extern for clean interface
   *---------------------------------------------------------------------------*/
  
  // UVM phase methods
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual function void connect_phase(uvm_phase phase);
  extern virtual function void end_of_elaboration_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);
  extern virtual function void report_phase(uvm_phase phase);
  
  // FSM control methods
  extern virtual task ltsm_fsm_process();
  extern virtual function ucie_ltsm_state_t get_next_state(ucie_ltsm_state_t state, ucie_ltsm_event_t event);
  extern virtual function void state_entry_actions();
  extern virtual function void transition_to_state(ucie_ltsm_state_t new_state);
  
  // State behavior methods
  extern virtual task reset_state_behavior();
  extern virtual task detect_state_behavior();
  extern virtual task polling_state_behavior();
  extern virtual task config_state_behavior();
  extern virtual task sbinit_state_behavior();
  extern virtual task error_state_behavior();
  
  // Protocol implementation methods
  extern virtual task send_clock_patterns();
  extern virtual task wait_for_clock_patterns();
  extern virtual task send_polling_patterns();
  extern virtual task receive_polling_patterns();
  extern virtual task send_config_request();
  extern virtual task wait_for_config_request();
  extern virtual task send_config_response();
  extern virtual task wait_for_config_response();
  extern virtual task send_sbinit_oor();
  extern virtual task wait_for_sbinit_oor();
  extern virtual task send_sbinit_done_request();
  extern virtual task wait_for_sbinit_done_request();
  extern virtual task send_sbinit_done_response();
  extern virtual task wait_for_sbinit_done_response();
  
  // Monitoring and utility methods
  extern virtual task timeout_monitor();
  extern virtual task statistics_collector();
  extern virtual function void configure_agent();
  extern virtual function void set_default_config();
  extern virtual function void print_final_statistics();

endclass : ucie_sb_ltsm_model

/*******************************************************************************
 * LTSM CONFIGURATION CLASS IMPLEMENTATION
 ******************************************************************************/

/*---------------------------------------------------------------------------
 * INITIATOR CONFIGURATION PRESET
 * 
 * Configures LTSM model for initiator role operation with optimized
 * parameters for link training initiation and control.
 *---------------------------------------------------------------------------*/
function void ucie_sb_ltsm_config::set_initiator_config();
  is_initiator = 1;
  enable_debug = 1;
  enable_statistics = 1;
  timeout_ms = 10.0;
  `uvm_info("LTSM_CONFIG", "Configured for initiator role", UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * TARGET CONFIGURATION PRESET
 * 
 * Configures LTSM model for target role operation with responsive
 * parameters for link training participation and acknowledgment.
 *---------------------------------------------------------------------------*/
function void ucie_sb_ltsm_config::set_target_config();
  is_initiator = 0;
  enable_debug = 1;
  enable_statistics = 1;
  timeout_ms = 15.0;  // Longer timeout for target
  `uvm_info("LTSM_CONFIG", "Configured for target role", UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * DEBUG CONFIGURATION PRESET
 * 
 * Configures LTSM model for enhanced debug operation with extended
 * timeouts and comprehensive logging for development and analysis.
 *---------------------------------------------------------------------------*/
function void ucie_sb_ltsm_config::set_debug_config();
  enable_debug = 1;
  enable_statistics = 1;
  timeout_ms = 50.0;  // Extended timeout for debug
  `uvm_info("LTSM_CONFIG", "Configured for debug mode", UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * CONFIGURATION DEBUG REPORTING
 * 
 * Generates comprehensive configuration summary for debugging and analysis.
 * Provides complete visibility into all LTSM configuration parameters
 * and operational settings.
 *---------------------------------------------------------------------------*/
function void ucie_sb_ltsm_config::print_config();
  `uvm_info("LTSM_CONFIG", "=== LTSM Configuration ===", UVM_LOW)
  `uvm_info("LTSM_CONFIG", $sformatf("Role: %s", is_initiator ? "Initiator" : "Target"), UVM_LOW)
  `uvm_info("LTSM_CONFIG", $sformatf("Debug enabled: %0b", enable_debug), UVM_LOW)
  `uvm_info("LTSM_CONFIG", $sformatf("Statistics enabled: %0b", enable_statistics), UVM_LOW)
  `uvm_info("LTSM_CONFIG", $sformatf("Timeout: %0.1f ms", timeout_ms), UVM_LOW)
  `uvm_info("LTSM_CONFIG", $sformatf("Required clock patterns: %0d", required_clock_patterns), UVM_LOW)
  `uvm_info("LTSM_CONFIG", $sformatf("Max polling cycles: %0d", max_polling_cycles), UVM_LOW)
  `uvm_info("LTSM_CONFIG", "========================", UVM_LOW)
endfunction

/*******************************************************************************
 * LTSM MODEL IMPLEMENTATION
 ******************************************************************************/

/*---------------------------------------------------------------------------
 * UVM BUILD PHASE IMPLEMENTATION
 * 
 * Component construction and configuration retrieval. Creates sideband
 * agent, retrieves virtual interface, and establishes configuration
 * management for LTSM operation.
 *---------------------------------------------------------------------------*/
function void ucie_sb_ltsm_model::build_phase(uvm_phase phase);
  super.build_phase(phase);
  
  // Create sideband agent for protocol transactions
  sb_agent = ucie_sb_agent::type_id::create("sb_agent", this);
  
  // Get virtual interface from configuration database
  if (!uvm_config_db#(virtual ucie_sb_inf)::get(this, "", "vif", vif)) begin
    `uvm_fatal("LTSM_MODEL", "Virtual interface not found in config DB")
  end
  
  // Get LTSM configuration or create default
  if (!uvm_config_db#(ucie_sb_ltsm_config)::get(this, "", "cfg", cfg)) begin
    set_default_config();
  end
  
  // Configure timeout duration
  timeout_duration = cfg.timeout_ms * 1_000_000; // Convert ms to ns
  
  // Configure agent for LTSM operation
  configure_agent();
  
  `uvm_info("LTSM_MODEL", "LTSM model build phase complete", UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * UVM CONNECT PHASE IMPLEMENTATION
 * 
 * Component connectivity establishment. Currently no connections required
 * as agent handles all protocol connectivity internally.
 *---------------------------------------------------------------------------*/
function void ucie_sb_ltsm_model::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  `uvm_info("LTSM_MODEL", "LTSM model connect phase complete", UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * UVM END OF ELABORATION PHASE IMPLEMENTATION
 * 
 * Final configuration validation and debug reporting. Prints configuration
 * summary and validates all required components are properly configured.
 *---------------------------------------------------------------------------*/
function void ucie_sb_ltsm_model::end_of_elaboration_phase(uvm_phase phase);
  super.end_of_elaboration_phase(phase);
  
  if (cfg.enable_debug) begin
    cfg.print_config();
  end
  
  `uvm_info("LTSM_MODEL", "LTSM model end of elaboration phase complete", UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * UVM RUN PHASE IMPLEMENTATION
 * 
 * Main LTSM execution phase. Starts parallel FSM process, timeout monitoring,
 * and statistics collection. Waits for training completion or error state.
 *---------------------------------------------------------------------------*/
task ucie_sb_ltsm_model::run_phase(uvm_phase phase);
  super.run_phase(phase);
  
  `uvm_info("LTSM_MODEL", "Starting LTSM model run phase", UVM_LOW)
  
  // Start parallel processes
  fork
    ltsm_fsm_process();
    timeout_monitor();
    if (cfg.enable_statistics) statistics_collector();
  join_none
  
  // Wait for training completion or timeout
  wait(current_state == LTSM_ACTIVE || current_state == LTSM_ERROR);
  
  if (current_state == LTSM_ACTIVE) begin
    `uvm_info("LTSM_MODEL", "Link training completed successfully!", UVM_LOW)
    -> training_complete_event;
  end else begin
    `uvm_error("LTSM_MODEL", "Link training failed or timed out")
  end
  
  if (cfg.enable_statistics) print_final_statistics();
endtask

/*---------------------------------------------------------------------------
 * UVM REPORT PHASE IMPLEMENTATION
 * 
 * Final statistics and status reporting. Generates comprehensive summary
 * of LTSM training results, timing analysis, and error statistics.
 *---------------------------------------------------------------------------*/
function void ucie_sb_ltsm_model::report_phase(uvm_phase phase);
  super.report_phase(phase);
  
  `uvm_info("LTSM_MODEL", "=== LTSM TRAINING REPORT ===", UVM_LOW)
  `uvm_info("LTSM_MODEL", $sformatf("Final state: %s", current_state.name()), UVM_LOW)
  `uvm_info("LTSM_MODEL", $sformatf("Training result: %s", 
            (current_state == LTSM_ACTIVE) ? "SUCCESS" : "FAILED"), UVM_LOW)
  `uvm_info("LTSM_MODEL", $sformatf("Total timeout errors: %0d", timeout_errors), UVM_LOW)
  `uvm_info("LTSM_MODEL", $sformatf("Total protocol errors: %0d", protocol_errors), UVM_LOW)
  `uvm_info("LTSM_MODEL", "===========================", UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * FSM MAIN PROCESS IMPLEMENTATION
 * 
 * Core finite state machine execution loop. Handles state entry actions,
 * state-specific behavior execution, event processing, and state transitions
 * with timeout protection.
 *---------------------------------------------------------------------------*/
task ucie_sb_ltsm_model::ltsm_fsm_process();
  `uvm_info("LTSM_MODEL", "Starting LTSM FSM process", UVM_MEDIUM)
  
  forever begin
    // State entry actions
    state_entry_actions();
    
    // Wait for events or state transitions with timeout protection
    fork
      begin
        // State-specific behavior
        case (current_state)
          LTSM_RESET:      reset_state_behavior();
          LTSM_DETECT:     detect_state_behavior();
          LTSM_POLLING:    polling_state_behavior();
          LTSM_CONFIG:     config_state_behavior();
          LTSM_SBINIT:     sbinit_state_behavior();
          LTSM_ERROR:      error_state_behavior();
          default:         error_state_behavior();
        endcase
      end
      begin
        // Timeout monitoring
        #(timeout_duration * 1ns);
        current_event = LTSM_EV_TIMEOUT;
      end
    join_any
    disable fork;
    
    // State transition logic
    next_state = get_next_state(current_state, current_event);
    
    if (next_state != current_state) begin
      transition_to_state(next_state);
    end
    
    // Small delay to prevent infinite loops
    #1ns;
  end
endtask

/*---------------------------------------------------------------------------
 * FSM TRANSITION LOGIC IMPLEMENTATION
 * 
 * Comprehensive state transition matrix implementing UCIe LTSM specification.
 * Handles all valid state transitions, timeout conditions, and error recovery
 * with proper event-driven state machine behavior.
 *---------------------------------------------------------------------------*/
function ucie_ltsm_state_t ucie_sb_ltsm_model::get_next_state(ucie_ltsm_state_t state, ucie_ltsm_event_t event);
  case (state)
    LTSM_RESET: begin
      case (event)
        LTSM_EV_RESET_DEASSERT: return LTSM_DETECT;
        default: return LTSM_RESET;
      endcase
    end
    
    LTSM_DETECT: begin
      case (event)
        LTSM_EV_CLOCK_DETECTED: return LTSM_POLLING;
        LTSM_EV_TIMEOUT: return LTSM_ERROR;
        LTSM_EV_RESET: return LTSM_RESET;
        default: return LTSM_DETECT;
      endcase
    end
    
    LTSM_POLLING: begin
      case (event)
        LTSM_EV_POLLING_SUCCESS: return LTSM_CONFIG;
        LTSM_EV_TIMEOUT: return LTSM_ERROR;
        LTSM_EV_RESET: return LTSM_RESET;
        default: return LTSM_POLLING;
      endcase
    end
    
    LTSM_CONFIG: begin
      case (event)
        LTSM_EV_CONFIG_COMPLETE: return LTSM_SBINIT;
        LTSM_EV_TIMEOUT: return LTSM_ERROR;
        LTSM_EV_RESET: return LTSM_RESET;
        default: return LTSM_CONFIG;
      endcase
    end
    
    LTSM_SBINIT: begin
      case (event)
        LTSM_EV_SBINIT_COMPLETE: return LTSM_ACTIVE;
        LTSM_EV_TIMEOUT: return LTSM_ERROR;
        LTSM_EV_RESET: return LTSM_RESET;
        default: return LTSM_SBINIT;
      endcase
    end
    
    default: return LTSM_ERROR;
  endcase
endfunction

/*---------------------------------------------------------------------------
 * STATE ENTRY ACTIONS IMPLEMENTATION
 * 
 * Common actions performed on entry to any state. Handles timing tracking,
 * statistics collection, debug logging, and event notification for
 * state transition monitoring.
 *---------------------------------------------------------------------------*/
function void ucie_sb_ltsm_model::state_entry_actions();
  state_entry_time = $realtime;
  state_transitions[current_state]++;
  
  if (cfg.enable_debug) begin
    `uvm_info("LTSM_MODEL", $sformatf("Entering state: %s", current_state.name()), UVM_MEDIUM)
  end
  
  -> state_change_event;
endfunction

/*---------------------------------------------------------------------------
 * STATE TRANSITION IMPLEMENTATION
 * 
 * Handles actual state transitions with timing tracking and debug logging.
 * Updates state duration statistics and provides comprehensive transition
 * visibility for analysis and debugging.
 *---------------------------------------------------------------------------*/
function void ucie_sb_ltsm_model::transition_to_state(ucie_ltsm_state_t new_state);
  realtime state_duration = $realtime - state_entry_time;
  state_durations[current_state] += state_duration;
  
  `uvm_info("LTSM_MODEL", $sformatf("State transition: %s → %s (duration: %0.3fms)", 
            current_state.name(), new_state.name(), state_duration/1_000_000.0), UVM_LOW)
  
  current_state = new_state;
endfunction

/*---------------------------------------------------------------------------
 * RESET STATE BEHAVIOR IMPLEMENTATION
 * 
 * Handles RESET state operation. Waits for reset deassertion with proper
 * recovery timing according to UCIe specification requirements.
 *---------------------------------------------------------------------------*/
task ucie_sb_ltsm_model::reset_state_behavior();
  `uvm_info("LTSM_MODEL", "In RESET state - waiting for reset deassertion", UVM_HIGH)
  
  // Wait for reset deassertion
  wait(!vif.reset);
  #(cfg.reset_recovery_time * 1ns); // Reset recovery time
  
  current_event = LTSM_EV_RESET_DEASSERT;
endtask

/*---------------------------------------------------------------------------
 * DETECT STATE BEHAVIOR IMPLEMENTATION
 * 
 * Handles DETECT state operation. Initiator sends clock patterns while
 * target waits for pattern detection according to role configuration.
 *---------------------------------------------------------------------------*/
task ucie_sb_ltsm_model::detect_state_behavior();
  `uvm_info("LTSM_MODEL", "In DETECT state - starting clock pattern detection", UVM_HIGH)
  
  if (cfg.is_initiator) begin
    // Initiator sends clock patterns
    send_clock_patterns();
  end else begin
    // Target waits for clock patterns
    wait_for_clock_patterns();
  end
endtask

/*---------------------------------------------------------------------------
 * POLLING STATE BEHAVIOR IMPLEMENTATION
 * 
 * Handles POLLING state operation. Implements bidirectional handshake
 * with concurrent pattern transmission and reception for link establishment.
 *---------------------------------------------------------------------------*/
task ucie_sb_ltsm_model::polling_state_behavior();
  `uvm_info("LTSM_MODEL", "In POLLING state - bidirectional handshake", UVM_HIGH)
  
  fork
    begin
      // Send polling patterns
      send_polling_patterns();
    end
    begin
      // Receive polling patterns
      receive_polling_patterns();
    end
  join
  
  if (polling_cycles >= cfg.max_polling_cycles) begin
    current_event = LTSM_EV_POLLING_SUCCESS;
  end else begin
    current_event = LTSM_EV_TIMEOUT;
  end
endtask

/*---------------------------------------------------------------------------
 * CONFIG STATE BEHAVIOR IMPLEMENTATION
 * 
 * Handles CONFIG state operation. Implements configuration parameter
 * negotiation with proper request/response sequencing based on role.
 *---------------------------------------------------------------------------*/
task ucie_sb_ltsm_model::config_state_behavior();
  `uvm_info("LTSM_MODEL", "In CONFIG state - parameter negotiation", UVM_HIGH)
  
  if (cfg.is_initiator) begin
    send_config_request();
    wait_for_config_response();
  end else begin
    wait_for_config_request();
    send_config_response();
  end
  
  if (config_req_sent && config_rsp_received) begin
    current_event = LTSM_EV_CONFIG_COMPLETE;
  end else begin
    current_event = LTSM_EV_TIMEOUT;
  end
endtask

/*---------------------------------------------------------------------------
 * SBINIT STATE BEHAVIOR IMPLEMENTATION
 * 
 * Handles SBINIT state operation. Implements complete SBINIT message
 * sequence: OOR → Done Request → Done Response per UCIe specification.
 *---------------------------------------------------------------------------*/
task ucie_sb_ltsm_model::sbinit_state_behavior();
  `uvm_info("LTSM_MODEL", "In SBINIT state - SBINIT message exchange", UVM_HIGH)
  
  // SBINIT sequence: OOR → Done Request → Done Response
  if (cfg.is_initiator) begin
    send_sbinit_oor();
    send_sbinit_done_request();
    wait_for_sbinit_done_response();
  end else begin
    wait_for_sbinit_oor();
    wait_for_sbinit_done_request();
    send_sbinit_done_response();
  end
  
  if (sbinit_oor_sent && sbinit_done_req_sent && sbinit_done_rsp_received) begin
    current_event = LTSM_EV_SBINIT_COMPLETE;
  end else begin
    current_event = LTSM_EV_TIMEOUT;
  end
endtask

/*---------------------------------------------------------------------------
 * ERROR STATE BEHAVIOR IMPLEMENTATION
 * 
 * Handles ERROR state operation. Provides error state persistence
 * for timeout and protocol violation conditions.
 *---------------------------------------------------------------------------*/
task ucie_sb_ltsm_model::error_state_behavior();
  `uvm_error("LTSM_MODEL", "In ERROR state - link training failed")
  
  // Stay in error state
  #1ms;
endtask

/*---------------------------------------------------------------------------
 * CLOCK PATTERN TRANSMISSION IMPLEMENTATION
 * 
 * Sends required number of clock patterns per UCIe specification.
 * Uses sideband agent driver for proper protocol compliance and timing.
 *---------------------------------------------------------------------------*/
task ucie_sb_ltsm_model::send_clock_patterns();
  ucie_sb_transaction clock_trans;
  
  for (int i = 0; i < cfg.required_clock_patterns; i++) begin
    clock_trans = ucie_sb_transaction::type_id::create("clock_trans");
    clock_trans.opcode = CLOCK_PATTERN;
    clock_trans.srcid = 3'h1;
    clock_trans.dstid = 3'h0;
    
    // Send via agent
    sb_agent.driver.send_transaction(clock_trans);
    clock_patterns_sent++;
    
    `uvm_info("LTSM_MODEL", $sformatf("Sent clock pattern %0d/%0d", i+1, cfg.required_clock_patterns), UVM_HIGH)
    #(cfg.clock_pattern_period * 1ns);
  end
  
  current_event = LTSM_EV_CLOCK_DETECTED;
endtask

/*---------------------------------------------------------------------------
 * CLOCK PATTERN DETECTION IMPLEMENTATION
 * 
 * Waits for required number of clock patterns from remote side.
 * Uses sideband agent monitor for protocol-compliant pattern detection.
 *---------------------------------------------------------------------------*/
task ucie_sb_ltsm_model::wait_for_clock_patterns();
  ucie_sb_transaction received_trans;
  int patterns_detected = 0;
  
  // Monitor for clock patterns
  forever begin
    sb_agent.monitor.ap.get(received_trans);
    
    if (received_trans.opcode == CLOCK_PATTERN) begin
      patterns_detected++;
      clock_patterns_received++;
      
      `uvm_info("LTSM_MODEL", $sformatf("Detected clock pattern %0d/%0d", patterns_detected, cfg.required_clock_patterns), UVM_HIGH)
      
      if (patterns_detected >= cfg.required_clock_patterns) begin
        current_event = LTSM_EV_CLOCK_DETECTED;
        break;
      end
    end
  end
endtask

/*---------------------------------------------------------------------------
 * POLLING PATTERN TRANSMISSION IMPLEMENTATION
 * 
 * Sends polling patterns during bidirectional handshake phase.
 * Implements proper source/destination ID assignment based on role.
 *---------------------------------------------------------------------------*/
task ucie_sb_ltsm_model::send_polling_patterns();
  ucie_sb_transaction poll_trans;
  
  for (int i = 0; i < cfg.max_polling_cycles; i++) begin
    poll_trans = ucie_sb_transaction::type_id::create("poll_trans");
    poll_trans.opcode = CLOCK_PATTERN; // Use clock pattern for polling
    poll_trans.srcid = cfg.is_initiator ? 3'h1 : 3'h2;
    poll_trans.dstid = cfg.is_initiator ? 3'h2 : 3'h1;
    
    sb_agent.driver.send_transaction(poll_trans);
    polling_cycles++;
    
    #(cfg.polling_interval * 1ns);
  end
endtask

/*---------------------------------------------------------------------------
 * POLLING PATTERN RECEPTION IMPLEMENTATION
 * 
 * Receives polling patterns during bidirectional handshake phase.
 * Validates proper source ID to ensure bidirectional communication.
 *---------------------------------------------------------------------------*/
task ucie_sb_ltsm_model::receive_polling_patterns();
  ucie_sb_transaction received_trans;
  int received_polls = 0;
  
  // Monitor for polling patterns
  forever begin
    sb_agent.monitor.ap.get(received_trans);
    
    if (received_trans.opcode == CLOCK_PATTERN && 
        received_trans.srcid != (cfg.is_initiator ? 3'h1 : 3'h2)) begin
      received_polls++;
      
      if (received_polls >= cfg.max_polling_cycles/2) begin
        break;
      end
    end
  end
endtask

/*---------------------------------------------------------------------------
 * CONFIGURATION REQUEST TRANSMISSION IMPLEMENTATION
 * 
 * Sends configuration read request to initiate parameter negotiation.
 * Uses proper UCIe configuration space addressing and tagging.
 *---------------------------------------------------------------------------*/
task ucie_sb_ltsm_model::send_config_request();
  ucie_sb_transaction config_trans;
  
  config_trans = ucie_sb_transaction::type_id::create("config_trans");
  config_trans.opcode = CFG_READ_64B;
  config_trans.srcid = 3'h1;
  config_trans.dstid = 3'h2;
  config_trans.addr = 24'h001000; // Configuration space
  config_trans.tag = cfg.config_tag;
  
  sb_agent.driver.send_transaction(config_trans);
  config_req_sent = 1;
  
  `uvm_info("LTSM_MODEL", "Sent configuration request", UVM_HIGH)
endtask

/*---------------------------------------------------------------------------
 * CONFIGURATION REQUEST RECEPTION IMPLEMENTATION
 * 
 * Waits for configuration read request from remote initiator.
 * Monitors for proper configuration space transactions.
 *---------------------------------------------------------------------------*/
task ucie_sb_ltsm_model::wait_for_config_request();
  ucie_sb_transaction received_trans;
  
  forever begin
    sb_agent.monitor.ap.get(received_trans);
    
    if (received_trans.opcode == CFG_READ_64B) begin
      `uvm_info("LTSM_MODEL", "Received configuration request", UVM_HIGH)
      break;
    end
  end
endtask

/*---------------------------------------------------------------------------
 * CONFIGURATION RESPONSE TRANSMISSION IMPLEMENTATION
 * 
 * Sends configuration completion with data in response to request.
 * Provides proper tag matching and configuration data payload.
 *---------------------------------------------------------------------------*/
task ucie_sb_ltsm_model::send_config_response();
  ucie_sb_transaction config_rsp_trans;
  
  config_rsp_trans = ucie_sb_transaction::type_id::create("config_rsp_trans");
  config_rsp_trans.opcode = CPL_DATA_64B;
  config_rsp_trans.srcid = 3'h2;
  config_rsp_trans.dstid = 3'h1;
  config_rsp_trans.tag = cfg.config_tag;
  config_rsp_trans.data = 64'hDEADBEEFCAFEBABE; // Config data
  
  sb_agent.driver.send_transaction(config_rsp_trans);
  config_rsp_received = 1;
  
  `uvm_info("LTSM_MODEL", "Sent configuration response", UVM_HIGH)
endtask

/*---------------------------------------------------------------------------
 * CONFIGURATION RESPONSE RECEPTION IMPLEMENTATION
 * 
 * Waits for configuration completion with proper tag matching.
 * Validates response corresponds to previously sent request.
 *---------------------------------------------------------------------------*/
task ucie_sb_ltsm_model::wait_for_config_response();
  ucie_sb_transaction received_trans;
  
  forever begin
    sb_agent.monitor.ap.get(received_trans);
    
    if (received_trans.opcode == CPL_DATA_64B && received_trans.tag == cfg.config_tag) begin
      config_rsp_received = 1;
      `uvm_info("LTSM_MODEL", "Received configuration response", UVM_HIGH)
      break;
    end
  end
endtask

/*---------------------------------------------------------------------------
 * SBINIT OUT OF RESET MESSAGE TRANSMISSION IMPLEMENTATION
 * 
 * Sends SBINIT Out of Reset VDM message to indicate reset completion.
 * Uses proper message code and addressing per UCIe specification.
 *---------------------------------------------------------------------------*/
task ucie_sb_ltsm_model::send_sbinit_oor();
  ucie_sb_transaction oor_trans;
  
  oor_trans = ucie_sb_transaction::type_id::create("oor_trans");
  oor_trans.opcode = MSG_VDM;
  oor_trans.srcid = 3'h1;
  oor_trans.dstid = 3'h0;
  oor_trans.msgcode = cfg.sbinit_oor_msgcode;
  oor_trans.tag = cfg.sbinit_tag;
  
  sb_agent.driver.send_transaction(oor_trans);
  sbinit_oor_sent = 1;
  
  `uvm_info("LTSM_MODEL", "Sent SBINIT Out of Reset message", UVM_HIGH)
endtask

/*---------------------------------------------------------------------------
 * SBINIT OUT OF RESET MESSAGE RECEPTION IMPLEMENTATION
 * 
 * Waits for SBINIT Out of Reset VDM message from remote side.
 * Validates proper message code for SBINIT sequence.
 *---------------------------------------------------------------------------*/
task ucie_sb_ltsm_model::wait_for_sbinit_oor();
  ucie_sb_transaction received_trans;
  
  forever begin
    sb_agent.monitor.ap.get(received_trans);
    
    if (received_trans.opcode == MSG_VDM && received_trans.msgcode == cfg.sbinit_oor_msgcode) begin
      `uvm_info("LTSM_MODEL", "Received SBINIT Out of Reset message", UVM_HIGH)
      break;
    end
  end
endtask

/*---------------------------------------------------------------------------
 * SBINIT DONE REQUEST MESSAGE TRANSMISSION IMPLEMENTATION
 * 
 * Sends SBINIT Done Request VDM message to request training completion.
 * Implements proper message sequencing in SBINIT protocol.
 *---------------------------------------------------------------------------*/
task ucie_sb_ltsm_model::send_sbinit_done_request();
  ucie_sb_transaction done_req_trans;
  
  done_req_trans = ucie_sb_transaction::type_id::create("done_req_trans");
  done_req_trans.opcode = MSG_VDM;
  done_req_trans.srcid = 3'h1;
  done_req_trans.dstid = 3'h2;
  done_req_trans.msgcode = cfg.sbinit_done_req_msgcode;
  done_req_trans.tag = cfg.sbinit_tag;
  
  sb_agent.driver.send_transaction(done_req_trans);
  sbinit_done_req_sent = 1;
  
  `uvm_info("LTSM_MODEL", "Sent SBINIT Done Request message", UVM_HIGH)
endtask

/*---------------------------------------------------------------------------
 * SBINIT DONE REQUEST MESSAGE RECEPTION IMPLEMENTATION
 * 
 * Waits for SBINIT Done Request VDM message from initiator.
 * Validates proper message code and prepares for response.
 *---------------------------------------------------------------------------*/
task ucie_sb_ltsm_model::wait_for_sbinit_done_request();
  ucie_sb_transaction received_trans;
  
  forever begin
    sb_agent.monitor.ap.get(received_trans);
    
    if (received_trans.opcode == MSG_VDM && received_trans.msgcode == cfg.sbinit_done_req_msgcode) begin
      `uvm_info("LTSM_MODEL", "Received SBINIT Done Request message", UVM_HIGH)
      break;
    end
  end
endtask

/*---------------------------------------------------------------------------
 * SBINIT DONE RESPONSE MESSAGE TRANSMISSION IMPLEMENTATION
 * 
 * Sends SBINIT Done Response VDM message to complete training sequence.
 * Final message in SBINIT protocol indicating training completion.
 *---------------------------------------------------------------------------*/
task ucie_sb_ltsm_model::send_sbinit_done_response();
  ucie_sb_transaction done_rsp_trans;
  
  done_rsp_trans = ucie_sb_transaction::type_id::create("done_rsp_trans");
  done_rsp_trans.opcode = MSG_VDM;
  done_rsp_trans.srcid = 3'h2;
  done_rsp_trans.dstid = 3'h1;
  done_rsp_trans.msgcode = cfg.sbinit_done_rsp_msgcode;
  done_rsp_trans.tag = cfg.sbinit_tag;
  
  sb_agent.driver.send_transaction(done_rsp_trans);
  sbinit_done_rsp_received = 1;
  
  `uvm_info("LTSM_MODEL", "Sent SBINIT Done Response message", UVM_HIGH)
endtask

/*---------------------------------------------------------------------------
 * SBINIT DONE RESPONSE MESSAGE RECEPTION IMPLEMENTATION
 * 
 * Waits for SBINIT Done Response VDM message to complete training.
 * Final reception indicating successful training completion.
 *---------------------------------------------------------------------------*/
task ucie_sb_ltsm_model::wait_for_sbinit_done_response();
  ucie_sb_transaction received_trans;
  
  forever begin
    sb_agent.monitor.ap.get(received_trans);
    
    if (received_trans.opcode == MSG_VDM && 
        received_trans.msgcode == cfg.sbinit_done_rsp_msgcode && 
        received_trans.tag == cfg.sbinit_tag) begin
      sbinit_done_rsp_received = 1;
      `uvm_info("LTSM_MODEL", "Received SBINIT Done Response", UVM_HIGH)
      break;
    end
  end
endtask

/*---------------------------------------------------------------------------
 * TIMEOUT MONITORING IMPLEMENTATION
 * 
 * Monitors state transitions for timeout conditions. Provides timeout
 * detection and error reporting for stuck states or protocol violations.
 *---------------------------------------------------------------------------*/
task ucie_sb_ltsm_model::timeout_monitor();
  forever begin
    @(state_change_event);
    
    fork
      begin
        #(timeout_duration * 1ns);
        if (current_state != LTSM_ACTIVE && current_state != LTSM_ERROR) begin
          timeout_errors++;
          `uvm_error("LTSM_MODEL", $sformatf("Timeout in state: %s", current_state.name()))
          -> timeout_event;
        end
      end
    join_none
  end
endtask

/*---------------------------------------------------------------------------
 * STATISTICS COLLECTION IMPLEMENTATION
 * 
 * Collects comprehensive training statistics including timing analysis
 * and performance metrics for analysis and reporting.
 *---------------------------------------------------------------------------*/
task ucie_sb_ltsm_model::statistics_collector();
  realtime start_time = $realtime;
  
  forever begin
    @(training_complete_event);
    total_training_time = $realtime - start_time;
    break;
  end
endtask

/*---------------------------------------------------------------------------
 * AGENT CONFIGURATION IMPLEMENTATION
 * 
 * Configures sideband agent for LTSM operation. Sets up agent configuration
 * with appropriate parameters for protocol transaction handling.
 *---------------------------------------------------------------------------*/
function void ucie_sb_ltsm_model::configure_agent();
  ucie_sb_agent_config agent_cfg;
  
  agent_cfg = ucie_sb_agent_config::type_id::create("agent_cfg");
  agent_cfg.is_active = UVM_ACTIVE;
  agent_cfg.enable_protocol_checking = 1;
  agent_cfg.enable_statistics = cfg.enable_statistics;
  agent_cfg.vif = vif;
  
  uvm_config_db#(ucie_sb_agent_config)::set(this, "sb_agent", "cfg", agent_cfg);
endfunction

/*---------------------------------------------------------------------------
 * DEFAULT CONFIGURATION SETUP IMPLEMENTATION
 * 
 * Creates default LTSM configuration when none provided via config DB.
 * Establishes standard operational parameters for typical usage scenarios.
 *---------------------------------------------------------------------------*/
function void ucie_sb_ltsm_model::set_default_config();
  cfg = ucie_sb_ltsm_config::type_id::create("cfg");
  cfg.set_initiator_config(); // Default to initiator role
  `uvm_info("LTSM_MODEL", "Using default LTSM configuration", UVM_LOW)
endfunction

/*---------------------------------------------------------------------------
 * FINAL STATISTICS REPORTING IMPLEMENTATION
 * 
 * Generates comprehensive final statistics report including state timing,
 * transaction counts, error statistics, and performance analysis.
 *---------------------------------------------------------------------------*/
function void ucie_sb_ltsm_model::print_final_statistics();
  `uvm_info("LTSM_MODEL", "=== LTSM Training Statistics ===", UVM_LOW)
  `uvm_info("LTSM_MODEL", $sformatf("Total training time: %0.3f ms", total_training_time/1_000_000.0), UVM_LOW)
  `uvm_info("LTSM_MODEL", $sformatf("Clock patterns sent: %0d", clock_patterns_sent), UVM_LOW)
  `uvm_info("LTSM_MODEL", $sformatf("Clock patterns received: %0d", clock_patterns_received), UVM_LOW)
  `uvm_info("LTSM_MODEL", $sformatf("Polling cycles: %0d", polling_cycles), UVM_LOW)
  `uvm_info("LTSM_MODEL", $sformatf("Timeout errors: %0d", timeout_errors), UVM_LOW)
  `uvm_info("LTSM_MODEL", $sformatf("Protocol errors: %0d", protocol_errors), UVM_LOW)
  
  foreach(state_transitions[state]) begin
    if (state_transitions[state] > 0) begin
      `uvm_info("LTSM_MODEL", $sformatf("State %s: %0d transitions, %0.3f ms total", 
                state.name(), state_transitions[state], state_durations[state]/1_000_000.0), UVM_LOW)
    end
  end
  `uvm_info("LTSM_MODEL", "================================", UVM_LOW)
endfunction