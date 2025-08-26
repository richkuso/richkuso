/*******************************************************************************
 * UCIe Sideband Link Training State Machine (LTSM) Model
 * 
 * OVERVIEW:
 *   Production-grade FSM-based model implementing UCIe sideband link training
 *   sequence with simplified RESET → SBINIT → TRAINING state flow according to
 *   UCIe specification. Integrates seamlessly with existing UCIe sideband UVM
 *   agent for comprehensive protocol compliance and transaction-level modeling.
 *
 * LTSM ARCHITECTURE:
 *   • Simplified state machine: RESET → SBINIT → TRAINING
 *   • Trigger-based training initiation via start_link_training control
 *   • Clock pattern detection for automatic training start
 *   • Comprehensive SBINIT message sequence implementation
 *   • Agent integration: Uses existing driver/monitor components
 *   • Protocol compliance: UCIe timing and message requirements
 *
 * FSM STATE SEQUENCE:
 *   • RESET      - Initial reset state, waits for training trigger or clock pattern
 *   • SBINIT     - Complete SBINIT sequence with clock patterns and messages
 *   • TRAINING   - Training completion state
 *
 * RESET STATE TRIGGERS:
 *   • start_link_training bit set → transition to SBINIT
 *   • Clock pattern detected from monitor → transition to SBINIT
 *
 * SBINIT PROTOCOL SEQUENCE:
 *   1. Send clock patterns continuously while monitoring for back-to-back patterns
 *   2. Upon detecting back-to-back patterns, send 4 more clock patterns then stop
 *   3. Send SBINIT Out of Reset (result=1) until received from monitor
 *   4. Send SBINIT Done Request when OOR exchange complete
 *   5. Send SBINIT Done Response when Done Request received
 *   6. Transition to TRAINING when Done Response sent and received
 *
 * INTEGRATION FEATURES:
 *   • Seamless sideband agent integration for TX/RX operations
 *   • UVM methodology compliance with proper phase implementation
 *   • Configuration database utilization for parameter management
 *   • Analysis port connectivity for transaction monitoring
 *   • Comprehensive debug and statistics collection
 *
 * COMPLIANCE:
 *   • IEEE 1800-2017 SystemVerilog
 *   • UVM 1.2 methodology
 *   • UCIe 1.1 specification
 *
 * AUTHOR: UCIe Sideband UVM Agent
 * VERSION: 2.0 - Simplified LTSM with RESET-SBINIT-TRAINING flow
 ******************************************************************************/

//=============================================================================
// UCIe LTSM State Enumeration
//=============================================================================
typedef enum bit [2:0] {
  LTSM_RESET      = 3'h0,  // Reset state - wait for training trigger
  LTSM_SBINIT     = 3'h1,  // SBINIT sequence execution
  LTSM_TRAINING   = 3'h2,  // Training completion state
  LTSM_ERROR      = 3'h7   // Error state
} ucie_ltsm_state_t;

//=============================================================================
// UCIe LTSM Event Enumeration  
//=============================================================================
typedef enum bit [3:0] {
  LTSM_EV_START_TRAINING    = 4'h0,  // start_link_training bit set
  LTSM_EV_CLOCK_DETECTED    = 4'h1,  // Clock pattern detected from monitor
  LTSM_EV_BACK_TO_BACK      = 4'h2,  // Back-to-back clock patterns detected
  LTSM_EV_CLOCK_STOP        = 4'h3,  // Clock pattern transmission complete
  LTSM_EV_OOR_COMPLETE      = 4'h4,  // SBINIT OOR exchange complete
  LTSM_EV_DONE_REQ_SENT     = 4'h5,  // SBINIT Done Request sent
  LTSM_EV_DONE_RESP_COMPLETE = 4'h6, // SBINIT Done Response exchange complete
  LTSM_EV_TIMEOUT           = 4'hE,  // Timeout occurred
  LTSM_EV_ERROR             = 4'hF   // Protocol error
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
  
  bit enable_debug = 1;                    // Enable debug messages
  bit enable_statistics = 1;               // Enable statistics collection
  
  /*---------------------------------------------------------------------------
   * TIMING CONFIGURATION PARAMETERS
   * State timeout and protocol timing control
   *---------------------------------------------------------------------------*/
  
  real timeout_ms = 30.0;                  // State timeout in milliseconds
  real clock_pattern_period = 1250.0;      // Clock pattern period in ns (800MHz)
  real message_interval = 5000.0;          // Message transmission interval in ns
  
  /*---------------------------------------------------------------------------
   * PROTOCOL CONFIGURATION PARAMETERS
   * UCIe specification compliance and validation controls
   *---------------------------------------------------------------------------*/
  
  int final_clock_patterns = 4;            // Final clock patterns after back-to-back detection
  int back_to_back_threshold = 2;          // Consecutive patterns for back-to-back detection
  
  /*---------------------------------------------------------------------------
   * SBINIT MESSAGE CONFIGURATION
   * SBINIT protocol message parameters and result codes
   *---------------------------------------------------------------------------*/
  
  bit [7:0] sbinit_oor_msgcode = 8'h10;    // SBINIT Out of Reset message code
  bit [7:0] sbinit_done_req_msgcode = 8'h11; // SBINIT Done Request message code
  bit [7:0] sbinit_done_rsp_msgcode = 8'h12; // SBINIT Done Response message code
  bit [4:0] sbinit_tag = 5'h11;            // SBINIT message tag
  bit [31:0] oor_result = 32'h1;           // SBINIT OOR result value (=1)
  
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
  
  extern function void set_fast_config();
  extern function void set_debug_config();
  extern function void print_config();

endclass : ucie_sb_ltsm_config

/*******************************************************************************
 * UCIe SIDEBAND LINK TRAINING STATE MACHINE MODEL
 * 
 * Production-grade FSM implementation for UCIe sideband link training sequence.
 * Implements simplified RESET → SBINIT → TRAINING flow with comprehensive
 * protocol compliance and integration with existing sideband UVM agent.
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
   * CONTROL SIGNALS AND TRIGGERS
   * External control interface for training initiation
   *---------------------------------------------------------------------------*/
  
  bit start_link_training = 0;             // External trigger for training start
  
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
   * SBINIT PROTOCOL TRACKING VARIABLES
   * Transaction and protocol sequence monitoring for SBINIT flow
   *---------------------------------------------------------------------------*/
  
  // Clock pattern transmission and detection
  bit clock_pattern_active = 0;            // Clock pattern transmission active
  int clock_patterns_sent = 0;             // Total clock patterns transmitted
  int consecutive_patterns_detected = 0;   // Consecutive patterns from monitor
  bit back_to_back_detected = 0;           // Back-to-back detection flag
  int final_patterns_remaining = 0;        // Remaining patterns after back-to-back
  
  // SBINIT message exchange tracking
  bit oor_sent = 0;                        // SBINIT OOR sent flag
  bit oor_received = 0;                    // SBINIT OOR received flag
  bit done_req_sent = 0;                   // SBINIT Done Request sent flag
  bit done_req_received = 0;               // SBINIT Done Request received flag
  bit done_resp_sent = 0;                  // SBINIT Done Response sent flag
  bit done_resp_received = 0;              // SBINIT Done Response received flag
  
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
  event start_training_event;
  
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
  extern virtual task sbinit_state_behavior();
  extern virtual task training_state_behavior();
  extern virtual task error_state_behavior();
  
  // Control and trigger methods
  extern virtual function void set_start_link_training();
  extern virtual function void clear_start_link_training();
  extern virtual task monitor_training_triggers();
  
  // SBINIT protocol implementation methods
  extern virtual task send_clock_patterns_continuous();
  extern virtual task monitor_back_to_back_patterns();
  extern virtual task send_final_clock_patterns();
  extern virtual task send_oor_messages();
  extern virtual task monitor_oor_messages();
  extern virtual task send_done_request();
  extern virtual task monitor_done_request();
  extern virtual task send_done_response();
  extern virtual task monitor_done_response();
  
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
 * FAST CONFIGURATION PRESET
 * 
 * Configures LTSM model for fast training operation with reduced
 * timeouts and intervals for accelerated simulation.
 *---------------------------------------------------------------------------*/
function void ucie_sb_ltsm_config::set_fast_config();
  enable_debug = 0;
  enable_statistics = 1;
  timeout_ms = 10.0;
  clock_pattern_period = 1250.0;  // Standard 800MHz
  message_interval = 2500.0;      // Faster message interval
  `uvm_info("LTSM_CONFIG", "Configured for fast training", UVM_LOW)
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
  timeout_ms = 50.0;              // Extended timeout for debug
  clock_pattern_period = 1250.0;
  message_interval = 10000.0;     // Slower for debug visibility
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
  `uvm_info("LTSM_CONFIG", $sformatf("Debug enabled: %0b", enable_debug), UVM_LOW)
  `uvm_info("LTSM_CONFIG", $sformatf("Statistics enabled: %0b", enable_statistics), UVM_LOW)
  `uvm_info("LTSM_CONFIG", $sformatf("Timeout: %0.1f ms", timeout_ms), UVM_LOW)
  `uvm_info("LTSM_CONFIG", $sformatf("Clock pattern period: %0.1f ns", clock_pattern_period), UVM_LOW)
  `uvm_info("LTSM_CONFIG", $sformatf("Message interval: %0.1f ns", message_interval), UVM_LOW)
  `uvm_info("LTSM_CONFIG", $sformatf("Final clock patterns: %0d", final_clock_patterns), UVM_LOW)
  `uvm_info("LTSM_CONFIG", $sformatf("Back-to-back threshold: %0d", back_to_back_threshold), UVM_LOW)
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
 * trigger monitoring, and statistics collection. Waits for training completion.
 *---------------------------------------------------------------------------*/
task ucie_sb_ltsm_model::run_phase(uvm_phase phase);
  super.run_phase(phase);
  
  `uvm_info("LTSM_MODEL", "Starting LTSM model run phase", UVM_LOW)
  
  // Start parallel processes
  fork
    ltsm_fsm_process();
    monitor_training_triggers();
    timeout_monitor();
    if (cfg.enable_statistics) statistics_collector();
  join_none
  
  // Wait for training completion or timeout
  wait(current_state == LTSM_TRAINING || current_state == LTSM_ERROR);
  
  if (current_state == LTSM_TRAINING) begin
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
            (current_state == LTSM_TRAINING) ? "SUCCESS" : "FAILED"), UVM_LOW)
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
          LTSM_SBINIT:     sbinit_state_behavior();
          LTSM_TRAINING:   training_state_behavior();
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
 * Comprehensive state transition matrix implementing simplified LTSM flow.
 * Handles RESET → SBINIT → TRAINING transitions with proper event handling.
 *---------------------------------------------------------------------------*/
function ucie_ltsm_state_t ucie_sb_ltsm_model::get_next_state(ucie_ltsm_state_t state, ucie_ltsm_event_t event);
  case (state)
    LTSM_RESET: begin
      case (event)
        LTSM_EV_START_TRAINING: return LTSM_SBINIT;
        LTSM_EV_CLOCK_DETECTED: return LTSM_SBINIT;
        LTSM_EV_TIMEOUT: return LTSM_ERROR;
        default: return LTSM_RESET;
      endcase
    end
    
    LTSM_SBINIT: begin
      case (event)
        LTSM_EV_DONE_RESP_COMPLETE: return LTSM_TRAINING;
        LTSM_EV_TIMEOUT: return LTSM_ERROR;
        default: return LTSM_SBINIT;
      endcase
    end
    
    LTSM_TRAINING: begin
      // Stay in training state (future implementation)
      return LTSM_TRAINING;
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
 * Handles RESET state operation. Waits for start_link_training trigger or
 * clock pattern detection from monitor to initiate training sequence.
 *---------------------------------------------------------------------------*/
task ucie_sb_ltsm_model::reset_state_behavior();
  `uvm_info("LTSM_MODEL", "In RESET state - waiting for training trigger or clock pattern", UVM_HIGH)
  
  // Wait for training triggers
  forever begin
    #100ns; // Small delay for trigger checking
    
    // Check for start_link_training trigger
    if (start_link_training) begin
      `uvm_info("LTSM_MODEL", "start_link_training trigger detected", UVM_MEDIUM)
      current_event = LTSM_EV_START_TRAINING;
      break;
    end
    
    // Note: Clock pattern detection is handled by monitor_training_triggers()
    // which will set current_event = LTSM_EV_CLOCK_DETECTED
  end
endtask

/*---------------------------------------------------------------------------
 * SBINIT STATE BEHAVIOR IMPLEMENTATION
 * 
 * Handles complete SBINIT state operation implementing the specified protocol:
 * 1. Send clock patterns continuously while monitoring for back-to-back
 * 2. Send 4 more patterns after back-to-back detection, then stop
 * 3. Exchange SBINIT Out of Reset messages (result=1)
 * 4. Exchange SBINIT Done Request/Response messages
 * 5. Transition to TRAINING when complete
 *---------------------------------------------------------------------------*/
task ucie_sb_ltsm_model::sbinit_state_behavior();
  `uvm_info("LTSM_MODEL", "In SBINIT state - starting protocol sequence", UVM_HIGH)
  
  // Reset SBINIT tracking variables
  clock_pattern_active = 1;
  back_to_back_detected = 0;
  final_patterns_remaining = 0;
  oor_sent = 0;
  oor_received = 0;
  done_req_sent = 0;
  done_req_received = 0;
  done_resp_sent = 0;
  done_resp_received = 0;
  
  // Start parallel SBINIT processes
  fork
    send_clock_patterns_continuous();       // Send clock patterns
    monitor_back_to_back_patterns();        // Monitor for back-to-back patterns
    send_oor_messages();                    // Send SBINIT OOR messages
    monitor_oor_messages();                 // Monitor SBINIT OOR messages
    send_done_request();                    // Send Done Request when appropriate
    monitor_done_request();                 // Monitor for Done Request
    send_done_response();                   // Send Done Response when appropriate
    monitor_done_response();                // Monitor for Done Response
  join_none
  
  // Wait for completion
  wait(done_resp_sent && done_resp_received);
  current_event = LTSM_EV_DONE_RESP_COMPLETE;
endtask

/*---------------------------------------------------------------------------
 * TRAINING STATE BEHAVIOR IMPLEMENTATION
 * 
 * Handles TRAINING state operation. Currently a placeholder for future
 * implementation of training completion activities.
 *---------------------------------------------------------------------------*/
task ucie_sb_ltsm_model::training_state_behavior();
  `uvm_info("LTSM_MODEL", "In TRAINING state - training complete", UVM_LOW)
  
  // TODO: Implement training completion activities
  // Stay in training state
  #1ms;
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
 * START LINK TRAINING CONTROL IMPLEMENTATION
 * 
 * Sets the start_link_training trigger bit to initiate training from
 * RESET state. Provides external control interface for training start.
 *---------------------------------------------------------------------------*/
function void ucie_sb_ltsm_model::set_start_link_training();
  start_link_training = 1;
  -> start_training_event;
  `uvm_info("LTSM_MODEL", "start_link_training trigger set", UVM_MEDIUM)
endfunction

/*---------------------------------------------------------------------------
 * CLEAR LINK TRAINING CONTROL IMPLEMENTATION
 * 
 * Clears the start_link_training trigger bit. Provides control interface
 * for trigger management and state cleanup.
 *---------------------------------------------------------------------------*/
function void ucie_sb_ltsm_model::clear_start_link_training();
  start_link_training = 0;
  `uvm_info("LTSM_MODEL", "start_link_training trigger cleared", UVM_MEDIUM)
endfunction

/*---------------------------------------------------------------------------
 * TRAINING TRIGGER MONITORING IMPLEMENTATION
 * 
 * Monitors sideband agent for clock pattern transactions that can trigger
 * training initiation from RESET state. Runs continuously to detect
 * incoming clock patterns from remote side.
 *---------------------------------------------------------------------------*/
task ucie_sb_ltsm_model::monitor_training_triggers();
  ucie_sb_transaction received_trans;
  
  forever begin
    // Monitor transactions from sideband agent
    sb_agent.monitor.ap.get(received_trans);
    
    // Check for clock pattern in RESET state
    if (current_state == LTSM_RESET && received_trans.opcode == CLOCK_PATTERN) begin
      `uvm_info("LTSM_MODEL", "Clock pattern detected from monitor - triggering training", UVM_MEDIUM)
      current_event = LTSM_EV_CLOCK_DETECTED;
    end
    
    // Track consecutive patterns for back-to-back detection in SBINIT
    if (current_state == LTSM_SBINIT && received_trans.opcode == CLOCK_PATTERN) begin
      consecutive_patterns_detected++;
      if (cfg.enable_debug) begin
        `uvm_info("LTSM_MODEL", $sformatf("Clock pattern detected: %0d consecutive", consecutive_patterns_detected), UVM_HIGH)
      end
    end else begin
      consecutive_patterns_detected = 0; // Reset counter for non-clock patterns
    end
  end
endtask

/*---------------------------------------------------------------------------
 * CONTINUOUS CLOCK PATTERN TRANSMISSION IMPLEMENTATION
 * 
 * Sends clock patterns continuously during SBINIT state until back-to-back
 * patterns are detected and final patterns are transmitted. Implements
 * the specified clock pattern transmission protocol.
 *---------------------------------------------------------------------------*/
task ucie_sb_ltsm_model::send_clock_patterns_continuous();
  ucie_sb_transaction clock_trans;
  
  while (clock_pattern_active) begin
    // Create and send clock pattern transaction
    clock_trans = ucie_sb_transaction::type_id::create("clock_trans");
    clock_trans.opcode = CLOCK_PATTERN;
    clock_trans.srcid = 3'h1;
    clock_trans.dstid = 3'h0;
    
    sb_agent.driver.send_transaction(clock_trans);
    clock_patterns_sent++;
    
    if (cfg.enable_debug) begin
      `uvm_info("LTSM_MODEL", $sformatf("Sent clock pattern %0d", clock_patterns_sent), UVM_HIGH)
    end
    
    // Wait for next transmission
    #(cfg.clock_pattern_period * 1ns);
  end
  
  `uvm_info("LTSM_MODEL", "Clock pattern transmission stopped", UVM_MEDIUM)
endtask

/*---------------------------------------------------------------------------
 * BACK-TO-BACK PATTERN MONITORING IMPLEMENTATION
 * 
 * Monitors for back-to-back clock pattern detection and triggers final
 * pattern transmission sequence. Implements the specified detection logic
 * for transitioning from continuous to final pattern transmission.
 *---------------------------------------------------------------------------*/
task ucie_sb_ltsm_model::monitor_back_to_back_patterns();
  forever begin
    // Wait for back-to-back threshold to be reached
    wait(consecutive_patterns_detected >= cfg.back_to_back_threshold);
    
    if (!back_to_back_detected) begin
      back_to_back_detected = 1;
      final_patterns_remaining = cfg.final_clock_patterns;
      
      `uvm_info("LTSM_MODEL", $sformatf("Back-to-back clock patterns detected - sending %0d final patterns", 
                cfg.final_clock_patterns), UVM_MEDIUM)
      
      // Start final pattern transmission
      fork
        send_final_clock_patterns();
      join_none
      
      break;
    end
    
    #100ns; // Small delay
  end
endtask

/*---------------------------------------------------------------------------
 * FINAL CLOCK PATTERN TRANSMISSION IMPLEMENTATION
 * 
 * Sends the specified number of final clock patterns after back-to-back
 * detection, then stops clock pattern transmission. Implements the
 * completion of clock pattern phase in SBINIT sequence.
 *---------------------------------------------------------------------------*/
task ucie_sb_ltsm_model::send_final_clock_patterns();
  ucie_sb_transaction clock_trans;
  
  for (int i = 0; i < cfg.final_clock_patterns; i++) begin
    clock_trans = ucie_sb_transaction::type_id::create("final_clock_trans");
    clock_trans.opcode = CLOCK_PATTERN;
    clock_trans.srcid = 3'h1;
    clock_trans.dstid = 3'h0;
    
    sb_agent.driver.send_transaction(clock_trans);
    final_patterns_remaining--;
    
    `uvm_info("LTSM_MODEL", $sformatf("Sent final clock pattern %0d/%0d", 
              i+1, cfg.final_clock_patterns), UVM_MEDIUM)
    
    #(cfg.clock_pattern_period * 1ns);
  end
  
  // Stop clock pattern transmission
  clock_pattern_active = 0;
  `uvm_info("LTSM_MODEL", "Final clock patterns sent - stopping transmission", UVM_MEDIUM)
endtask

/*---------------------------------------------------------------------------
 * SBINIT OUT OF RESET MESSAGE TRANSMISSION IMPLEMENTATION
 * 
 * Sends SBINIT Out of Reset messages with result=1 continuously until
 * OOR message is received from monitor. Implements the OOR exchange
 * phase of SBINIT protocol sequence.
 *---------------------------------------------------------------------------*/
task ucie_sb_ltsm_model::send_oor_messages();
  ucie_sb_transaction oor_trans;
  
  // Wait for clock patterns to stop before starting OOR messages
  wait(!clock_pattern_active);
  
  while (!oor_received) begin
    oor_trans = ucie_sb_transaction::type_id::create("oor_trans");
    oor_trans.opcode = MSG_VDM;
    oor_trans.srcid = 3'h1;
    oor_trans.dstid = 3'h0;
    oor_trans.msgcode = cfg.sbinit_oor_msgcode;
    oor_trans.tag = cfg.sbinit_tag;
    oor_trans.data[31:0] = cfg.oor_result; // result = 1
    
    sb_agent.driver.send_transaction(oor_trans);
    oor_sent = 1;
    
    `uvm_info("LTSM_MODEL", "Sent SBINIT Out of Reset message (result=1)", UVM_HIGH)
    
    #(cfg.message_interval * 1ns);
  end
  
  `uvm_info("LTSM_MODEL", "SBINIT OOR exchange complete", UVM_MEDIUM)
endtask

/*---------------------------------------------------------------------------
 * SBINIT OUT OF RESET MESSAGE MONITORING IMPLEMENTATION
 * 
 * Monitors for SBINIT Out of Reset messages from remote side to complete
 * the OOR exchange phase. Sets completion flag when OOR message received.
 *---------------------------------------------------------------------------*/
task ucie_sb_ltsm_model::monitor_oor_messages();
  ucie_sb_transaction received_trans;
  
  forever begin
    sb_agent.monitor.ap.get(received_trans);
    
    if (received_trans.opcode == MSG_VDM && 
        received_trans.msgcode == cfg.sbinit_oor_msgcode) begin
      oor_received = 1;
      `uvm_info("LTSM_MODEL", "Received SBINIT Out of Reset message", UVM_HIGH)
      break;
    end
  end
endtask

/*---------------------------------------------------------------------------
 * SBINIT DONE REQUEST MESSAGE TRANSMISSION IMPLEMENTATION
 * 
 * Sends SBINIT Done Request message when OOR exchange is complete.
 * Implements the Done Request phase of SBINIT protocol sequence.
 *---------------------------------------------------------------------------*/
task ucie_sb_ltsm_model::send_done_request();
  ucie_sb_transaction done_req_trans;
  
  // Wait for OOR exchange to complete
  wait(oor_sent && oor_received);
  
  done_req_trans = ucie_sb_transaction::type_id::create("done_req_trans");
  done_req_trans.opcode = MSG_VDM;
  done_req_trans.srcid = 3'h1;
  done_req_trans.dstid = 3'h2;
  done_req_trans.msgcode = cfg.sbinit_done_req_msgcode;
  done_req_trans.tag = cfg.sbinit_tag;
  
  sb_agent.driver.send_transaction(done_req_trans);
  done_req_sent = 1;
  
  `uvm_info("LTSM_MODEL", "Sent SBINIT Done Request message", UVM_MEDIUM)
endtask

/*---------------------------------------------------------------------------
 * SBINIT DONE REQUEST MESSAGE MONITORING IMPLEMENTATION
 * 
 * Monitors for SBINIT Done Request messages from remote side to trigger
 * Done Response transmission. Sets received flag when Done Request detected.
 *---------------------------------------------------------------------------*/
task ucie_sb_ltsm_model::monitor_done_request();
  ucie_sb_transaction received_trans;
  
  forever begin
    sb_agent.monitor.ap.get(received_trans);
    
    if (received_trans.opcode == MSG_VDM && 
        received_trans.msgcode == cfg.sbinit_done_req_msgcode) begin
      done_req_received = 1;
      `uvm_info("LTSM_MODEL", "Received SBINIT Done Request message", UVM_MEDIUM)
      break;
    end
  end
endtask

/*---------------------------------------------------------------------------
 * SBINIT DONE RESPONSE MESSAGE TRANSMISSION IMPLEMENTATION
 * 
 * Sends SBINIT Done Response message when Done Request is received.
 * Implements the Done Response phase of SBINIT protocol sequence.
 *---------------------------------------------------------------------------*/
task ucie_sb_ltsm_model::send_done_response();
  ucie_sb_transaction done_resp_trans;
  
  // Wait for Done Request to be received
  wait(done_req_received);
  
  done_resp_trans = ucie_sb_transaction::type_id::create("done_resp_trans");
  done_resp_trans.opcode = MSG_VDM;
  done_resp_trans.srcid = 3'h2;
  done_resp_trans.dstid = 3'h1;
  done_resp_trans.msgcode = cfg.sbinit_done_rsp_msgcode;
  done_resp_trans.tag = cfg.sbinit_tag;
  
  sb_agent.driver.send_transaction(done_resp_trans);
  done_resp_sent = 1;
  
  `uvm_info("LTSM_MODEL", "Sent SBINIT Done Response message", UVM_MEDIUM)
endtask

/*---------------------------------------------------------------------------
 * SBINIT DONE RESPONSE MESSAGE MONITORING IMPLEMENTATION
 * 
 * Monitors for SBINIT Done Response messages to complete the SBINIT
 * protocol sequence. Sets completion flag when Done Response received.
 *---------------------------------------------------------------------------*/
task ucie_sb_ltsm_model::monitor_done_response();
  ucie_sb_transaction received_trans;
  
  forever begin
    sb_agent.monitor.ap.get(received_trans);
    
    if (received_trans.opcode == MSG_VDM && 
        received_trans.msgcode == cfg.sbinit_done_rsp_msgcode) begin
      done_resp_received = 1;
      `uvm_info("LTSM_MODEL", "Received SBINIT Done Response message", UVM_MEDIUM)
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
        if (current_state != LTSM_TRAINING && current_state != LTSM_ERROR) begin
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
  cfg.set_fast_config(); // Default to fast configuration
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
  `uvm_info("LTSM_MODEL", $sformatf("Back-to-back detected: %0b", back_to_back_detected), UVM_LOW)
  `uvm_info("LTSM_MODEL", $sformatf("SBINIT OOR sent/received: %0b/%0b", oor_sent, oor_received), UVM_LOW)
  `uvm_info("LTSM_MODEL", $sformatf("SBINIT Done Req sent/received: %0b/%0b", done_req_sent, done_req_received), UVM_LOW)
  `uvm_info("LTSM_MODEL", $sformatf("SBINIT Done Resp sent/received: %0b/%0b", done_resp_sent, done_resp_received), UVM_LOW)
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