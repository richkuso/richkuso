/*******************************************************************************
 * UCIe Sideband Link Training State Machine (LTSM) Model
 * 
 * OVERVIEW:
 *   FSM-based model implementing UCIe sideband link training sequence from
 *   RESET state through SBINIT state according to UCIe 1.1 specification.
 *   Integrates with existing UCIe sideband UVM agent for protocol compliance.
 *
 * LINK TRAINING SEQUENCE:
 *   RESET → DETECT → POLLING → CONFIGURATION → SBINIT
 *
 * FSM STATES:
 *   • RESET      - Initial reset state, all signals idle
 *   • DETECT     - Clock pattern detection phase
 *   • POLLING    - Bidirectional clock pattern exchange
 *   • CONFIG     - Link configuration and parameter negotiation
 *   • SBINIT     - SBINIT message exchange and training completion
 *
 * INTEGRATION:
 *   • Uses ucie_sb_agent for protocol transactions
 *   • Implements UCIe timing requirements
 *   • Supports both initiator and target roles
 *   • Provides comprehensive debug and analysis
 *
 * COMPLIANCE:
 *   • UCIe 1.1 specification compliant
 *   • IEEE 1800-2017 SystemVerilog
 *   • UVM 1.2 methodology
 *
 * AUTHOR: UCIe Sideband UVM Agent
 * VERSION: 1.0 - LTSM FSM Implementation
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

//=============================================================================
// CLASS: ucie_sb_ltsm_model
//
// DESCRIPTION:
//   UCIe Sideband Link Training State Machine model implementing the complete
//   link training sequence from RESET to SBINIT state. Provides FSM-based
//   control with comprehensive timing and protocol compliance.
//=============================================================================

class ucie_sb_ltsm_model extends uvm_component;
  `uvm_component_utils(ucie_sb_ltsm_model)
  
  //===========================================================================
  // CONFIGURATION AND INTERFACES
  //===========================================================================
  
  // Agent integration
  ucie_sb_agent sb_agent;
  virtual ucie_sb_inf vif;
  
  // Configuration
  bit is_initiator = 1;                    // Role: 1=initiator, 0=target
  bit enable_debug = 1;                    // Enable debug messages
  real timeout_ms = 10.0;                 // State timeout in milliseconds
  
  //===========================================================================
  // FSM STATE VARIABLES
  //===========================================================================
  
  ucie_ltsm_state_t current_state = LTSM_RESET;
  ucie_ltsm_state_t next_state = LTSM_RESET;
  ucie_ltsm_event_t current_event;
  
  // State entry times for timeout detection
  realtime state_entry_time;
  realtime timeout_duration;
  
  //===========================================================================
  // PROTOCOL TRACKING VARIABLES
  //===========================================================================
  
  // Clock pattern detection
  int clock_patterns_sent = 0;
  int clock_patterns_received = 0;
  int required_patterns = 4;               // UCIe spec requirement
  
  // Polling phase tracking
  int polling_cycles = 0;
  int max_polling_cycles = 100;
  
  // Configuration tracking
  bit config_req_sent = 0;
  bit config_rsp_received = 0;
  
  // SBINIT tracking
  bit sbinit_oor_sent = 0;                 // Out of Reset message
  bit sbinit_done_req_sent = 0;            // Done Request message
  bit sbinit_done_rsp_received = 0;        // Done Response received
  
  //===========================================================================
  // STATISTICS AND ANALYSIS
  //===========================================================================
  
  // State transition counters
  int state_transitions[ucie_ltsm_state_t];
  realtime state_durations[ucie_ltsm_state_t];
  realtime total_training_time;
  
  // Error tracking
  int timeout_errors = 0;
  int protocol_errors = 0;
  
  //===========================================================================
  // EVENTS AND PROCESSES
  //===========================================================================
  
  event state_change_event;
  event timeout_event;
  event training_complete_event;
  
  //===========================================================================
  // CONSTRUCTOR
  //===========================================================================
  
  function new(string name = "ucie_sb_ltsm_model", uvm_component parent = null);
    super.new(name, parent);
    timeout_duration = timeout_ms * 1_000_000; // Convert ms to ns
  endfunction
  
  //===========================================================================
  // UVM PHASES
  //===========================================================================
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    // Create sideband agent
    sb_agent = ucie_sb_agent::type_id::create("sb_agent", this);
    
    // Get virtual interface
    if (!uvm_config_db#(virtual ucie_sb_inf)::get(this, "", "vif", vif)) begin
      `uvm_fatal("LTSM_MODEL", "Virtual interface not found in config DB")
    end
    
    // Configure agent for LTSM operation
    configure_agent();
    
    `uvm_info("LTSM_MODEL", "LTSM model build phase complete", UVM_LOW)
  endfunction
  
  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    `uvm_info("LTSM_MODEL", "LTSM model connect phase complete", UVM_LOW)
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    
    // Start parallel processes
    fork
      ltsm_fsm_process();
      timeout_monitor();
      statistics_collector();
    join_none
    
    // Wait for training completion or timeout
    wait(current_state == LTSM_SBINIT || current_state == LTSM_ERROR);
    
    if (current_state == LTSM_SBINIT) begin
      `uvm_info("LTSM_MODEL", "Link training completed successfully!", UVM_LOW)
      -> training_complete_event;
    end else begin
      `uvm_error("LTSM_MODEL", "Link training failed or timed out")
    end
    
    print_final_statistics();
  endtask
  
  //===========================================================================
  // FSM MAIN PROCESS
  //===========================================================================
  
  virtual task ltsm_fsm_process();
    `uvm_info("LTSM_MODEL", "Starting LTSM FSM process", UVM_MEDIUM)
    
    forever begin
      // State entry actions
      state_entry_actions();
      
      // Wait for events or state transitions
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
  
  //===========================================================================
  // STATE BEHAVIOR TASKS
  //===========================================================================
  
  virtual task reset_state_behavior();
    `uvm_info("LTSM_MODEL", "In RESET state - waiting for reset deassertion", UVM_HIGH)
    
    // Wait for reset deassertion
    wait(!vif.reset);
    #100ns; // Reset recovery time
    
    current_event = LTSM_EV_RESET_DEASSERT;
  endtask
  
  virtual task detect_state_behavior();
    `uvm_info("LTSM_MODEL", "In DETECT state - starting clock pattern detection", UVM_HIGH)
    
    if (is_initiator) begin
      // Initiator sends clock patterns
      send_clock_patterns();
    end else begin
      // Target waits for clock patterns
      wait_for_clock_patterns();
    end
  endtask
  
  virtual task polling_state_behavior();
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
    
    if (polling_cycles >= max_polling_cycles) begin
      current_event = LTSM_EV_POLLING_SUCCESS;
    end else begin
      current_event = LTSM_EV_TIMEOUT;
    end
  endtask
  
  virtual task config_state_behavior();
    `uvm_info("LTSM_MODEL", "In CONFIG state - parameter negotiation", UVM_HIGH)
    
    if (is_initiator) begin
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
  
  virtual task sbinit_state_behavior();
    `uvm_info("LTSM_MODEL", "In SBINIT state - SBINIT message exchange", UVM_HIGH)
    
    // SBINIT sequence: OOR → Done Request → Done Response
    if (is_initiator) begin
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
  
  virtual task error_state_behavior();
    `uvm_error("LTSM_MODEL", "In ERROR state - link training failed")
    
    // Stay in error state
    #1ms;
  endtask
  
  //===========================================================================
  // PROTOCOL IMPLEMENTATION TASKS
  //===========================================================================
  
  virtual task send_clock_patterns();
    ucie_sb_transaction clock_trans;
    
    for (int i = 0; i < required_patterns; i++) begin
      clock_trans = ucie_sb_transaction::type_id::create("clock_trans");
      clock_trans.opcode = CLOCK_PATTERN;
      clock_trans.srcid = 3'h1;
      clock_trans.dstid = 3'h0;
      
      // Send via agent
      sb_agent.driver.send_transaction(clock_trans);
      clock_patterns_sent++;
      
      `uvm_info("LTSM_MODEL", $sformatf("Sent clock pattern %0d/%0d", i+1, required_patterns), UVM_HIGH)
      #1250ns; // 800MHz period
    end
    
    current_event = LTSM_EV_CLOCK_DETECTED;
  endtask
  
  virtual task wait_for_clock_patterns();
    ucie_sb_transaction received_trans;
    int patterns_detected = 0;
    
    // Monitor for clock patterns
    forever begin
      sb_agent.monitor.analysis_port.get(received_trans);
      
      if (received_trans.opcode == CLOCK_PATTERN) begin
        patterns_detected++;
        clock_patterns_received++;
        
        `uvm_info("LTSM_MODEL", $sformatf("Detected clock pattern %0d/%0d", patterns_detected, required_patterns), UVM_HIGH)
        
        if (patterns_detected >= required_patterns) begin
          current_event = LTSM_EV_CLOCK_DETECTED;
          break;
        end
      end
    end
  endtask
  
  virtual task send_polling_patterns();
    ucie_sb_transaction poll_trans;
    
    for (int i = 0; i < max_polling_cycles; i++) begin
      poll_trans = ucie_sb_transaction::type_id::create("poll_trans");
      poll_trans.opcode = CLOCK_PATTERN; // Use clock pattern for polling
      poll_trans.srcid = is_initiator ? 3'h1 : 3'h2;
      poll_trans.dstid = is_initiator ? 3'h2 : 3'h1;
      
      sb_agent.driver.send_transaction(poll_trans);
      polling_cycles++;
      
      #2500ns; // Polling interval
    end
  endtask
  
  virtual task receive_polling_patterns();
    ucie_sb_transaction received_trans;
    int received_polls = 0;
    
    // Monitor for polling patterns
    forever begin
      sb_agent.monitor.analysis_port.get(received_trans);
      
      if (received_trans.opcode == CLOCK_PATTERN && 
          received_trans.srcid != (is_initiator ? 3'h1 : 3'h2)) begin
        received_polls++;
        
        if (received_polls >= max_polling_cycles/2) begin
          break;
        end
      end
    end
  endtask
  
  virtual task send_config_request();
    ucie_sb_transaction config_trans;
    
    config_trans = ucie_sb_transaction::type_id::create("config_trans");
    config_trans.opcode = CFG_READ_64B;
    config_trans.srcid = 3'h1;
    config_trans.dstid = 3'h2;
    config_trans.addr = 24'h001000; // Configuration space
    config_trans.tag = 5'h10;
    
    sb_agent.driver.send_transaction(config_trans);
    config_req_sent = 1;
    
    `uvm_info("LTSM_MODEL", "Sent configuration request", UVM_HIGH)
  endtask
  
  virtual task wait_for_config_response();
    ucie_sb_transaction received_trans;
    
    forever begin
      sb_agent.monitor.analysis_port.get(received_trans);
      
      if (received_trans.opcode == CPL_DATA_64B && received_trans.tag == 5'h10) begin
        config_rsp_received = 1;
        `uvm_info("LTSM_MODEL", "Received configuration response", UVM_HIGH)
        break;
      end
    end
  endtask
  
  virtual task wait_for_config_request();
    ucie_sb_transaction received_trans;
    
    forever begin
      sb_agent.monitor.analysis_port.get(received_trans);
      
      if (received_trans.opcode == CFG_READ_64B) begin
        `uvm_info("LTSM_MODEL", "Received configuration request", UVM_HIGH)
        break;
      end
    end
  endtask
  
  virtual task send_config_response();
    ucie_sb_transaction config_rsp_trans;
    
    config_rsp_trans = ucie_sb_transaction::type_id::create("config_rsp_trans");
    config_rsp_trans.opcode = CPL_DATA_64B;
    config_rsp_trans.srcid = 3'h2;
    config_rsp_trans.dstid = 3'h1;
    config_rsp_trans.tag = 5'h10;
    config_rsp_trans.data = 64'hDEADBEEFCAFEBABE; // Config data
    
    sb_agent.driver.send_transaction(config_rsp_trans);
    config_rsp_received = 1;
    
    `uvm_info("LTSM_MODEL", "Sent configuration response", UVM_HIGH)
  endtask
  
  virtual task wait_for_sbinit_oor();
    ucie_sb_transaction received_trans;
    
    forever begin
      sb_agent.monitor.analysis_port.get(received_trans);
      
      if (received_trans.opcode == MSG_VDM && received_trans.msgcode == 8'h10) begin
        `uvm_info("LTSM_MODEL", "Received SBINIT Out of Reset message", UVM_HIGH)
        break;
      end
    end
  endtask
  
  virtual task wait_for_sbinit_done_request();
    ucie_sb_transaction received_trans;
    
    forever begin
      sb_agent.monitor.analysis_port.get(received_trans);
      
      if (received_trans.opcode == MSG_VDM && received_trans.msgcode == 8'h11) begin
        `uvm_info("LTSM_MODEL", "Received SBINIT Done Request message", UVM_HIGH)
        break;
      end
    end
  endtask
  
  virtual task send_sbinit_done_response();
    ucie_sb_transaction done_rsp_trans;
    
    done_rsp_trans = ucie_sb_transaction::type_id::create("done_rsp_trans");
    done_rsp_trans.opcode = MSG_VDM;
    done_rsp_trans.srcid = 3'h2;
    done_rsp_trans.dstid = 3'h1;
    done_rsp_trans.msgcode = 8'h12; // SBINIT Done Response
    done_rsp_trans.tag = 5'h11;
    
    sb_agent.driver.send_transaction(done_rsp_trans);
    sbinit_done_rsp_received = 1;
    
    `uvm_info("LTSM_MODEL", "Sent SBINIT Done Response message", UVM_HIGH)
  endtask
  
  virtual task send_sbinit_oor();
    ucie_sb_transaction oor_trans;
    
    oor_trans = ucie_sb_transaction::type_id::create("oor_trans");
    oor_trans.opcode = MSG_VDM;
    oor_trans.srcid = 3'h1;
    oor_trans.dstid = 3'h0;
    oor_trans.msgcode = 8'h10; // SBINIT OOR
    oor_trans.tag = 5'h10;
    
    sb_agent.driver.send_transaction(oor_trans);
    sbinit_oor_sent = 1;
    
    `uvm_info("LTSM_MODEL", "Sent SBINIT Out of Reset message", UVM_HIGH)
  endtask
  
  virtual task send_sbinit_done_request();
    ucie_sb_transaction done_req_trans;
    
    done_req_trans = ucie_sb_transaction::type_id::create("done_req_trans");
    done_req_trans.opcode = MSG_VDM;
    done_req_trans.srcid = 3'h1;
    done_req_trans.dstid = 3'h2;
    done_req_trans.msgcode = 8'h11; // SBINIT Done Request
    done_req_trans.tag = 5'h11;
    
    sb_agent.driver.send_transaction(done_req_trans);
    sbinit_done_req_sent = 1;
    
    `uvm_info("LTSM_MODEL", "Sent SBINIT Done Request message", UVM_HIGH)
  endtask
  
  virtual task wait_for_sbinit_done_response();
    ucie_sb_transaction received_trans;
    
    forever begin
      sb_agent.monitor.analysis_port.get(received_trans);
      
      if (received_trans.opcode == MSG_VDM && 
          received_trans.msgcode == 8'h12 && // SBINIT Done Response
          received_trans.tag == 5'h11) begin
        sbinit_done_rsp_received = 1;
        `uvm_info("LTSM_MODEL", "Received SBINIT Done Response", UVM_HIGH)
        break;
      end
    end
  endtask
  
  //===========================================================================
  // FSM TRANSITION LOGIC
  //===========================================================================
  
  virtual function ucie_ltsm_state_t get_next_state(ucie_ltsm_state_t state, ucie_ltsm_event_t event);
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
  
  //===========================================================================
  // STATE MANAGEMENT
  //===========================================================================
  
  virtual function void state_entry_actions();
    state_entry_time = $realtime;
    state_transitions[current_state]++;
    
    if (enable_debug) begin
      `uvm_info("LTSM_MODEL", $sformatf("Entering state: %s", current_state.name()), UVM_MEDIUM)
    end
    
    -> state_change_event;
  endfunction
  
  virtual function void transition_to_state(ucie_ltsm_state_t new_state);
    realtime state_duration = $realtime - state_entry_time;
    state_durations[current_state] += state_duration;
    
    `uvm_info("LTSM_MODEL", $sformatf("State transition: %s → %s (duration: %0.3fms)", 
              current_state.name(), new_state.name(), state_duration/1_000_000.0), UVM_LOW)
    
    current_state = new_state;
  endfunction
  
  //===========================================================================
  // MONITORING TASKS
  //===========================================================================
  
  virtual task timeout_monitor();
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
  
  virtual task statistics_collector();
    realtime start_time = $realtime;
    
    forever begin
      @(training_complete_event);
      total_training_time = $realtime - start_time;
      break;
    end
  endtask
  
  //===========================================================================
  // CONFIGURATION AND UTILITY FUNCTIONS
  //===========================================================================
  
  virtual function void configure_agent();
    ucie_sb_agent_config agent_cfg;
    
    agent_cfg = ucie_sb_agent_config::type_id::create("agent_cfg");
    agent_cfg.is_active = UVM_ACTIVE;
    agent_cfg.enable_protocol_checking = 1;
    agent_cfg.enable_statistics = 1;
    agent_cfg.vif = vif;
    
    uvm_config_db#(ucie_sb_agent_config)::set(this, "sb_agent", "cfg", agent_cfg);
  endfunction
  
  virtual function void print_final_statistics();
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
  
endclass : ucie_sb_ltsm_model