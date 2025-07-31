// UCIe Sideband Model (UVM Component)
// Implements sideband initial flow and acts as DUT's link parameter training engine

//=============================================================================
// CLASS: ucie_sb_model
//
// DESCRIPTION:
//   UVM component that implements the UCIe sideband initial flow and acts as
//   a training engine for link parameter training via register access.
//   
//   Sideband Initial Flow Implementation:
//   1. Send continuous clock pattern on TX driver
//   2. Detect two back-to-back clock patterns on RX monitor
//   3. Stop clock pattern after 4 more patterns when detected
//   4. Send SBINIT Out of Reset (Result=4'h1) until detected or 8ms timeout
//   5. Stop SBINIT Out of Reset when detected on RX
//   6. Send SBINIT done req and wait for SBINIT done rsp
//   7. Respond to SBINIT done req with SBINIT done rsp
//   8. Initial flow complete when both req/rsp exchanged
//
// AUTHOR: UCIe Sideband UVM Agent
// VERSION: 1.0 - Sideband Initial Flow Model
//=============================================================================

class ucie_sb_model extends uvm_component;
  `uvm_component_utils(ucie_sb_model)
  
  //=============================================================================
  // CLASS FIELDS
  //=============================================================================
  
  // Virtual interface
  virtual ucie_sb_interface vif;
  
  // Sideband agent
  ucie_sb_agent sb_agent;
  
  // Configuration
  ucie_sb_config cfg;
  
  // TLM FIFO for communication
  uvm_tlm_analysis_fifo #(ucie_sb_transaction) rx_fifo;
  
  // Control and status
  bit enable_initial_flow = 1;
  bit initial_flow_active = 0;
  bit initial_flow_complete = 0;
  bit initial_flow_timeout = 0;
  bit initial_flow_error = 0;
  
  //=============================================================================
  // SIDEBAND INITIAL FLOW STATES
  //=============================================================================
  
  typedef enum {
    IDLE,
    SEND_CLOCK_PATTERN,
    CLOCK_PATTERN_FOUND,
    SEND_SBINIT_OOR,
    SEND_SBINIT_DONE_REQ,
    WAIT_SBINIT_DONE_RSP,
    SEND_SBINIT_DONE_RSP,
    INITIAL_FLOW_DONE,
    TIMEOUT_ERROR,
    PROTOCOL_ERROR
  } sb_init_state_t;
  
  sb_init_state_t current_state = IDLE;
  string state_name = "IDLE";
  
  // Internal counters and flags
  int clock_pattern_count = 0;
  bit two_clock_patterns_detected = 0;
  bit sbinit_oor_received = 0;
  bit sbinit_done_req_received = 0;
  bit sbinit_done_rsp_received = 0;
  bit sbinit_done_req_sent = 0;
  bit sbinit_done_rsp_sent = 0;
  
  // Timing
  time start_time;
  time current_time;
  
  // Events
  event sbinit_oor_received_event;
  event sbinit_done_req_received_event;
  event sbinit_done_rsp_received_event;
  event timeout_event;
  
  //=============================================================================
  // CONSTRUCTOR
  //=============================================================================
  
  function new(string name = "ucie_sb_model", uvm_component parent = null);
    super.new(name, parent);
    
    // Create FIFO
    rx_fifo = new("rx_fifo", this);
  endfunction
  
  //=============================================================================
  // UVM PHASES
  //=============================================================================
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    // Get configuration
    if (!uvm_config_db#(ucie_sb_config)::get(this, "", "cfg", cfg)) begin
      `uvm_fatal("NOCFG", "Configuration not found")
    end
    
    // Get virtual interface
    if (!uvm_config_db#(virtual ucie_sb_interface)::get(this, "", "vif", vif)) begin
      `uvm_fatal("NOVIF", "Virtual interface not found")
    end
    
    // Create sideband agent
    sb_agent = ucie_sb_agent::type_id::create("sb_agent", this);
    
    // Configure agent - create agent config from model config
    ucie_sb_agent_config agent_cfg = ucie_sb_agent_config::type_id::create("agent_cfg");
    agent_cfg.is_active = UVM_ACTIVE;
    agent_cfg.vif = vif;
    agent_cfg.driver_cfg = ucie_sb_driver_config::type_id::create("driver_cfg");
    agent_cfg.driver_cfg.set_frequency(800e6); // 800MHz default
    
    // Set agent configuration
    uvm_config_db#(ucie_sb_agent_config)::set(this, "sb_agent", "cfg", agent_cfg);
    
    `uvm_info("SB_MODEL", "Sideband model built", UVM_LOW)
  endfunction
  
  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    
    // Connect agent monitor to FIFO
    sb_agent.ap.connect(rx_fifo.analysis_export);
    
    `uvm_info("SB_MODEL", "Sideband model connected", UVM_LOW)
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    
    fork
      // Main initial flow process
      initial_flow_process();
      
      // RX message monitoring
      rx_message_monitor();
      
      // Timeout monitoring
      timeout_monitor();
      
    join_none
    
    `uvm_info("SB_MODEL", "Sideband model run phase started", UVM_LOW)
  endtask
  
  //=============================================================================
  // INITIAL FLOW PROCESS
  //=============================================================================
  
  virtual task initial_flow_process();
    if (!enable_initial_flow) return;
    
    `uvm_info("SB_MODEL", "Starting sideband initial flow", UVM_MEDIUM)
    initial_flow_active = 1;
    start_time = $time;
    
    // State machine for initial flow
    current_state = SEND_CLOCK_PATTERN;
    update_state_name();
    
    while (current_state != INITIAL_FLOW_DONE && 
           current_state != TIMEOUT_ERROR && 
           current_state != PROTOCOL_ERROR) begin
      
      case (current_state)
        SEND_CLOCK_PATTERN: begin
          send_clock_pattern_task();
        end
        
        CLOCK_PATTERN_FOUND: begin
          send_remaining_clock_patterns_task();
        end
        
        SEND_SBINIT_OOR: begin
          send_sbinit_oor_task();
        end
        
        SEND_SBINIT_DONE_REQ: begin
          send_sbinit_done_req_task();
        end
        
        WAIT_SBINIT_DONE_RSP: begin
          wait_sbinit_done_rsp_task();
        end
        
        SEND_SBINIT_DONE_RSP: begin
          send_sbinit_done_rsp_task();
        end
        
        default: begin
          `uvm_error("SB_MODEL", $sformatf("Unknown state: %s", current_state.name()))
          current_state = PROTOCOL_ERROR;
        end
      endcase
      
      // Small delay between state processing
      #1ns;
    end
    
    // Final state processing
    if (current_state == INITIAL_FLOW_DONE) begin
      initial_flow_complete = 1;
      `uvm_info("SB_MODEL", "Sideband initial flow completed successfully", UVM_LOW)
    end else if (current_state == TIMEOUT_ERROR) begin
      initial_flow_timeout = 1;
      `uvm_error("SB_MODEL", "Sideband initial flow timed out")
    end else if (current_state == PROTOCOL_ERROR) begin
      initial_flow_error = 1;
      `uvm_error("SB_MODEL", "Sideband initial flow protocol error")
    end
    
    initial_flow_active = 0;
  endtask
  
  //=============================================================================
  // STATE TASKS
  //=============================================================================
  
  virtual task send_clock_pattern_task();
    ucie_sb_transaction clock_pattern_trans;
    
    `uvm_info("SB_MODEL", "Sending clock pattern continuously", UVM_MEDIUM)
    
    fork
      begin
        // Send clock patterns continuously
        while (current_state == SEND_CLOCK_PATTERN) begin
          clock_pattern_trans = create_clock_pattern_transaction();
          send_transaction(clock_pattern_trans);
          #(cfg.clock_pattern_period * 1ns);
        end
      end
      
      begin
        // Wait for two back-to-back patterns detected
        wait (two_clock_patterns_detected);
        current_state = CLOCK_PATTERN_FOUND;
        update_state_name();
        `uvm_info("SB_MODEL", "Two clock patterns detected, transitioning to CLOCK_PATTERN_FOUND", UVM_MEDIUM)
      end
      
      begin
        // Timeout check
        wait (timeout_event.triggered);
        current_state = TIMEOUT_ERROR;
        update_state_name();
      end
    join_any
    disable fork;
  endtask
  
  virtual task send_remaining_clock_patterns_task();
    ucie_sb_transaction clock_pattern_trans;
    
    `uvm_info("SB_MODEL", $sformatf("Sending %0d remaining clock patterns", cfg.remaining_clock_patterns), UVM_MEDIUM)
    
    for (int i = 0; i < cfg.remaining_clock_patterns; i++) begin
      clock_pattern_trans = create_clock_pattern_transaction();
      send_transaction(clock_pattern_trans);
      #(cfg.clock_pattern_period * 1ns);
    end
    
    current_state = SEND_SBINIT_OOR;
    update_state_name();
    `uvm_info("SB_MODEL", "Finished sending remaining clock patterns, transitioning to SEND_SBINIT_OOR", UVM_MEDIUM)
  endtask
  
  virtual task send_sbinit_oor_task();
    ucie_sb_transaction sbinit_oor_trans;
    
    `uvm_info("SB_MODEL", "Sending SBINIT Out of Reset messages", UVM_MEDIUM)
    
    fork
      begin
        // Send SBINIT Out of Reset continuously
        while (current_state == SEND_SBINIT_OOR) begin
          sbinit_oor_trans = create_sbinit_oor_transaction();
          send_transaction(sbinit_oor_trans);
          #(cfg.sbinit_message_period * 1ns);
        end
      end
      
      begin
        // Wait for SBINIT Out of Reset received
        wait (sbinit_oor_received_event.triggered);
        current_state = SEND_SBINIT_DONE_REQ;
        update_state_name();
        `uvm_info("SB_MODEL", "SBINIT Out of Reset received, transitioning to SEND_SBINIT_DONE_REQ", UVM_MEDIUM)
      end
      
      begin
        // Timeout check
        wait (timeout_event.triggered);
        current_state = TIMEOUT_ERROR;
        update_state_name();
      end
    join_any
    disable fork;
  endtask
  
  virtual task send_sbinit_done_req_task();
    ucie_sb_transaction sbinit_done_req_trans;
    
    `uvm_info("SB_MODEL", "Sending SBINIT Done Request", UVM_MEDIUM)
    
    sbinit_done_req_trans = create_sbinit_done_req_transaction();
    send_transaction(sbinit_done_req_trans);
    sbinit_done_req_sent = 1;
    
    current_state = WAIT_SBINIT_DONE_RSP;
    update_state_name();
  endtask
  
  virtual task wait_sbinit_done_rsp_task();
    `uvm_info("SB_MODEL", "Waiting for SBINIT Done Response", UVM_MEDIUM)
    
    fork
      begin
        // Wait for SBINIT Done Response
        wait (sbinit_done_rsp_received_event.triggered);
        if (sbinit_done_req_sent && sbinit_done_rsp_sent) begin
          current_state = INITIAL_FLOW_DONE;
        end else begin
          // Still need to send response if we received a request
          current_state = SEND_SBINIT_DONE_RSP;
        end
        update_state_name();
      end
      
      begin
        // Wait for SBINIT Done Request (to respond to)
        wait (sbinit_done_req_received_event.triggered);
        current_state = SEND_SBINIT_DONE_RSP;
        update_state_name();
      end
      
      begin
        // Timeout check
        wait (timeout_event.triggered);
        current_state = TIMEOUT_ERROR;
        update_state_name();
      end
    join_any
    disable fork;
  endtask
  
  virtual task send_sbinit_done_rsp_task();
    ucie_sb_transaction sbinit_done_rsp_trans;
    
    `uvm_info("SB_MODEL", "Sending SBINIT Done Response", UVM_MEDIUM)
    
    sbinit_done_rsp_trans = create_sbinit_done_rsp_transaction();
    send_transaction(sbinit_done_rsp_trans);
    sbinit_done_rsp_sent = 1;
    
    // Check if we've completed the handshake
    if (sbinit_done_req_sent && sbinit_done_rsp_received) begin
      current_state = INITIAL_FLOW_DONE;
    end else begin
      current_state = WAIT_SBINIT_DONE_RSP;
    end
    update_state_name();
  endtask
  
  //=============================================================================
  // RX MESSAGE MONITORING
  //=============================================================================
  
  virtual task rx_message_monitor();
    ucie_sb_transaction rx_trans;
    
    forever begin
      rx_fifo.get(rx_trans);
      
      case (rx_trans.opcode)
        // Clock pattern detection
        MEM_READ_32B, MEM_WRITE_32B: begin
          if (is_clock_pattern(rx_trans)) begin
            clock_pattern_count++;
            `uvm_info("SB_MODEL", $sformatf("Clock pattern detected (count=%0d)", clock_pattern_count), UVM_HIGH)
            
            if (clock_pattern_count >= cfg.required_pattern_detections) begin
              two_clock_patterns_detected = 1;
            end
          end
        end
        
        // SBINIT messages (assuming specific opcodes for SBINIT messages)
        default: begin
          if (is_sbinit_oor_message(rx_trans)) begin
            sbinit_oor_received = 1;
            ->sbinit_oor_received_event;
            `uvm_info("SB_MODEL", "SBINIT Out of Reset message received", UVM_MEDIUM)
          end
          else if (is_sbinit_done_req_message(rx_trans)) begin
            sbinit_done_req_received = 1;
            ->sbinit_done_req_received_event;
            `uvm_info("SB_MODEL", "SBINIT Done Request message received", UVM_MEDIUM)
          end
          else if (is_sbinit_done_rsp_message(rx_trans)) begin
            sbinit_done_rsp_received = 1;
            ->sbinit_done_rsp_received_event;
            `uvm_info("SB_MODEL", "SBINIT Done Response message received", UVM_MEDIUM)
          end
        end
      endcase
    end
  endtask
  
  //=============================================================================
  // TIMEOUT MONITORING
  //=============================================================================
  
  virtual task timeout_monitor();
    forever begin
      #(cfg.timeout_8ms * 1ns);
      current_time = $time;
      if ((current_time - start_time) >= (cfg.timeout_8ms * 1ns)) begin
        if (current_state == SEND_CLOCK_PATTERN || current_state == SEND_SBINIT_OOR) begin
          `uvm_warning("SB_MODEL", $sformatf("Timeout in state %s", state_name))
          ->timeout_event;
        end
      end
    end
  endtask
  
  //=============================================================================
  // TRANSACTION SENDING
  //=============================================================================
  
  virtual task send_transaction(ucie_sb_transaction trans);
    // Send transaction through the agent's sequencer
    if (sb_agent != null && sb_agent.sequencer != null) begin
      sb_agent.sequencer.execute_item(trans);
    end else begin
      `uvm_error("SB_MODEL", "Agent or sequencer not available for transaction sending")
    end
  endtask
  
  //=============================================================================
  // TRANSACTION CREATION FUNCTIONS
  //=============================================================================
  
  virtual function ucie_sb_transaction create_clock_pattern_transaction();
    ucie_sb_transaction trans = ucie_sb_transaction::type_id::create("clock_pattern_trans");
    
    // Create alternating pattern for clock pattern
    trans.pkt_type = PKT_REG_ACCESS;
    trans.opcode = MEM_READ_32B;
    trans.srcid = cfg.srcid;
    trans.dstid = cfg.dstid;
    trans.tag = 5'h0;
    trans.addr = 24'hAAAAAA; // Alternating pattern
    trans.data = 32'h55555555; // Alternating pattern
    
    return trans;
  endfunction
  
  virtual function ucie_sb_transaction create_sbinit_oor_transaction();
    ucie_sb_transaction trans = ucie_sb_transaction::type_id::create("sbinit_oor_trans");
    
    // SBINIT Out of Reset message with Result=4'h1
    trans.pkt_type = PKT_REG_ACCESS;
    trans.opcode = CFG_WRITE_32B; // Using CFG write for SBINIT messages
    trans.srcid = cfg.srcid;
    trans.dstid = cfg.dstid;
    trans.tag = 5'h10; // Special tag for SBINIT OOR
    trans.addr = 24'h000010; // SBINIT OOR message type
    trans.data = 32'h00000001; // Result = 4'h1
    
    return trans;
  endfunction
  
  virtual function ucie_sb_transaction create_sbinit_done_req_transaction();
    ucie_sb_transaction trans = ucie_sb_transaction::type_id::create("sbinit_done_req_trans");
    
    trans.pkt_type = PKT_REG_ACCESS;
    trans.opcode = CFG_WRITE_32B;
    trans.srcid = cfg.srcid;
    trans.dstid = cfg.dstid;
    trans.tag = 5'h11; // Special tag for SBINIT Done Req
    trans.addr = 24'h000011; // SBINIT Done Req message type
    trans.data = 32'h00000000; // No specific result for req
    
    return trans;
  endfunction
  
  virtual function ucie_sb_transaction create_sbinit_done_rsp_transaction();
    ucie_sb_transaction trans = ucie_sb_transaction::type_id::create("sbinit_done_rsp_trans");
    
    trans.pkt_type = PKT_REG_ACCESS;
    trans.opcode = CFG_WRITE_32B;
    trans.srcid = cfg.srcid;
    trans.dstid = cfg.dstid;
    trans.tag = 5'h12; // Special tag for SBINIT Done Rsp
    trans.addr = 24'h000012; // SBINIT Done Rsp message type
    trans.data = 32'h00000000; // No specific result for rsp
    
    return trans;
  endfunction
  
  //=============================================================================
  // MESSAGE DETECTION FUNCTIONS
  //=============================================================================
  
  virtual function bit is_clock_pattern(ucie_sb_transaction trans);
    // Simple clock pattern detection based on alternating data pattern
    return (trans.addr == 24'hAAAAAA && trans.data == 32'h55555555);
  endfunction
  
  virtual function bit is_sbinit_oor_message(ucie_sb_transaction trans);
    return (trans.tag == 5'h10 && trans.addr == 24'h000010);
  endfunction
  
  virtual function bit is_sbinit_done_req_message(ucie_sb_transaction trans);
    return (trans.tag == 5'h11 && trans.addr == 24'h000011);
  endfunction
  
  virtual function bit is_sbinit_done_rsp_message(ucie_sb_transaction trans);
    return (trans.tag == 5'h12 && trans.addr == 24'h000012);
  endfunction
  
  //=============================================================================
  // UTILITY FUNCTIONS
  //=============================================================================
  
  virtual function void update_state_name();
    state_name = current_state.name();
    `uvm_info("SB_MODEL", $sformatf("State transition to: %s", state_name), UVM_HIGH)
  endfunction
  
  virtual function string get_status();
    return $sformatf("State:%s Active:%0b Complete:%0b Timeout:%0b Error:%0b", 
                     state_name, initial_flow_active, initial_flow_complete, 
                     initial_flow_timeout, initial_flow_error);
  endfunction
  
  virtual function void reset_initial_flow();
    current_state = IDLE;
    state_name = "IDLE";
    initial_flow_active = 0;
    initial_flow_complete = 0;
    initial_flow_timeout = 0;
    initial_flow_error = 0;
    clock_pattern_count = 0;
    two_clock_patterns_detected = 0;
    sbinit_oor_received = 0;
    sbinit_done_req_received = 0;
    sbinit_done_rsp_received = 0;
    sbinit_done_req_sent = 0;
    sbinit_done_rsp_sent = 0;
    
    `uvm_info("SB_MODEL", "Initial flow reset", UVM_MEDIUM)
  endfunction
  
  //=============================================================================
  // PUBLIC API
  //=============================================================================
  
  virtual function void start_initial_flow();
    if (!initial_flow_active) begin
      reset_initial_flow();
      enable_initial_flow = 1;
      `uvm_info("SB_MODEL", "Starting initial flow", UVM_LOW)
    end else begin
      `uvm_warning("SB_MODEL", "Initial flow already active")
    end
  endfunction
  
  virtual function void stop_initial_flow();
    enable_initial_flow = 0;
    `uvm_info("SB_MODEL", "Stopping initial flow", UVM_LOW)
  endfunction

endclass : ucie_sb_model