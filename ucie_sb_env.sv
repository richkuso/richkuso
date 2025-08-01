// UCIe Sideband UVM Environment
// Contains the testbench environment with 16 inactive agents and checker

class ucie_sb_env extends uvm_env;
  `uvm_component_utils(ucie_sb_env)
  
  // 16 inactive agents for monitoring
  ucie_sb_agent agents[16];
  
  // 8 register checkers (each handles 2 agents)
  ucie_sb_reg_access_checker reg_checkers[8];
  
  // Agent configurations
  ucie_sb_agent_config agent_cfgs[16];
  
  function new(string name = "ucie_sb_env", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    string agent_name;
    
    super.build_phase(phase);
    
    // Each agent gets its own dedicated virtual interface set directly by testbench
    // No need to retrieve interfaces at environment level
    
    // Create and configure 16 inactive agents
    for (int i = 0; i < 16; i++) begin
      agent_name = $sformatf("agent_%0d", i);
      
      // Create agent configuration
      agent_cfgs[i] = ucie_sb_agent_config::type_id::create($sformatf("agent_cfg_%0d", i));
      agent_cfgs[i].is_active = UVM_PASSIVE;  // All agents are inactive (passive)
      // Note: Each agent gets its own dedicated vif from testbench (sb_intf[i]), no need to set here
      agent_cfgs[i].enable_coverage = 1;
      agent_cfgs[i].enable_protocol_checking = 1;
      agent_cfgs[i].enable_statistics = 1;
      
      // Set agent configuration in config database
      uvm_config_db#(ucie_sb_agent_config)::set(this, agent_name, "cfg", agent_cfgs[i]);
      
      // Create agent
      agents[i] = ucie_sb_agent::type_id::create(agent_name, this);
      
      `uvm_info("ENV", $sformatf("Created inactive agent[%0d]: %s", i, agent_name), UVM_MEDIUM)
    end
    
    // Create 8 register access checkers
    for (int j = 0; j < 8; j++) begin
      string checker_name = $sformatf("reg_checker_%0d", j);
      reg_checkers[j] = ucie_sb_reg_access_checker::type_id::create(checker_name, this);
      `uvm_info("ENV", $sformatf("Created register checker[%0d]: %s", j, checker_name), UVM_MEDIUM)
    end
    
    `uvm_info("ENV", "Environment build phase completed", UVM_LOW)
    `uvm_info("ENV", $sformatf("Created %0d inactive agents with dedicated interfaces", 16), UVM_LOW)
    `uvm_info("ENV", $sformatf("Created %0d register checkers (2 agents per checker)", 8), UVM_LOW)
  endfunction
  
  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    
    // Connect 16 agents to 8 register checkers in pairs
    // Pattern: agent(2*i) → checker[i].tx_fifo, agent(2*i+1) → checker[i].rx_fifo
    for (int i = 0; i < 8; i++) begin
      int agent_tx_idx = 2 * i;      // Even agents (0,2,4,6,8,10,12,14)
      int agent_rx_idx = 2 * i + 1;  // Odd agents (1,3,5,7,9,11,13,15)
      
      // Connect even agent to TX FIFO
      agents[agent_tx_idx].monitor.ap.connect(reg_checkers[i].tx_fifo.analysis_export);
      `uvm_info("ENV", $sformatf("Agent[%0d] Monitor → reg_checker_%0d.tx_fifo", agent_tx_idx, i), UVM_MEDIUM)
      
      // Connect odd agent to RX FIFO
      agents[agent_rx_idx].monitor.ap.connect(reg_checkers[i].rx_fifo.analysis_export);
      `uvm_info("ENV", $sformatf("Agent[%0d] Monitor → reg_checker_%0d.rx_fifo", agent_rx_idx, i), UVM_MEDIUM)
    end
    
    `uvm_info("ENV", "=== Checker Connections Established ===", UVM_LOW)
    `uvm_info("ENV", $sformatf("Connected %0d agents to %0d checkers (2 agents per checker)", 16, 8), UVM_LOW)
  endfunction
endclass