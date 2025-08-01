// UCIe Sideband UVM Environment
// Contains the testbench environment with 16 inactive agents and checker

class ucie_sb_env extends uvm_env;
  `uvm_component_utils(ucie_sb_env)
  
  // 16 inactive agents for monitoring
  ucie_sb_agent agents[16];
  ucie_sb_reg_access_checker reg_checker;
  
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
    
    // Create register access checker
    reg_checker = ucie_sb_reg_access_checker::type_id::create("reg_checker", this);
    
    `uvm_info("ENV", "Environment build phase completed", UVM_LOW)
    `uvm_info("ENV", $sformatf("Created %0d inactive agents, each with dedicated interface", 16), UVM_LOW)
  endfunction
  
  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    
    // Connect all agent monitors to checker using FIFO-only architecture
    // Since all agents are passive (monitor-only), connect them to TX FIFO for monitoring
    for (int i = 0; i < 16; i++) begin
      agents[i].monitor.ap.connect(reg_checker.tx_fifo.analysis_export);
      `uvm_info("ENV", $sformatf("Agent[%0d] Monitor → reg_checker.tx_fifo", i), UVM_MEDIUM)
    end
    
    `uvm_info("ENV", "=== Checker Connections Established ===", UVM_LOW)
    `uvm_info("ENV", $sformatf("Connected %0d inactive agent monitors to checker", 16), UVM_LOW)
  endfunction
endclass