// UCIe Sideband UVM Loopback Environment
// Contains the testbench environment with 16 agents (15 passive, 1 active), 
// 8 register checkers, and 1 compare result model for loopback testing

class ucie_sb_env_loopback extends uvm_env;
  `uvm_component_utils(ucie_sb_env_loopback)
  
  // 16 agents (agent[1] active for compare model output, others passive)
  ucie_sb_agent agents[16];
  
  // 8 register checkers (each handles 2 agents)
  ucie_sb_reg_access_checker reg_checkers[8];
  
  // Compare result model for sideband TX/RX rewriting
  ucie_sb_compare_result_model compare_model;
  
  // Agent configurations
  ucie_sb_agent_config agent_cfgs[16];
  
  // Compare result model configuration
  ucie_sb_compare_result_config compare_cfg;
  
  function new(string name = "ucie_sb_env_loopback", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    string agent_name;
    
    super.build_phase(phase);
    
    // Each agent gets its own dedicated virtual interface set directly by testbench
    // No need to retrieve interfaces at environment level
    
    // Create and configure agents (agent[1] active for compare model output, others passive)
    for (int i = 0; i < 16; i++) begin
      agent_name = $sformatf("agent_%0d", i);
      
      // Create agent configuration
      agent_cfgs[i] = ucie_sb_agent_config::type_id::create($sformatf("agent_cfg_%0d", i));
      // Agent[1] is active to provide sequencer for compare model output
      agent_cfgs[i].is_active = (i == 1) ? UVM_ACTIVE : UVM_PASSIVE;
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
    
    // Create and configure compare result model
    compare_cfg = ucie_sb_compare_result_config::type_id::create("compare_cfg");
    compare_cfg.enable_model = 1;
    compare_cfg.enable_debug = 1;
    compare_cfg.enable_logging = 1;
    // Set default array initialization parameters
    compare_cfg.exp_volt_min = 10;
    compare_cfg.exp_volt_max = 20;
    compare_cfg.exp_clk_phase_min = 29;
    compare_cfg.exp_clk_phase_max = 33;
    // Set initial index selection parameters
    compare_cfg.volt_min = 12;
    compare_cfg.volt_max = 14;
    compare_cfg.clk_phase = 2;
    
    // Set compare model configuration in config database
    uvm_config_db#(ucie_sb_compare_result_config)::set(this, "compare_model", "cfg", compare_cfg);
    
    // Create compare result model
    compare_model = ucie_sb_compare_result_model::type_id::create("compare_model", this);
    `uvm_info("ENV", "Created compare result model", UVM_MEDIUM)
    
    `uvm_info("ENV", "Environment build phase completed", UVM_LOW)
    `uvm_info("ENV", $sformatf("Created %0d inactive agents with dedicated interfaces", 16), UVM_LOW)
    `uvm_info("ENV", $sformatf("Created %0d register checkers (2 agents per checker)", 8), UVM_LOW)
    `uvm_info("ENV", "Created compare result model for TX/RX rewriting", UVM_LOW)
  endfunction
  
  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    
    // Connect 16 agents to 8 register checkers in pairs
    // Pattern: agent(2*i) → checker[i].tx_fifo, agent(2*i+1) → checker[i].rx_fifo
    for (int i = 0; i < 8; i++) begin
      int agent_tx_idx = 2 * i;      // Even agents (0,2,4,6,8,10,12,14)
      int agent_rx_idx = 2 * i + 1;  // Odd agents (1,3,5,7,9,11,13,15)
      
      // Connect even agent's analysis port to TX FIFO
      agents[agent_tx_idx].ap.connect(reg_checkers[i].tx_fifo.analysis_export);
      `uvm_info("ENV", $sformatf("Agent[%0d].ap -> reg_checker_%0d.tx_fifo", agent_tx_idx, i), UVM_MEDIUM)
      
      // Connect odd agent's analysis port to RX FIFO
      agents[agent_rx_idx].ap.connect(reg_checkers[i].rx_fifo.analysis_export);
      `uvm_info("ENV", $sformatf("Agent[%0d].ap -> reg_checker_%0d.rx_fifo", agent_rx_idx, i), UVM_MEDIUM)
    end
    
    // Connect compare result model
    // Agent[0] monitors TX transactions, Agent[2] monitors RX transactions
    // Agent[1] provides active sequencer for compare model output
    agents[0].ap.connect(compare_model.tx_fifo.analysis_export);
    `uvm_info("ENV", "Agent[0].ap -> compare_model.tx_fifo (TX monitoring)", UVM_MEDIUM)
    
    agents[2].ap.connect(compare_model.rx_fifo.analysis_export);
    `uvm_info("ENV", "Agent[2].ap -> compare_model.rx_fifo (RX monitoring)", UVM_MEDIUM)
    
    // Connect compare model's rx_sequencer to active agent[1]'s sequencer
    compare_model.rx_sequencer = agents[1].sequencer;
    `uvm_info("ENV", "compare_model.rx_sequencer -> agents[1].sequencer (output path)", UVM_MEDIUM)
    
    `uvm_info("ENV", "=== Checker Connections Established ===", UVM_LOW)
    `uvm_info("ENV", $sformatf("Connected %0d agents to %0d checkers (2 agents per checker)", 16, 8), UVM_LOW)
    `uvm_info("ENV", "=== Compare Result Model Connected ===", UVM_LOW)
    `uvm_info("ENV", "TX Monitor: Agent[0] -> compare_model.tx_fifo", UVM_LOW)
    `uvm_info("ENV", "RX Monitor: Agent[2] -> compare_model.rx_fifo", UVM_LOW)
    `uvm_info("ENV", "Output Path: compare_model -> Agent[1].sequencer", UVM_LOW)
  endfunction
endclass