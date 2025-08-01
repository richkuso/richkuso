// UCIe Sideband UVM Environment
// Contains the testbench environment with agents and checker

class ucie_sb_env extends uvm_env;
  `uvm_component_utils(ucie_sb_env)
  
  ucie_sb_agent tx_agent;
  ucie_sb_agent rx_agent;
  ucie_sb_reg_access_checker reg_checker;
  
  // Agent configurations
  ucie_sb_agent_config tx_agent_cfg;
  ucie_sb_agent_config rx_agent_cfg;
  
  function new(string name = "ucie_sb_env", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    virtual ucie_sb_interface vif;
    
    super.build_phase(phase);
    
    // Get the virtual interface from config database
    if (!uvm_config_db#(virtual ucie_sb_interface)::get(this, "", "vif", vif)) begin
      `uvm_fatal("ENV", "Virtual interface not found in config database")
    end
    
    // Create and configure TX agent (active)
    tx_agent_cfg = ucie_sb_agent_config::type_id::create("tx_agent_cfg");
    tx_agent_cfg.is_active = UVM_ACTIVE;
    tx_agent_cfg.vif = vif;
    tx_agent_cfg.enable_coverage = 1;
    tx_agent_cfg.enable_protocol_checking = 1;
    tx_agent_cfg.enable_statistics = 1;
    uvm_config_db#(ucie_sb_agent_config)::set(this, "tx_agent", "cfg", tx_agent_cfg);
    tx_agent = ucie_sb_agent::type_id::create("tx_agent", this);
    
    // Create and configure RX agent (passive monitor only)
    rx_agent_cfg = ucie_sb_agent_config::type_id::create("rx_agent_cfg");
    rx_agent_cfg.is_active = UVM_PASSIVE;
    rx_agent_cfg.vif = vif;
    rx_agent_cfg.enable_coverage = 1;
    rx_agent_cfg.enable_protocol_checking = 1;
    rx_agent_cfg.enable_statistics = 1;
    uvm_config_db#(ucie_sb_agent_config)::set(this, "rx_agent", "cfg", rx_agent_cfg);
    rx_agent = ucie_sb_agent::type_id::create("rx_agent", this);
    
    // Create register access checker
    reg_checker = ucie_sb_reg_access_checker::type_id::create("reg_checker", this);
    
    `uvm_info("ENV", "Environment build phase completed", UVM_LOW)
    `uvm_info("ENV", $sformatf("TX Agent: %s, RX Agent: %s", 
              tx_agent_cfg.is_active.name(), rx_agent_cfg.is_active.name()), UVM_LOW)
  endfunction
  
  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    
    // Connect agents to checker using FIFO-only architecture
    tx_agent.monitor.ap.connect(reg_checker.tx_fifo.analysis_export);
    rx_agent.monitor.ap.connect(reg_checker.rx_fifo.analysis_export);
    
    `uvm_info("ENV", "=== Checker Connections Established ===", UVM_LOW)
    `uvm_info("ENV", "TX Agent Monitor → reg_checker.tx_fifo", UVM_LOW)
    `uvm_info("ENV", "RX Agent Monitor → reg_checker.rx_fifo", UVM_LOW)
  endfunction
endclass