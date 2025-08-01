// UCIe Sideband UVM Environment
// Contains the testbench environment with agents and checker

class ucie_sb_env extends uvm_env;
  `uvm_component_utils(ucie_sb_env)
  
  ucie_sb_agent tx_agent;
  ucie_sb_agent rx_agent;
  ucie_sb_reg_access_checker reg_checker;
  
  function new(string name = "ucie_sb_env", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    // Create TX agent (active)
    tx_agent = ucie_sb_agent::type_id::create("tx_agent", this);
    
    // Create RX agent (passive monitor only)
    rx_agent = ucie_sb_agent::type_id::create("rx_agent", this);
    
    // Create register access checker
    reg_checker = ucie_sb_reg_access_checker::type_id::create("reg_checker", this);
    
    // Configure agents
    uvm_config_db#(uvm_active_passive_enum)::set(this, "tx_agent", "is_active", UVM_ACTIVE);
    uvm_config_db#(uvm_active_passive_enum)::set(this, "rx_agent", "is_active", UVM_PASSIVE);
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