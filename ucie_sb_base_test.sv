// UCIe Sideband Base Test Class
// Base class for all UCIe sideband tests

class ucie_sb_base_test extends uvm_test;
  `uvm_component_utils(ucie_sb_base_test)
  
  ucie_sb_env sb_env;
  ucie_sb_config cfg;
  
  function new(string name = "ucie_sb_base_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    // Create configuration
    cfg = ucie_sb_config::type_id::create("cfg");
    assert(cfg.randomize() with {
      srcid == 3'h1;
      dstid == 3'h2;
      enable_initial_flow == 1;
    });
    
    // Create environment
    sb_env = ucie_sb_env::type_id::create("sb_env", this);
    
    // Set configuration in database
    uvm_config_db#(ucie_sb_config)::set(this, "*", "cfg", cfg);
    
    // Note: Virtual interface is set by the testbench module
    // uvm_config_db#(virtual ucie_sb_inf)::set(null, "*", "vif", sb_intf);
  endfunction
  
  virtual function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    uvm_top.print_topology();
  endfunction
endclass