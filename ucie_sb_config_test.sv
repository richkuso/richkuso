// UCIe Sideband Configuration Test
// Tests configuration access without TAG support

class ucie_sb_config_test extends ucie_sb_base_test;
  `uvm_component_utils(ucie_sb_config_test)
  
  function new(string name = "ucie_sb_config_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    ucie_sb_register_access_sequence reg_seq;
    
    phase.raise_objection(this);
    
    `uvm_info("CONFIG_TEST", "=== Starting Config Access Test without TAG Support ===", UVM_LOW)
    
    // Configure checker for non-TAG mode (blocking behavior)
    env.reg_checker.enable_tag_support = 0;
    
    // Run configuration sequence (one at a time due to blocking)
    reg_seq = ucie_sb_register_access_sequence::type_id::create("reg_seq");
    assert(reg_seq.randomize() with {
      num_transactions == 4;
      enable_mem_read == 0;
      enable_mem_write == 0;
      enable_cfg_read == 1;
      enable_cfg_write == 1;
      enable_32bit == 1;
      enable_64bit == 0;
      force_tag_zero == 1; // Force TAG=0 for non-TAG mode
    });
    reg_seq.start(env.tx_agent.sequencer);
    
    #8000;
    
    `uvm_info("CONFIG_TEST", "=== Config Access Test Completed ===", UVM_LOW)
    
    phase.drop_objection(this);
  endtask
endclass