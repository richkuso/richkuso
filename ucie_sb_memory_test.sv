// UCIe Sideband Memory Test
// Tests memory access with TAG support

class ucie_sb_memory_test extends ucie_sb_base_test;
  `uvm_component_utils(ucie_sb_memory_test)
  
  function new(string name = "ucie_sb_memory_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    ucie_sb_register_access_sequence reg_seq;
    
    phase.raise_objection(this);
    
    `uvm_info("MEMORY_TEST", "=== Starting Memory Access Test with TAG Support ===", UVM_LOW)
    
    // Configure checker for TAG mode
    env.reg_checker.enable_tag_support = 1;
    
    // Run memory access sequence with various operations
    reg_seq = ucie_sb_register_access_sequence::type_id::create("reg_seq");
    assert(reg_seq.randomize() with {
      num_transactions == 8;
      enable_mem_read == 1;
      enable_mem_write == 1;
      enable_cfg_read == 1;
      enable_cfg_write == 1;
      enable_32bit == 1;
      enable_64bit == 1;
    });
    reg_seq.start(env.tx_agent.sequencer);
    
    #10000; // Allow time for all transactions
    
    `uvm_info("MEMORY_TEST", "=== Memory Access Test Completed ===", UVM_LOW)
    
    phase.drop_objection(this);
  endtask
endclass