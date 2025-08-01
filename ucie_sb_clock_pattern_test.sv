// UCIe Sideband Clock Pattern Test
// Tests clock pattern functionality

class ucie_sb_clock_pattern_test extends ucie_sb_base_test;
  `uvm_component_utils(ucie_sb_clock_pattern_test)
  
  function new(string name = "ucie_sb_clock_pattern_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    ucie_sb_clock_pattern_sequence clk_seq;
    
    phase.raise_objection(this);
    
    `uvm_info("CLOCK_PATTERN_TEST", "=== Starting Clock Pattern Test ===", UVM_LOW)
    
    // Configure checker for non-TAG mode (clock patterns don't use tags)
    env.reg_checker.enable_tag_support = 0;
    
    // Run clock pattern sequence
    clk_seq = ucie_sb_clock_pattern_sequence::type_id::create("clk_seq");
    assert(clk_seq.randomize() with {
      num_patterns == 10;
    });
    clk_seq.start(env.tx_agent.sequencer);
    
    #5000; // Allow time for patterns to complete
    
    `uvm_info("CLOCK_PATTERN_TEST", "=== Clock Pattern Test Completed ===", UVM_LOW)
    
    phase.drop_objection(this);
  endtask
endclass