// UCIe Sideband Mixed Traffic Test
// Tests comprehensive mixed traffic scenarios

class ucie_sb_mixed_test extends ucie_sb_base_test;
  `uvm_component_utils(ucie_sb_mixed_test)
  
  function new(string name = "ucie_sb_mixed_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    ucie_sb_base_sequence sequences[];
    
    phase.raise_objection(this);
    
    `uvm_info("MIXED_TEST", "=== Starting Comprehensive Mixed Traffic Test ===", UVM_LOW)
    
    // Configure checker for TAG mode
    env.reg_checker.enable_tag_support = 1;
    
    // Create array of different sequences
    sequences = new[5];
    sequences[0] = ucie_sb_clock_pattern_sequence::type_id::create("clk_pattern");
    sequences[1] = ucie_sb_register_access_sequence::type_id::create("reg_32bit");
    sequences[2] = ucie_sb_register_access_sequence::type_id::create("reg_64bit");
    sequences[3] = ucie_sb_sbinit_sequence::type_id::create("sbinit_msgs");
    sequences[4] = ucie_sb_register_access_sequence::type_id::create("mixed_reg");
    
    // Configure clock pattern sequence
    assert(sequences[0].randomize() with {
      ucie_sb_clock_pattern_sequence::num_patterns == 5;
    });
    
    // Configure 32-bit register sequence
    assert(sequences[1].randomize() with {
      ucie_sb_register_access_sequence::num_transactions == 4;
      ucie_sb_register_access_sequence::enable_32bit == 1;
      ucie_sb_register_access_sequence::enable_64bit == 0;
    });
    
    // Configure 64-bit register sequence
    assert(sequences[2].randomize() with {
      ucie_sb_register_access_sequence::num_transactions == 3;
      ucie_sb_register_access_sequence::enable_32bit == 0;
      ucie_sb_register_access_sequence::enable_64bit == 1;
    });
    
    // Configure SBINIT sequence
    assert(sequences[3].randomize() with {
      ucie_sb_sbinit_sequence::include_out_of_reset == 1;
      ucie_sb_sbinit_sequence::include_done_req == 1;
      ucie_sb_sbinit_sequence::num_repetitions == 1;
    });
    
    // Configure mixed register sequence
    assert(sequences[4].randomize() with {
      ucie_sb_register_access_sequence::num_transactions == 6;
      ucie_sb_register_access_sequence::enable_mem_read == 1;
      ucie_sb_register_access_sequence::enable_cfg_write == 1;
    });
    
    // Run sequences with gaps
    foreach(sequences[i]) begin
      `uvm_info("MIXED_TEST", $sformatf("Running sequence %0d: %s", i, sequences[i].get_name()), UVM_MEDIUM)
      sequences[i].start(env.tx_agent.sequencer);
      #2000; // Gap between different sequence types
    end
    
    #5000; // Final settling time
    
    `uvm_info("MIXED_TEST", "=== Mixed Traffic Test Completed ===", UVM_LOW)
    
    phase.drop_objection(this);
  endtask
endclass