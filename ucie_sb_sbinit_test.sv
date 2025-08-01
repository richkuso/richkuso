// UCIe Sideband SBINIT Test
// Tests SBINIT message functionality

class ucie_sb_sbinit_test extends ucie_sb_base_test;
  `uvm_component_utils(ucie_sb_sbinit_test)
  
  function new(string name = "ucie_sb_sbinit_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    ucie_sb_sbinit_sequence sbinit_seq;
    
    phase.raise_objection(this);
    
    `uvm_info("SBINIT_TEST", "=== Starting SBINIT Message Test ===", UVM_LOW)
    
    // Configure checker to ignore messages (focus on register access)
    env.reg_checker.enable_tag_support = 1;
    
    // Run SBINIT sequence
    sbinit_seq = ucie_sb_sbinit_sequence::type_id::create("sbinit_seq");
    assert(sbinit_seq.randomize() with {
      include_out_of_reset == 1;
      include_done_req == 1;
      include_done_resp == 1;
      num_repetitions == 2;
    });
    sbinit_seq.start(env.tx_agent.sequencer);
    
    #6000;
    
    `uvm_info("SBINIT_TEST", "=== SBINIT Message Test Completed ===", UVM_LOW)
    
    phase.drop_objection(this);
  endtask
endclass