// UCIe Sideband Checker Validation Test
// Specifically tests checker functionality

class ucie_sb_checker_test extends ucie_sb_base_test;
  `uvm_component_utils(ucie_sb_checker_test)
  
  function new(string name = "ucie_sb_checker_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    ucie_sb_single_transaction_sequence single_seq;
    ucie_sb_transaction req_trans, comp_trans;
    
    phase.raise_objection(this);
    
    `uvm_info("CHECKER_TEST", "=== Starting Checker Validation Test ===", UVM_LOW)
    
    // Test TAG mode first
    `uvm_info("CHECKER_TEST", "--- Testing TAG Mode ---", UVM_LOW)
    env.reg_checker.enable_tag_support = 1;
    
    // Send a memory read request
    single_seq = ucie_sb_single_transaction_sequence::type_id::create("mem_read_req");
    req_trans = ucie_sb_transaction::type_id::create("req_trans");
    assert(req_trans.randomize() with {
      opcode == MEM_READ_32B;
      srcid == 3'h1;
      dstid == 3'h2;
      tag == 5'h05;
      addr == 24'h001000;
    });
    single_seq.trans = req_trans;
    single_seq.start(env.tx_agent.sequencer);
    
    #1000;
    
    // Send corresponding completion
    single_seq = ucie_sb_single_transaction_sequence::type_id::create("mem_read_comp");
    comp_trans = ucie_sb_transaction::type_id::create("comp_trans");
    assert(comp_trans.randomize() with {
      opcode == COMPLETION_32B;
      srcid == 3'h2; // Swapped for completion
      dstid == 3'h1;
      tag == 5'h05;   // Matching tag
      status == 16'h0000; // Success
      data == 64'hDEADBEEF_CAFEBABE;
    });
    single_seq.trans = comp_trans;
    single_seq.start(env.tx_agent.sequencer);
    
    #2000;
    
    // Test non-TAG mode
    `uvm_info("CHECKER_TEST", "--- Testing Non-TAG Mode ---", UVM_LOW)
    env.reg_checker.enable_tag_support = 0;
    
    // Send config write (no completion expected)
    single_seq = ucie_sb_single_transaction_sequence::type_id::create("cfg_write");
    req_trans = ucie_sb_transaction::type_id::create("cfg_write_trans");
    assert(req_trans.randomize() with {
      opcode == CFG_WRITE_32B;
      srcid == 3'h1;
      dstid == 3'h2;
      tag == 5'h00;    // Must be 0 in non-TAG mode
      addr == 24'h002000;
      data == 64'h12345678_9ABCDEF0;
    });
    single_seq.trans = req_trans;
    single_seq.start(env.tx_agent.sequencer);
    
    #3000;
    
    `uvm_info("CHECKER_TEST", "=== Checker Validation Test Completed ===", UVM_LOW)
    
    phase.drop_objection(this);
  endtask
endclass