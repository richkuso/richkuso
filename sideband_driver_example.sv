// Example usage of the updated UCIe Sideband Driver
// Shows proper configuration and UCIe specification compliance

module sideband_driver_example;
  import uvm_pkg::*;
  import sideband_pkg::*;
  `include "uvm_macros.svh"
  
  // Test class demonstrating proper driver configuration
  class sideband_driver_test extends uvm_test;
    `uvm_component_utils(sideband_driver_test)
    
    sideband_agent agent;
    sideband_driver_config driver_cfg;
    
    function new(string name = "sideband_driver_test", uvm_component parent = null);
      super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      
      // Create and configure driver
      driver_cfg = sideband_driver_config::type_id::create("driver_cfg");
      
      // Configure clock timing (800MHz - UCIe sideband standard)
      driver_cfg.set_frequency(800e6);     // 800MHz
      driver_cfg.set_duty_cycle(50.0);     // 50% duty cycle
      
      // Configure protocol parameters
      driver_cfg.min_gap_cycles = 32;
      driver_cfg.enable_protocol_checking = 1;
      driver_cfg.enable_statistics = 1;
      
      // Configure timing parameters
      driver_cfg.setup_time = 0.1;         // 100ps setup time
      driver_cfg.hold_time = 0.1;          // 100ps hold time
      driver_cfg.gap_time = 0.0;           // No additional gap time
      
      // Set configuration in config_db
      uvm_config_db#(sideband_driver_config)::set(this, "agent.driver", "cfg", driver_cfg);
      
      // Create agent
      agent = sideband_agent::type_id::create("agent", this);
      uvm_config_db#(uvm_active_passive_enum)::set(this, "agent", "is_active", UVM_ACTIVE);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
      // Example sequences showing UCIe compliant transactions
      ucIe_compliant_sequence seq;
      
      phase.raise_objection(this);
      
      `uvm_info("TEST", "Starting UCIe compliant sideband test", UVM_LOW)
      
      seq = ucIe_compliant_sequence::type_id::create("seq");
      seq.start(agent.sequencer);
      
      #10000; // Let some time pass
      
      `uvm_info("TEST", "UCIe compliant sideband test completed", UVM_LOW)
      
      phase.drop_objection(this);
    endtask
  endclass
  
  // Example sequence with UCIe specification compliant transactions
  class ucIe_compliant_sequence extends sideband_base_sequence;
    `uvm_object_utils(ucIe_compliant_sequence)
    
    function new(string name = "ucIe_compliant_sequence");
      super.new(name);
    endfunction
    
    virtual task body();
      sideband_transaction trans;
      
      `uvm_info("SEQ", "Generating UCIe compliant transactions", UVM_MEDIUM)
      
      // Example 1: D2D Adapter to Remote Die Memory Write (32-bit)
      trans = sideband_transaction::type_id::create("d2d_mem_write");
      start_item(trans);
      assert(trans.randomize() with {
        opcode == MEM_WRITE_32B;
        srcid == 3'b001;     // D2D Adapter (Table 7-4)
        dstid == 3'b100;     // Remote die (dstid[2]=1, dstid[1:0]=00 reserved)
        addr[1:0] == 2'b00;  // 32-bit alignment
        be[7:4] == 4'b0000;  // Reserved for 32-bit
        tag inside {[1:30]};
        ep == 1'b0;          // No poison
        cr == 1'b0;          // No credit return
      });
      finish_item(trans);
      
      // Example 2: Physical Layer to Local Configuration Read (64-bit)
      trans = sideband_transaction::type_id::create("phy_cfg_read");
      start_item(trans);
      assert(trans.randomize() with {
        opcode == CFG_READ_64B;
        srcid == 3'b010;     // Physical Layer
        dstid == 3'b000;     // Local (dstid[2]=0)
        addr[2:0] == 3'b000; // 64-bit alignment
        tag inside {[1:30]};
        ep == 1'b0;
        cr == 1'b0;
      });
      finish_item(trans);
      
      // Example 3: Management Port Gateway Message with Data
      trans = sideband_transaction::type_id::create("mgmt_message");
      start_item(trans);
      assert(trans.randomize() with {
        opcode == MESSAGE_64B;
        srcid == 3'b011;     // Management Port Gateway
        dstid == 3'b111;     // Remote Management Port Gateway message
        tag inside {[1:30]};
        ep == 1'b0;
        cr == 1'b1;          // With credit return
        data != 64'h0;
      });
      finish_item(trans);
      
      // Example 4: Completion with 32-bit data to Remote D2D Adapter
      trans = sideband_transaction::type_id::create("completion_32b");
      start_item(trans);
      assert(trans.randomize() with {
        opcode == COMPLETION_32B;
        srcid == 3'b010;     // Physical Layer
        dstid == 3'b101;     // Remote D2D Adapter (dstid[2]=1, dstid[1:0]=01)
        tag inside {[1:30]};
        status == 16'h0000;  // Success
        ep == 1'b0;
        cr == 1'b0;
        data != 64'h0;
      });
      finish_item(trans);
      
      // Example 5: DMS Register Write with Error Poison
      trans = sideband_transaction::type_id::create("dms_write_poison");
      start_item(trans);
      assert(trans.randomize() with {
        opcode == DMS_WRITE_64B;
        srcid == 3'b001;     // D2D Adapter  
        dstid == 3'b000;     // Local
        addr[2:0] == 3'b000; // 64-bit alignment
        be == 8'hFF;         // All bytes enabled
        tag inside {[1:30]};
        ep == 1'b1;          // Error poison set
        cr == 1'b0;
        data != 64'h0;
      });
      finish_item(trans);
      
      `uvm_info("SEQ", "UCIe compliant transaction sequence completed", UVM_MEDIUM)
    endtask
  endclass
  
endmodule