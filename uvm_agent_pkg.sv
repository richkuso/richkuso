package uvm_agent_pkg;
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  
  // Transaction item
  class my_transaction extends uvm_sequence_item;
    // Transaction fields
    rand bit [31:0] data;
    rand bit [7:0]  addr;
    rand bit        read_write; // 1 for write, 0 for read
    bit             valid;
    
    // UVM automation macros
    `uvm_object_utils_begin(my_transaction)
      `uvm_field_int(data, UVM_ALL_ON)
      `uvm_field_int(addr, UVM_ALL_ON)
      `uvm_field_int(read_write, UVM_ALL_ON)
      `uvm_field_int(valid, UVM_ALL_ON)
    `uvm_object_utils_end
    
    // Constructor
    function new(string name = "my_transaction");
      super.new(name);
    endfunction
    
    // Constraints
    constraint addr_c { addr inside {[0:255]}; }
    constraint data_c { data != 32'h0; }
  endclass
  
  // Sequence
  class my_sequence extends uvm_sequence #(my_transaction);
    `uvm_object_utils(my_sequence)
    
    function new(string name = "my_sequence");
      super.new(name);
    endfunction
    
    virtual task body();
      my_transaction trans;
      repeat(10) begin
        trans = my_transaction::type_id::create("trans");
        start_item(trans);
        assert(trans.randomize());
        finish_item(trans);
      end
    endtask
  endclass
  
  // Driver
  class my_driver extends uvm_driver #(my_transaction);
    `uvm_component_utils(my_driver)
    
    virtual interface my_interface vif;
    
    function new(string name = "my_driver", uvm_component parent = null);
      super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      if (!uvm_config_db#(virtual my_interface)::get(this, "", "vif", vif))
        `uvm_fatal("DRIVER", "Virtual interface not found")
    endfunction
    
    virtual task run_phase(uvm_phase phase);
      my_transaction trans;
      forever begin
        seq_item_port.get_next_item(trans);
        drive_transaction(trans);
        seq_item_port.item_done();
      end
    endtask
    
    virtual task drive_transaction(my_transaction trans);
      @(posedge vif.clk);
      vif.addr <= trans.addr;
      vif.data <= trans.data;
      vif.read_write <= trans.read_write;
      vif.valid <= 1'b1;
      @(posedge vif.clk);
      vif.valid <= 1'b0;
      `uvm_info("DRIVER", $sformatf("Drove transaction: addr=0x%0h, data=0x%0h, rw=%0b", 
                trans.addr, trans.data, trans.read_write), UVM_MEDIUM)
    endtask
  endclass
  
  // Monitor
  class my_monitor extends uvm_monitor;
    `uvm_component_utils(my_monitor)
    
    virtual interface my_interface vif;
    uvm_analysis_port #(my_transaction) analysis_port;
    
    function new(string name = "my_monitor", uvm_component parent = null);
      super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      if (!uvm_config_db#(virtual my_interface)::get(this, "", "vif", vif))
        `uvm_fatal("MONITOR", "Virtual interface not found")
      analysis_port = new("analysis_port", this);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
      my_transaction trans;
      forever begin
        @(posedge vif.clk);
        if (vif.valid) begin
          trans = my_transaction::type_id::create("trans");
          trans.addr = vif.addr;
          trans.data = vif.data;
          trans.read_write = vif.read_write;
          trans.valid = vif.valid;
          analysis_port.write(trans);
          `uvm_info("MONITOR", $sformatf("Monitored transaction: addr=0x%0h, data=0x%0h, rw=%0b", 
                    trans.addr, trans.data, trans.read_write), UVM_MEDIUM)
        end
      end
    endtask
  endclass
  
  // Sequencer
  typedef uvm_sequencer #(my_transaction) my_sequencer;
  
  // Agent
  class my_agent extends uvm_agent;
    `uvm_component_utils(my_agent)
    
    my_driver    driver;
    my_monitor   monitor;
    my_sequencer sequencer;
    
    function new(string name = "my_agent", uvm_component parent = null);
      super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      
      // Create components
      monitor = my_monitor::type_id::create("monitor", this);
      
      if (get_is_active() == UVM_ACTIVE) begin
        driver = my_driver::type_id::create("driver", this);
        sequencer = my_sequencer::type_id::create("sequencer", this);
      end
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      
      if (get_is_active() == UVM_ACTIVE) begin
        driver.seq_item_port.connect(sequencer.seq_item_export);
      end
    endfunction
  endclass
  
endpackage