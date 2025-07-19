// UVM Package for Counter Testbench
package counter_pkg;
    
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    // Parameters
    parameter int WIDTH = 8;
    parameter int MAX_COUNT = (1 << WIDTH) - 1;
    
    // Transaction item
    class counter_transaction extends uvm_sequence_item;
        
        // Transaction fields
        rand bit             reset;
        rand bit             enable;
        rand bit             load;
        rand bit [WIDTH-1:0] load_data;
        bit [WIDTH-1:0]      count;
        bit                  overflow;
        
        // Constraints
        constraint c_reset { reset dist {0 := 95, 1 := 5}; }
        constraint c_enable { enable dist {0 := 30, 1 := 70}; }
        constraint c_load { load dist {0 := 90, 1 := 10}; }
        constraint c_load_data { load_data inside {[0:MAX_COUNT]}; }
        
        // UVM macros
        `uvm_object_utils_begin(counter_transaction)
            `uvm_field_int(reset, UVM_ALL_ON)
            `uvm_field_int(enable, UVM_ALL_ON)
            `uvm_field_int(load, UVM_ALL_ON)
            `uvm_field_int(load_data, UVM_ALL_ON)
            `uvm_field_int(count, UVM_ALL_ON)
            `uvm_field_int(overflow, UVM_ALL_ON)
        `uvm_object_utils_end
        
        function new(string name = "counter_transaction");
            super.new(name);
        endfunction
        
    endclass
    
    // Sequence
    class counter_sequence extends uvm_sequence #(counter_transaction);
        
        `uvm_object_utils(counter_sequence)
        
        function new(string name = "counter_sequence");
            super.new(name);
        endfunction
        
        virtual task body();
            counter_transaction req;
            
            repeat(100) begin
                req = counter_transaction::type_id::create("req");
                start_item(req);
                assert(req.randomize());
                finish_item(req);
            end
        endtask
        
    endclass
    
    // Reset sequence
    class counter_reset_sequence extends uvm_sequence #(counter_transaction);
        
        `uvm_object_utils(counter_reset_sequence)
        
        function new(string name = "counter_reset_sequence");
            super.new(name);
        endfunction
        
        virtual task body();
            counter_transaction req;
            
            req = counter_transaction::type_id::create("req");
            start_item(req);
            req.reset = 1;
            req.enable = 0;
            req.load = 0;
            req.load_data = 0;
            finish_item(req);
            
            repeat(5) begin
                req = counter_transaction::type_id::create("req");
                start_item(req);
                req.reset = 0;
                req.enable = 0;
                req.load = 0;
                req.load_data = 0;
                finish_item(req);
            end
        endtask
        
    endclass
    
    // Driver
    class counter_driver extends uvm_driver #(counter_transaction);
        
        virtual counter_if vif;
        
        `uvm_component_utils(counter_driver)
        
        function new(string name = "counter_driver", uvm_component parent = null);
            super.new(name, parent);
        endfunction
        
        virtual function void build_phase(uvm_phase phase);
            super.build_phase(phase);
            if (!uvm_config_db#(virtual counter_if)::get(this, "", "vif", vif))
                `uvm_fatal("DRIVER", "Could not get vif")
        endfunction
        
        virtual task run_phase(uvm_phase phase);
            counter_transaction req;
            
            // Initialize signals
            vif.driver_cb.rst_n <= 1'b1;
            vif.driver_cb.enable <= 1'b0;
            vif.driver_cb.load <= 1'b0;
            vif.driver_cb.load_data <= '0;
            
            forever begin
                seq_item_port.get_next_item(req);
                drive_transaction(req);
                seq_item_port.item_done();
            end
        endtask
        
        virtual task drive_transaction(counter_transaction req);
            @(vif.driver_cb);
            vif.driver_cb.rst_n <= !req.reset;
            vif.driver_cb.enable <= req.enable;
            vif.driver_cb.load <= req.load;
            vif.driver_cb.load_data <= req.load_data;
        endtask
        
    endclass
    
    // Monitor
    class counter_monitor extends uvm_monitor;
        
        virtual counter_if vif;
        uvm_analysis_port #(counter_transaction) ap;
        
        `uvm_component_utils(counter_monitor)
        
        function new(string name = "counter_monitor", uvm_component parent = null);
            super.new(name, parent);
        endfunction
        
        virtual function void build_phase(uvm_phase phase);
            super.build_phase(phase);
            ap = new("ap", this);
            if (!uvm_config_db#(virtual counter_if)::get(this, "", "vif", vif))
                `uvm_fatal("MONITOR", "Could not get vif")
        endfunction
        
        virtual task run_phase(uvm_phase phase);
            counter_transaction trans;
            
            forever begin
                @(vif.monitor_cb);
                trans = counter_transaction::type_id::create("trans");
                trans.reset = !vif.monitor_cb.rst_n;
                trans.enable = vif.monitor_cb.enable;
                trans.load = vif.monitor_cb.load;
                trans.load_data = vif.monitor_cb.load_data;
                trans.count = vif.monitor_cb.count;
                trans.overflow = vif.monitor_cb.overflow;
                ap.write(trans);
            end
        endtask
        
    endclass
    
    // Scoreboard
    class counter_scoreboard extends uvm_scoreboard;
        
        uvm_analysis_imp #(counter_transaction, counter_scoreboard) ap_imp;
        counter_transaction expected_trans;
        bit [WIDTH-1:0] expected_count;
        bit expected_overflow;
        
        `uvm_component_utils(counter_scoreboard)
        
        function new(string name = "counter_scoreboard", uvm_component parent = null);
            super.new(name, parent);
            expected_count = 0;
            expected_overflow = 0;
        endfunction
        
        virtual function void build_phase(uvm_phase phase);
            super.build_phase(phase);
            ap_imp = new("ap_imp", this);
        endfunction
        
        virtual function void write(counter_transaction trans);
            // Calculate expected values
            if (trans.reset) begin
                expected_count = 0;
                expected_overflow = 0;
            end
            else if (trans.load) begin
                expected_count = trans.load_data;
                expected_overflow = 0;
            end
            else if (trans.enable) begin
                {expected_overflow, expected_count} = expected_count + 1;
            end
            
            // Compare with actual values
            if (trans.count !== expected_count) begin
                `uvm_error("SCOREBOARD", $sformatf("Count mismatch: expected=%0d, actual=%0d", 
                          expected_count, trans.count))
            end
            
            if (trans.overflow !== expected_overflow) begin
                `uvm_error("SCOREBOARD", $sformatf("Overflow mismatch: expected=%0b, actual=%0b", 
                          expected_overflow, trans.overflow))
            end
            
            `uvm_info("SCOREBOARD", $sformatf("Transaction: reset=%b, enable=%b, load=%b, load_data=%0d, count=%0d, overflow=%b", 
                     trans.reset, trans.enable, trans.load, trans.load_data, trans.count, trans.overflow), UVM_HIGH)
        endfunction
        
    endclass
    
    // Agent
    class counter_agent extends uvm_agent;
        
        counter_driver    driver;
        counter_monitor   monitor;
        uvm_sequencer #(counter_transaction) sequencer;
        
        `uvm_component_utils(counter_agent)
        
        function new(string name = "counter_agent", uvm_component parent = null);
            super.new(name, parent);
        endfunction
        
        virtual function void build_phase(uvm_phase phase);
            super.build_phase(phase);
            
            if (get_is_active() == UVM_ACTIVE) begin
                driver = counter_driver::type_id::create("driver", this);
                sequencer = uvm_sequencer#(counter_transaction)::type_id::create("sequencer", this);
            end
            monitor = counter_monitor::type_id::create("monitor", this);
        endfunction
        
        virtual function void connect_phase(uvm_phase phase);
            if (get_is_active() == UVM_ACTIVE) begin
                driver.seq_item_port.connect(sequencer.seq_item_export);
            end
        endfunction
        
    endclass
    
    // Environment
    class counter_env extends uvm_env;
        
        counter_agent      agent;
        counter_scoreboard scoreboard;
        
        `uvm_component_utils(counter_env)
        
        function new(string name = "counter_env", uvm_component parent = null);
            super.new(name, parent);
        endfunction
        
        virtual function void build_phase(uvm_phase phase);
            super.build_phase(phase);
            agent = counter_agent::type_id::create("agent", this);
            scoreboard = counter_scoreboard::type_id::create("scoreboard", this);
        endfunction
        
        virtual function void connect_phase(uvm_phase phase);
            agent.monitor.ap.connect(scoreboard.ap_imp);
        endfunction
        
    endclass
    
    // Test
    class counter_test extends uvm_test;
        
        counter_env env;
        
        `uvm_component_utils(counter_test)
        
        function new(string name = "counter_test", uvm_component parent = null);
            super.new(name, parent);
        endfunction
        
        virtual function void build_phase(uvm_phase phase);
            super.build_phase(phase);
            env = counter_env::type_id::create("env", this);
        endfunction
        
        virtual task run_phase(uvm_phase phase);
            counter_reset_sequence reset_seq;
            counter_sequence main_seq;
            
            phase.raise_objection(this);
            
            // Run reset sequence
            reset_seq = counter_reset_sequence::type_id::create("reset_seq");
            reset_seq.start(env.agent.sequencer);
            
            // Run main sequence
            main_seq = counter_sequence::type_id::create("main_seq");
            main_seq.start(env.agent.sequencer);
            
            phase.drop_objection(this);
        endtask
        
    endclass

endpackage