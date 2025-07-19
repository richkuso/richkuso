// Advanced test sequences and components
package advanced_tests_pkg;
    
    import uvm_pkg::*;
    import counter_pkg::*;
    `include "uvm_macros.svh"
    
    // Directed test sequence for overflow testing
    class counter_overflow_sequence extends uvm_sequence #(counter_transaction);
        
        `uvm_object_utils(counter_overflow_sequence)
        
        function new(string name = "counter_overflow_sequence");
            super.new(name);
        endfunction
        
        virtual task body();
            counter_transaction req;
            
            // Reset first
            req = counter_transaction::type_id::create("req");
            start_item(req);
            req.reset = 1;
            req.enable = 0;
            req.load = 0;
            req.load_data = 0;
            finish_item(req);
            
            // Load near maximum value
            req = counter_transaction::type_id::create("req");
            start_item(req);
            req.reset = 0;
            req.enable = 0;
            req.load = 1;
            req.load_data = counter_pkg::MAX_COUNT - 2; // 253 for 8-bit
            finish_item(req);
            
            // Enable counting to cause overflow
            repeat(5) begin
                req = counter_transaction::type_id::create("req");
                start_item(req);
                req.reset = 0;
                req.enable = 1;
                req.load = 0;
                req.load_data = 0;
                finish_item(req);
            end
        endtask
        
    endclass
    
    // Stress test sequence
    class counter_stress_sequence extends uvm_sequence #(counter_transaction);
        
        `uvm_object_utils(counter_stress_sequence)
        
        rand int num_transactions;
        constraint c_num_trans { num_transactions inside {[500:1000]}; }
        
        function new(string name = "counter_stress_sequence");
            super.new(name);
        endfunction
        
        virtual task body();
            counter_transaction req;
            
            `uvm_info(get_type_name(), $sformatf("Starting stress test with %0d transactions", num_transactions), UVM_LOW)
            
            repeat(num_transactions) begin
                req = counter_transaction::type_id::create("req");
                start_item(req);
                assert(req.randomize() with {
                    reset dist {0 := 98, 1 := 2};
                    if (!reset) {
                        enable dist {0 := 20, 1 := 80};
                        load dist {0 := 95, 1 := 5};
                    }
                });
                finish_item(req);
            end
        endtask
        
    endclass
    
    // Coverage collector
    class counter_coverage extends uvm_subscriber #(counter_transaction);
        
        `uvm_component_utils(counter_coverage)
        
        // Coverage groups
        covergroup counter_cg;
            
            cp_reset: coverpoint trans.reset {
                bins reset_active = {1};
                bins reset_inactive = {0};
            }
            
            cp_enable: coverpoint trans.enable {
                bins enable_high = {1};
                bins enable_low = {0};
            }
            
            cp_load: coverpoint trans.load {
                bins load_active = {1};
                bins load_inactive = {0};
            }
            
            cp_load_data: coverpoint trans.load_data {
                bins low_values = {[0:63]};
                bins mid_values = {[64:191]};
                bins high_values = {[192:255]};
            }
            
            cp_count: coverpoint trans.count {
                bins zero = {0};
                bins low = {[1:63]};
                bins mid = {[64:191]};
                bins high = {[192:254]};
                bins max = {255};
            }
            
            cp_overflow: coverpoint trans.overflow {
                bins no_overflow = {0};
                bins overflow = {1};
            }
            
            // Cross coverage
            cx_load_enable: cross cp_load, cp_enable {
                ignore_bins load_and_enable = binsof(cp_load.load_active) && binsof(cp_enable.enable_high);
            }
            
            cx_reset_others: cross cp_reset, cp_enable, cp_load {
                ignore_bins reset_with_others = binsof(cp_reset.reset_active) && 
                    (binsof(cp_enable.enable_high) || binsof(cp_load.load_active));
            }
            
        endgroup
        
        counter_transaction trans;
        
        function new(string name = "counter_coverage", uvm_component parent = null);
            super.new(name, parent);
            counter_cg = new();
        endfunction
        
        virtual function void write(counter_transaction t);
            trans = t;
            counter_cg.sample();
        endfunction
        
        virtual function void report_phase(uvm_phase phase);
            `uvm_info(get_type_name(), $sformatf("Coverage = %.2f%%", counter_cg.get_coverage()), UVM_LOW)
        endfunction
        
    endclass
    
    // Enhanced environment with coverage
    class counter_env_with_coverage extends counter_env;
        
        counter_coverage coverage;
        
        `uvm_component_utils(counter_env_with_coverage)
        
        function new(string name = "counter_env_with_coverage", uvm_component parent = null);
            super.new(name, parent);
        endfunction
        
        virtual function void build_phase(uvm_phase phase);
            super.build_phase(phase);
            coverage = counter_coverage::type_id::create("coverage", this);
        endfunction
        
        virtual function void connect_phase(uvm_phase phase);
            super.connect_phase(phase);
            agent.monitor.ap.connect(coverage.analysis_export);
        endfunction
        
    endclass
    
    // Advanced test with multiple sequences
    class counter_advanced_test extends uvm_test;
        
        counter_env_with_coverage env;
        
        `uvm_component_utils(counter_advanced_test)
        
        function new(string name = "counter_advanced_test", uvm_component parent = null);
            super.new(name, parent);
        endfunction
        
        virtual function void build_phase(uvm_phase phase);
            super.build_phase(phase);
            env = counter_env_with_coverage::type_id::create("env", this);
        endfunction
        
        virtual task run_phase(uvm_phase phase);
            counter_reset_sequence reset_seq;
            counter_overflow_sequence overflow_seq;
            counter_stress_sequence stress_seq;
            
            phase.raise_objection(this);
            
            `uvm_info(get_type_name(), "Starting advanced counter test", UVM_LOW)
            
            // Reset sequence
            reset_seq = counter_reset_sequence::type_id::create("reset_seq");
            reset_seq.start(env.agent.sequencer);
            
            // Overflow test
            overflow_seq = counter_overflow_sequence::type_id::create("overflow_seq");
            overflow_seq.start(env.agent.sequencer);
            
            // Stress test
            stress_seq = counter_stress_sequence::type_id::create("stress_seq");
            assert(stress_seq.randomize());
            stress_seq.start(env.agent.sequencer);
            
            `uvm_info(get_type_name(), "Advanced counter test completed", UVM_LOW)
            
            phase.drop_objection(this);
        endtask
        
    endclass
    
    // Virtual sequence for coordinated testing
    class counter_virtual_sequence extends uvm_sequence;
        
        `uvm_object_utils(counter_virtual_sequence)
        `uvm_declare_p_sequencer(uvm_sequencer#(counter_transaction))
        
        function new(string name = "counter_virtual_sequence");
            super.new(name);
        endfunction
        
        virtual task body();
            counter_reset_sequence reset_seq;
            counter_sequence normal_seq;
            counter_overflow_sequence overflow_seq;
            
            // Parallel execution of sequences
            fork
                begin
                    reset_seq = counter_reset_sequence::type_id::create("reset_seq");
                    reset_seq.start(p_sequencer);
                    #100;
                    
                    normal_seq = counter_sequence::type_id::create("normal_seq");
                    normal_seq.start(p_sequencer);
                end
                begin
                    #500;
                    overflow_seq = counter_overflow_sequence::type_id::create("overflow_seq");
                    overflow_seq.start(p_sequencer);
                end
            join
            
        endtask
        
    endclass

endpackage