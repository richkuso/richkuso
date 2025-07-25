// UCIe Sideband Clock Pattern Example
// Demonstrates the usage of clock pattern sequences for timing synchronization

`include "uvm_macros.svh"
import uvm_pkg::*;
import ucie_sb_pkg::*;

// Example test using clock pattern sequences
class ucie_sb_clock_pattern_test extends uvm_test;
  `uvm_component_utils(ucie_sb_clock_pattern_test)
  
  ucie_sb_agent agent;
  
  function new(string name = "ucie_sb_clock_pattern_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    // Create agent
    agent = ucie_sb_agent::type_id::create("agent", this);
    
    // Configure agent for active mode
    uvm_config_db#(uvm_active_passive_enum)::set(this, "agent", "is_active", UVM_ACTIVE);
    
    `uvm_info("TEST", "Clock pattern test built", UVM_LOW)
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    ucie_sb_clock_pattern_seq clock_seq;
    ucie_sb_init_seq init_seq;
    ucie_sb_random_seq random_seq;
    
    phase.raise_objection(this);
    
    `uvm_info("TEST", "Starting UCIe sideband clock pattern demonstration", UVM_LOW)
    
    // Test 1: Basic clock pattern generation
    `uvm_info("TEST", "=== Test 1: Basic Clock Pattern Generation ===", UVM_LOW)
    clock_seq = ucie_sb_clock_pattern_seq::type_id::create("clock_seq");
    assert(clock_seq.randomize() with {
      num_patterns == 3;
      gap_cycles == 50;
      pattern_srcid == 3'b001;  // D2D_ADAPTER
      pattern_dstid == 3'b000;  // LOCAL_DIE
    });
    clock_seq.start(agent.sequencer);
    
    #200ns; // Wait between tests
    
    // Test 2: UCIe initialization sequence with clock patterns
    `uvm_info("TEST", "=== Test 2: UCIe Initialization Sequence ===", UVM_LOW)
    init_seq = ucie_sb_init_seq::type_id::create("init_seq");
    assert(init_seq.randomize() with {
      init_srcid == 3'b001;      // D2D_ADAPTER
      init_dstid == 3'b000;      // LOCAL_DIE
      reset_result == 4'h5;      // Example result code
      num_clock_patterns == 2;
      include_done_handshake == 1;
    });
    init_seq.start(agent.sequencer);
    
    #300ns; // Wait between tests
    
    // Test 3: Mixed traffic with clock patterns
    `uvm_info("TEST", "=== Test 3: Mixed Traffic with Clock Patterns ===", UVM_LOW)
    random_seq = ucie_sb_random_seq::type_id::create("random_seq");
    assert(random_seq.randomize() with {
      num_transactions == 15;
      enable_completions == 1;
      enable_messages == 1;
      enable_mgmt == 0;
      enable_clock_patterns == 1;  // Enable clock patterns in random mix
    });
    random_seq.start(agent.sequencer);
    
    #500ns; // Wait for completion
    
    `uvm_info("TEST", "UCIe sideband clock pattern demonstration completed", UVM_LOW)
    
    phase.drop_objection(this);
  endtask
  
endclass

// Standalone example module for clock pattern demonstration
module ucie_sb_clock_pattern_example;
  
  // Clock and reset
  logic clk;
  logic rst_n;
  
  // UCIe sideband interface
  ucie_sb_interface sb_if();
  
  // Clock generation (800MHz for 1.25ns UI)
  initial begin
    clk = 0;
    forever #0.625ns clk = ~clk; // 800MHz clock
  end
  
  // Reset generation
  initial begin
    rst_n = 0;
    #100ns rst_n = 1;
  end
  
  // Connect interface signals
  assign sb_if.clk = clk;
  assign sb_if.rst_n = rst_n;
  
  // UVM test execution
  initial begin
    // Set interface in config DB
    uvm_config_db#(virtual ucie_sb_interface)::set(null, "*", "vif", sb_if);
    
    // Set UI time for 800MHz (1.25ns)
    uvm_config_db#(real)::set(null, "*", "ui_time_ns", 1.25);
    
    // Run the test
    run_test("ucie_sb_clock_pattern_test");
  end
  
  // Monitor the interface signals for demonstration
  initial begin
    wait(rst_n);
    forever begin
      @(posedge sb_if.SBTX_CLK or posedge sb_if.SBRX_CLK);
      if (sb_if.SBTX_CLK || sb_if.SBRX_CLK) begin
        $display("[%0t] Clock edge detected - TX_CLK=%b, TX_DATA=%b, RX_CLK=%b, RX_DATA=%b", 
                 $time, sb_if.SBTX_CLK, sb_if.SBTX_DATA, sb_if.SBRX_CLK, sb_if.SBRX_DATA);
      end
    end
  end
  
endmodule

// Usage Examples and Documentation

/*
=== UCIe Sideband Clock Pattern Sequence Usage Examples ===

1. Basic Clock Pattern Generation:
   ```systemverilog
   ucie_sb_clock_pattern_seq clock_seq;
   clock_seq = ucie_sb_clock_pattern_seq::type_id::create("clock_seq");
   assert(clock_seq.randomize() with {
     num_patterns == 1;           // Single clock pattern
     gap_cycles == 32;            // Minimum gap
     pattern_srcid == 3'b001;     // Source ID
     pattern_dstid == 3'b000;     // Destination ID
   });
   clock_seq.start(sequencer);
   ```

2. Multiple Clock Patterns for Synchronization:
   ```systemverilog
   ucie_sb_clock_pattern_seq sync_seq;
   sync_seq = ucie_sb_clock_pattern_seq::type_id::create("sync_seq");
   assert(sync_seq.randomize() with {
     num_patterns == 5;           // Multiple patterns
     gap_cycles == 64;            // Longer gap between patterns
     pattern_srcid == 3'b010;     // PHYSICAL_LAYER
     pattern_dstid == 3'b001;     // D2D_ADAPTER
   });
   sync_seq.start(sequencer);
   ```

3. UCIe Initialization with Clock Patterns:
   ```systemverilog
   ucie_sb_init_seq init_seq;
   init_seq = ucie_sb_init_seq::type_id::create("init_seq");
   assert(init_seq.randomize() with {
     init_srcid == 3'b001;        // D2D_ADAPTER
     init_dstid == 3'b000;        // LOCAL_DIE
     reset_result == 4'h0;        // Success result
     num_clock_patterns == 3;     // 3 sync patterns before init
     include_done_handshake == 1; // Include done request/response
   });
   init_seq.start(sequencer);
   ```

4. Random Traffic with Clock Patterns:
   ```systemverilog
   ucie_sb_random_seq random_seq;
   random_seq = ucie_sb_random_seq::type_id::create("random_seq");
   assert(random_seq.randomize() with {
     num_transactions == 20;
     enable_clock_patterns == 1;  // Include clock patterns in mix
     enable_messages == 1;
     enable_completions == 1;
   });
   random_seq.start(sequencer);
   ```

=== Clock Pattern Characteristics ===

Clock Pattern Packet Format:
- Phase 0: 32'h5555_5555 (alternating 1010... pattern)
- Phase 1: 32'h5555_5555 (alternating 1010... pattern)
- Total Duration: 64 UI (64 × 1.25ns = 80ns at 800MHz)
- Gap After Pattern: Minimum 32 UI (40ns at 800MHz)

Timing Specifications:
- UI Period: 1.25ns (800MHz)
- Clock Pattern Duration: 64 UI = 80ns
- Minimum Gap: 32 UI = 40ns
- Pattern Recognition: Fixed 0x5555555555555555 value

Usage Scenarios:
1. Link Initialization and Synchronization
2. Clock Domain Crossing Alignment
3. Receiver Clock Recovery
4. Protocol Compliance Testing
5. Timing Margin Validation

=== Integration with UCIe Messages ===

The clock pattern sequence integrates seamlessly with UCIe initialization messages:

1. Clock Pattern → SBINIT Out of Reset → Clock Pattern → SBINIT Done Handshake

This provides proper timing synchronization before and during the initialization
sequence, ensuring reliable communication establishment.

*/