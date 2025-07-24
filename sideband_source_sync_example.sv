// UCIe Sideband Source-Synchronous Driver Example
// This example demonstrates how the sideband driver generates both clock and data
// as part of each transaction, implementing true source-synchronous behavior.

`include "uvm_macros.svh"
import uvm_pkg::*;

// Include the sideband UVM agent
`include "sideband_pkg_updated.sv"

module sideband_source_sync_example;

  // Testbench signals
  logic reset = 1;
  
  // Sideband interface - no external clocks needed
  sideband_interface sb_intf(reset);
  
  // Simple waveform monitor
  initial begin
    $dumpfile("sideband_source_sync.vcd");
    $dumpvars(0, sideband_source_sync_example);
  end
  
  // Reset generation
  initial begin
    reset = 1;
    #100ns;
    reset = 0;
    `uvm_info("TB", "Reset released", UVM_LOW)
  end
  
  // Source-synchronous demonstration
  initial begin
    sideband_driver driver;
    sideband_driver_config cfg;
    sideband_transaction trans;
    
    // Wait for reset
    wait(!reset);
    #50ns;
    
    `uvm_info("TB", "=== UCIe Sideband Source-Synchronous Demo ===", UVM_LOW)
    
    // Create driver and configuration
    driver = sideband_driver::type_id::create("driver", null);
    cfg = sideband_driver_config::type_id::create("cfg");
    
    // Configure for 800MHz operation (UCIe standard)
    cfg.set_frequency(800e6);        // 800MHz (1.25ns period)
    cfg.set_duty_cycle(50.0);        // 50% duty cycle (0.625ns high, 0.625ns low)
    cfg.min_gap_cycles = 32;         // UCIe minimum gap
    cfg.setup_time = 0.5;            // 500ps setup
    cfg.hold_time = 0.5;             // 500ps hold
    cfg.gap_time = 10.0;             // 10ns additional gap time
    
    driver.cfg = cfg;
    driver.vif = sb_intf;
    
    `uvm_info("TB", $sformatf("Clock period: %.1f ns, High: %.1f ns, Low: %.1f ns", 
              cfg.clock_period, cfg.clock_high_time, cfg.clock_low_time), UVM_LOW)
    
    // Create sample transactions
    trans = sideband_transaction::type_id::create("trans");
    
    // Transaction 1: Memory Read 32-bit
    trans.randomize() with {
      opcode == MEM_READ_32B;
      srcid == 3'b001;  // D2D Adapter
      dstid == 3'b000;  // Local die
      addr == 24'h123400;
      be == 8'hF0;
    };
    
    `uvm_info("TB", "--- Driving Transaction 1: Memory Read 32-bit ---", UVM_LOW)
    `uvm_info("TB", trans.convert2string(), UVM_LOW)
    
    // Drive the transaction - driver will generate clock and data
    fork
      begin
        driver.drive_transaction(trans);
      end
      begin
        // Monitor the signals
        monitor_signals("Transaction 1");
      end
    join
    
    #200ns; // Gap between transactions
    
    // Transaction 2: Configuration Write 64-bit
    trans.randomize() with {
      opcode == CFG_WRITE_64B;
      srcid == 3'b010;  // Physical Layer
      dstid == 3'b000;  // Local die
      addr == 24'h456800;
      be == 8'hFF;
      data == 64'hDEADBEEF_CAFEBABE;
    };
    
    `uvm_info("TB", "--- Driving Transaction 2: Config Write 64-bit ---", UVM_LOW)
    `uvm_info("TB", trans.convert2string(), UVM_LOW)
    
    // Drive the second transaction
    fork
      begin
        driver.drive_transaction(trans);
      end
      begin
        monitor_signals("Transaction 2");
      end
    join
    
    #200ns;
    
    `uvm_info("TB", "=== Source-Synchronous Demo Complete ===", UVM_LOW)
    $finish;
  end
  
  // Task to monitor and report signal activity
  task monitor_signals(string trans_name);
    int bit_count = 0;
    logic prev_clk = 0;
    
    `uvm_info("TB", $sformatf("Monitoring %s...", trans_name), UVM_MEDIUM)
    
    // Wait for first clock edge
    @(posedge sb_intf.SBTX_CLK);
    
    // Monitor for 64 bits + some extra time
    repeat(70) begin
      @(sb_intf.SBTX_CLK);
      if (sb_intf.SBTX_CLK !== prev_clk) begin
        if (sb_intf.SBTX_CLK === 1'b1) begin // Rising edge
          bit_count++;
          `uvm_info("TB", $sformatf("Bit %0d: Data=%b, Time=%0t", 
                    bit_count, sb_intf.SBTX_DATA, $time), UVM_HIGH)
        end
        prev_clk = sb_intf.SBTX_CLK;
      end
    end
    
    `uvm_info("TB", $sformatf("%s: Captured %0d bits", trans_name, bit_count), UVM_MEDIUM)
  endtask
  
  // Timeout watchdog
  initial begin
    #50us;
    `uvm_fatal("TB", "Simulation timeout")
  end

endmodule

// Compile and run commands:
// vcs -sverilog -ntb_opts uvm-1.2 +incdir+$UVM_HOME/src sideband_source_sync_example.sv
// ./simv +UVM_VERBOSITY=UVM_LOW