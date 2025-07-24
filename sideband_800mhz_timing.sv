// UCIe Sideband 800MHz Timing Analysis
// This file demonstrates the timing characteristics of 800MHz sideband operation

`include "uvm_macros.svh"
import uvm_pkg::*;

module sideband_800mhz_timing;

  // 800MHz timing constants
  parameter real CLOCK_FREQ = 800e6;              // 800MHz
  parameter real CLOCK_PERIOD = 1.25;             // ns
  parameter real CLOCK_HIGH = 0.625;              // ns (50% duty cycle)
  parameter real CLOCK_LOW = 0.625;               // ns (50% duty cycle)
  
  // UCIe protocol constants
  parameter int PACKET_BITS = 64;                 // bits per packet
  parameter int MIN_GAP_CYCLES = 32;              // minimum gap cycles
  parameter real GAP_TIME = MIN_GAP_CYCLES * CLOCK_PERIOD; // 40ns
  
  // Calculated timing
  parameter real PACKET_TIME = PACKET_BITS * CLOCK_PERIOD;     // 80ns
  parameter real TRANSACTION_TIME = PACKET_TIME + GAP_TIME;    // 120ns
  parameter real MAX_THROUGHPUT = 1.0 / TRANSACTION_TIME;      // 8.33 MHz
  
  initial begin
    `uvm_info("TIMING", "=== UCIe Sideband 800MHz Timing Analysis ===", UVM_NONE)
    `uvm_info("TIMING", "", UVM_NONE)
    
    // Clock characteristics
    `uvm_info("TIMING", "Clock Characteristics:", UVM_NONE)
    `uvm_info("TIMING", $sformatf("  Frequency: %.0f MHz", CLOCK_FREQ/1e6), UVM_NONE)
    `uvm_info("TIMING", $sformatf("  Period: %.3f ns", CLOCK_PERIOD), UVM_NONE)
    `uvm_info("TIMING", $sformatf("  High Time: %.3f ns", CLOCK_HIGH), UVM_NONE)
    `uvm_info("TIMING", $sformatf("  Low Time: %.3f ns", CLOCK_LOW), UVM_NONE)
    `uvm_info("TIMING", "", UVM_NONE)
    
    // Packet timing
    `uvm_info("TIMING", "Packet Timing:", UVM_NONE)
    `uvm_info("TIMING", $sformatf("  Bits per packet: %0d", PACKET_BITS), UVM_NONE)
    `uvm_info("TIMING", $sformatf("  Packet transmission time: %.1f ns", PACKET_TIME), UVM_NONE)
    `uvm_info("TIMING", $sformatf("  Minimum gap cycles: %0d", MIN_GAP_CYCLES), UVM_NONE)
    `uvm_info("TIMING", $sformatf("  Gap time: %.1f ns", GAP_TIME), UVM_NONE)
    `uvm_info("TIMING", $sformatf("  Total transaction time: %.1f ns", TRANSACTION_TIME), UVM_NONE)
    `uvm_info("TIMING", "", UVM_NONE)
    
    // Performance calculations
    `uvm_info("TIMING", "Performance:", UVM_NONE)
    `uvm_info("TIMING", $sformatf("  Max transaction rate: %.2f MHz", MAX_THROUGHPUT/1e6), UVM_NONE)
    `uvm_info("TIMING", $sformatf("  Max data rate (64-bit): %.2f Gbps", (PACKET_BITS * MAX_THROUGHPUT)/1e9), UVM_NONE)
    `uvm_info("TIMING", $sformatf("  Efficiency: %.1f%% (data vs total time)", (PACKET_TIME/TRANSACTION_TIME)*100), UVM_NONE)
    `uvm_info("TIMING", "", UVM_NONE)
    
    // Different transaction types
    analyze_transaction_types();
    
    // Setup/hold timing considerations
    analyze_timing_margins();
    
    $finish;
  end
  
  // Analyze different UCIe transaction types
  task analyze_transaction_types();
    real header_time = PACKET_TIME;                    // 80ns for header
    real data32_time = PACKET_TIME;                    // 80ns for 32-bit data (padded to 64-bit)
    real data64_time = PACKET_TIME;                    // 80ns for 64-bit data
    real total_read_time = header_time + GAP_TIME;     // Header + gap
    real total_write32_time = header_time + GAP_TIME + data32_time + GAP_TIME; // Header + gap + data + gap
    real total_write64_time = header_time + GAP_TIME + data64_time + GAP_TIME; // Header + gap + data + gap
    
    `uvm_info("TIMING", "Transaction Type Analysis:", UVM_NONE)
    `uvm_info("TIMING", $sformatf("  Read (header only): %.1f ns", total_read_time), UVM_NONE)
    `uvm_info("TIMING", $sformatf("  Write 32-bit: %.1f ns", total_write32_time), UVM_NONE)
    `uvm_info("TIMING", $sformatf("  Write 64-bit: %.1f ns", total_write64_time), UVM_NONE)
    `uvm_info("TIMING", "", UVM_NONE)
    
    `uvm_info("TIMING", "Transaction Rates:", UVM_NONE)
    `uvm_info("TIMING", $sformatf("  Read rate: %.2f MHz", 1e9/total_read_time/1e6), UVM_NONE)
    `uvm_info("TIMING", $sformatf("  Write 32-bit rate: %.2f MHz", 1e9/total_write32_time/1e6), UVM_NONE)
    `uvm_info("TIMING", $sformatf("  Write 64-bit rate: %.2f MHz", 1e9/total_write64_time/1e6), UVM_NONE)
    `uvm_info("TIMING", "", UVM_NONE)
  endtask
  
  // Analyze setup/hold timing margins
  task analyze_timing_margins();
    real typical_setup = 0.1;      // 100ps
    real typical_hold = 0.1;       // 100ps
    real margin_percent;
    
    `uvm_info("TIMING", "Timing Margin Analysis (at 800MHz):", UVM_NONE)
    
    margin_percent = (typical_setup / CLOCK_LOW) * 100;
    `uvm_info("TIMING", $sformatf("  Setup time: %.1f ps (%.1f%% of low period)", typical_setup*1000, margin_percent), UVM_NONE)
    
    margin_percent = (typical_hold / CLOCK_HIGH) * 100;
    `uvm_info("TIMING", $sformatf("  Hold time: %.1f ps (%.1f%% of high period)", typical_hold*1000, margin_percent), UVM_NONE)
    
    if (typical_setup + typical_hold > CLOCK_PERIOD * 0.5) begin
      `uvm_warning("TIMING", "Setup + hold time exceeds 50% of clock period - may need adjustment")
    end else begin
      `uvm_info("TIMING", "  Timing margins look reasonable for 800MHz operation", UVM_NONE)
    end
    
    `uvm_info("TIMING", "", UVM_NONE)
  endtask

endmodule

// Expected output:
// === UCIe Sideband 800MHz Timing Analysis ===
// 
// Clock Characteristics:
//   Frequency: 800 MHz
//   Period: 1.250 ns
//   High Time: 0.625 ns
//   Low Time: 0.625 ns
// 
// Packet Timing:
//   Bits per packet: 64
//   Packet transmission time: 80.0 ns
//   Minimum gap cycles: 32
//   Gap time: 40.0 ns
//   Total transaction time: 120.0 ns
// 
// Performance:
//   Max transaction rate: 8.33 MHz
//   Max data rate (64-bit): 0.53 Gbps
//   Efficiency: 66.7% (data vs total time)