// UCIe Sideband Interface
// Defines signals for UCIe sideband protocol communication

//=============================================================================
// INTERFACE: ucie_sb_interface
//
// DESCRIPTION:
//   UCIe sideband interface defining the source-synchronous serial communication
//   signals for the UCIe sideband protocol. Supports separate TX and RX paths
//   for driver and monitor access.
//
// SIGNALS:
//   - SBTX_CLK/SBRX_CLK: Source-synchronous clocks (800MHz)
//   - SBTX_DATA/SBRX_DATA: Serial data signals
//   - sb_reset: Active-high reset signal
//
// AUTHOR: UCIe Sideband UVM Agent
// VERSION: 1.0
//=============================================================================

interface ucie_sb_interface(input logic clk, input logic reset);
  
  //=============================================================================
  // SIGNAL DECLARATIONS
  //=============================================================================
  
  // UCIe sideband TX signals (driven by driver)
  logic SBTX_CLK;   // TX clock (source-synchronous)
  logic SBTX_DATA;  // TX serial data
  
  // UCIe sideband RX signals (monitored by monitor)  
  logic SBRX_CLK;   // RX clock (source-synchronous)
  logic SBRX_DATA;  // RX serial data
  
  // Control signals
  logic sb_reset;   // Active-high reset
  

  
  //=============================================================================
  // ASSERTIONS
  //=============================================================================
  
  // Reset behavior assertions
  property reset_clears_tx_clk;
    @(posedge clk) sb_reset |-> (SBTX_CLK == 1'b0);
  endproperty
  
  property reset_clears_tx_data;
    @(posedge clk) sb_reset |-> (SBTX_DATA == 1'b0);
  endproperty
  
  // UCIe sideband protocol assertions
  
  // UCIe 800MHz ±5% frequency check (1.25ns ±0.0625ns period)
  property sbtx_clk_800mhz_frequency;
    realtime current_time, prev_time;
    @(posedge SBTX_CLK) 
      (prev_time = $realtime, 1'b1) |-> 
      @(posedge SBTX_CLK) 
      (current_time = $realtime, 
       (current_time - prev_time) >= 1.1875ns && (current_time - prev_time) <= 1.3125ns);
  endproperty
  
  property sbrx_clk_800mhz_frequency;
    realtime current_time, prev_time;
    @(posedge SBRX_CLK) 
      (prev_time = $realtime, 1'b1) |-> 
      @(posedge SBRX_CLK) 
      (current_time = $realtime, 
       (current_time - prev_time) >= 1.1875ns && (current_time - prev_time) <= 1.3125ns);
  endproperty
  
  // UCIe minimum gap requirement: 32 UI between packets
  // Detect end of packet (transition from data to idle)
  property min_gap_32ui_tx;
    realtime gap_start_time;
    @(negedge SBTX_CLK) 
      ($fell(SBTX_DATA), gap_start_time = $realtime) |-> 
      @(posedge SBTX_CLK) 
      (SBTX_DATA == 1'b1) |-> 
      (($realtime - gap_start_time) >= 40.0ns); // 32 UI * 1.25ns = 40ns
  endproperty
  
  property min_gap_32ui_rx;
    realtime gap_start_time;
    @(negedge SBRX_CLK) 
      ($fell(SBRX_DATA), gap_start_time = $realtime) |-> 
      @(posedge SBRX_CLK) 
      (SBRX_DATA == 1'b1) |-> 
      (($realtime - gap_start_time) >= 40.0ns); // 32 UI * 1.25ns = 40ns
  endproperty
  
  // Enable assertions
  assert property (reset_clears_tx_clk) else 
    $error("TX clock not cleared during reset");
    
  assert property (reset_clears_tx_data) else 
    $error("TX data not cleared during reset");
    
  // UCIe protocol assertions (can be disabled for performance)
  assert property (sbtx_clk_800mhz_frequency) else 
    $error("SBTX_CLK frequency out of UCIe spec: must be 800MHz ±5% (1.1875ns-1.3125ns period)");
    
  assert property (sbrx_clk_800mhz_frequency) else 
    $error("SBRX_CLK frequency out of UCIe spec: must be 800MHz ±5% (1.1875ns-1.3125ns period)");
    
  assert property (min_gap_32ui_tx) else 
    $error("SBTX gap violation: minimum 32 UI (40ns) required between packets");
    
  assert property (min_gap_32ui_rx) else 
    $error("SBRX gap violation: minimum 32 UI (40ns) required between packets");

endinterface : ucie_sb_interface