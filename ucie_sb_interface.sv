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
  // Only check frequency during active transmission, ignore gaps
  property sbtx_clk_800mhz_frequency;
    realtime current_time, prev_time, time_diff;
    @(posedge SBTX_CLK) 
      (prev_time = $realtime, 1'b1) |-> 
      @(posedge SBTX_CLK) 
      (current_time = $realtime, time_diff = current_time - prev_time,
       // Only check frequency for consecutive clocks (< 1.875ns), ignore gaps
       (time_diff >= 1.875ns) || 
       (time_diff >= 1.1875ns && time_diff <= 1.3125ns));
  endproperty
  
  property sbrx_clk_800mhz_frequency;
    realtime current_time, prev_time, time_diff;
    @(posedge SBRX_CLK) 
      (prev_time = $realtime, 1'b1) |-> 
      @(posedge SBRX_CLK) 
      (current_time = $realtime, time_diff = current_time - prev_time,
       // Only check frequency for consecutive clocks (< 1.875ns), ignore gaps
       (time_diff >= 1.875ns) || 
       (time_diff >= 1.1875ns && time_diff <= 1.3125ns));
  endproperty
  
  // UCIe minimum gap requirement: 32 UI between packets
  // Check time between posedges: ignore <1.5 cycles, others must be ≥32 UI
  property min_gap_32ui_tx;
    realtime prev_edge, curr_edge, time_diff;
    @(posedge SBTX_CLK) 
      (prev_edge = $realtime, 1'b1) |-> 
      @(posedge SBTX_CLK) 
      (curr_edge = $realtime, time_diff = curr_edge - prev_edge,
       // If time_diff < 1.875ns (1.5 cycles), ignore (normal clock)
       // If time_diff >= 1.875ns, must be ≥ 40ns (32 UI gap)
       (time_diff < 1.875ns) || (time_diff >= 40.0ns));
  endproperty
  
  property min_gap_32ui_rx;
    realtime prev_edge, curr_edge, time_diff;
    @(posedge SBRX_CLK) 
      (prev_edge = $realtime, 1'b1) |-> 
      @(posedge SBRX_CLK) 
      (curr_edge = $realtime, time_diff = curr_edge - prev_edge,
       // If time_diff < 1.875ns (1.5 cycles), ignore (normal clock)
       // If time_diff >= 1.875ns, must be ≥ 40ns (32 UI gap)
       (time_diff < 1.875ns) || (time_diff >= 40.0ns));
  endproperty
  
  //=============================================================================
  // ASSERTION INSTANTIATION WITH TAGS
  //=============================================================================
  //
  // Assertion tags allow selective control via simulator commands:
  //   - VCS: $assertoff(0, "ASSERT_SBTX_800MHZ_FREQ") 
  //   - Questa: disable assertion */ASSERT_SBTX_800MHZ_FREQ
  //   - Xcelium: assertion -disable ASSERT_SBTX_800MHZ_FREQ
  //
  // Tag categories:
  //   - RESET_CHECK: Reset behavior validation
  //   - FREQ_CHECK: 800MHz ±5% frequency validation  
  //   - GAP_CHECK: 32 UI minimum gap validation
  //=============================================================================
  
  // Reset behavior assertions
  ASSERT_RESET_TX_CLK: assert property (reset_clears_tx_clk) else 
    $error("[RESET_CHECK] TX clock not cleared during reset");
    
  ASSERT_RESET_TX_DATA: assert property (reset_clears_tx_data) else 
    $error("[RESET_CHECK] TX data not cleared during reset");
    
  // UCIe protocol assertions (can be disabled for performance)
  ASSERT_SBTX_800MHZ_FREQ: assert property (sbtx_clk_800mhz_frequency) else 
    $error("[FREQ_CHECK] SBTX_CLK frequency out of UCIe spec: consecutive clocks must be 800MHz ±5% (1.1875ns-1.3125ns)");
    
  ASSERT_SBRX_800MHZ_FREQ: assert property (sbrx_clk_800mhz_frequency) else 
    $error("[FREQ_CHECK] SBRX_CLK frequency out of UCIe spec: consecutive clocks must be 800MHz ±5% (1.1875ns-1.3125ns)");
    
  ASSERT_SBTX_32UI_GAP: assert property (min_gap_32ui_tx) else 
    $error("[GAP_CHECK] SBTX gap violation: clock edge spacing >1.5 cycles must be ≥32 UI (40ns)");
    
  ASSERT_SBRX_32UI_GAP: assert property (min_gap_32ui_rx) else 
    $error("[GAP_CHECK] SBRX gap violation: clock edge spacing >1.5 cycles must be ≥32 UI (40ns)");

endinterface : ucie_sb_interface