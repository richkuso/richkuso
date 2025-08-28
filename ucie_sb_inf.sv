/*******************************************************************************
 * UCIe Sideband Protocol Interface
 * 
 * OVERVIEW:
 *   SystemVerilog interface defining source-synchronous serial communication
 *   signals for UCIe (Universal Chiplet Interconnect Express) sideband protocol.
 *   Provides separate TX/RX paths with comprehensive protocol assertions.
 *
 * SIGNAL DEFINITIONS:
 *   • SBTX_CLK/SBRX_CLK: Source-synchronous clocks (up to 800MHz)
 *   • SBTX_DATA/SBRX_DATA: Serial data signals
 *   • sb_reset: Active-high reset signal
 *
 * ASSERTION COVERAGE:
 *   • Reset behavior validation
 *   • 800MHz ±5% frequency compliance checking
 *   • 32 UI minimum gap enforcement
 *   • Configurable assertion control via tags
 *
 * COMPLIANCE:
 *   • IEEE 1800-2017 SystemVerilog
 *   • UCIe 1.1 specification timing requirements
 *   • UVM 1.2 interface conventions
 *
 * AUTHOR: UCIe Sideband UVM Agent
 * VERSION: 3.0 - Production-grade interface with assertions
 ******************************************************************************/

interface ucie_sb_inf(input logic clk, input logic reset);
  
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

  // Time tracking variables for assertions (updated via blocking assignments)
  realtime sbtx_prev_time = 0;
  realtime sbrx_prev_time = 0;
  

  
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
    realtime current_time, time_diff, old_prev_time;
    @(posedge SBTX_CLK) 
      (current_time = $realtime, 
       old_prev_time = sbtx_prev_time,  // Save old value before update
       time_diff = current_time - old_prev_time,
       sbtx_prev_time = current_time,  // Update for next cycle
       // Skip check for first edge (old_prev_time = 0) or gaps, check frequency for consecutive clocks
       (old_prev_time == 0) || (time_diff >= 1875) || 
       (time_diff >= 1187 && time_diff <= 1312)); // in picoseconds
  endproperty
  
  property sbrx_clk_800mhz_frequency;
    realtime current_time, time_diff, old_prev_time;
    @(posedge SBRX_CLK) 
      (current_time = $realtime, 
       old_prev_time = sbrx_prev_time,  // Save old value before update
       time_diff = current_time - old_prev_time,
       sbrx_prev_time = current_time,  // Update for next cycle
       // Skip check for first edge (old_prev_time = 0) or gaps, check frequency for consecutive clocks
       (old_prev_time == 0) || (time_diff >= 1875) || 
       (time_diff >= 1187 && time_diff <= 1312)); // in picoseconds
  endproperty
  
  // UCIe minimum gap requirement: 32 UI between packets
  // Check time between posedges: ignore <1.5 cycles, others must be ≥32 UI
  property min_gap_32ui_tx;
    realtime curr_edge, time_diff;
    @(posedge SBTX_CLK) 
      (curr_edge = $realtime, 
       time_diff = curr_edge - sbtx_prev_time,
       // Skip first edge, for others: if time_diff < 1875ps (1.5 cycles), ignore (normal clock)
       // If time_diff >= 1875ps, must be ≥ 40000ps (32 UI gap)
       (sbtx_prev_time == 0) || (time_diff < 1875) || (time_diff >= 40000));
  endproperty
  
  property min_gap_32ui_rx;
    realtime curr_edge, time_diff;
    @(posedge SBRX_CLK) 
      (curr_edge = $realtime, 
       time_diff = curr_edge - sbrx_prev_time,
       // Skip first edge, for others: if time_diff < 1875ps (1.5 cycles), ignore (normal clock)
       // If time_diff >= 1875ps, must be ≥ 40000ps (32 UI gap)
       (sbrx_prev_time == 0) || (time_diff < 1875) || (time_diff >= 40000));
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
    $error("[FREQ_CHECK] SBTX_CLK frequency out of UCIe spec: consecutive clocks must be 800MHz ±5% (1187ps-1312ps)");
    
  ASSERT_SBRX_800MHZ_FREQ: assert property (sbrx_clk_800mhz_frequency) else 
    $error("[FREQ_CHECK] SBRX_CLK frequency out of UCIe spec: consecutive clocks must be 800MHz ±5% (1187ps-1312ps)");
    
  ASSERT_SBTX_32UI_GAP: assert property (min_gap_32ui_tx) else 
    $error("[GAP_CHECK] SBTX gap violation: clock edge spacing >1.5 cycles must be ≥32 UI (40000ps)");
    
  ASSERT_SBRX_32UI_GAP: assert property (min_gap_32ui_rx) else 
    $error("[GAP_CHECK] SBRX gap violation: clock edge spacing >1.5 cycles must be ≥32 UI (40000ps)");

endinterface : ucie_sb_inf