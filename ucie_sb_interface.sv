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
  property sbtx_clk_frequency;
    @(posedge SBTX_CLK) 1'b1 |-> ##[1:3] $rose(SBTX_CLK);
  endproperty
  
  property sbrx_clk_frequency;
    @(posedge SBRX_CLK) 1'b1 |-> ##[1:3] $rose(SBRX_CLK);
  endproperty
  
  // Enable assertions
  assert property (reset_clears_tx_clk) else 
    $error("TX clock not cleared during reset");
    
  assert property (reset_clears_tx_data) else 
    $error("TX data not cleared during reset");
    
  // Protocol assertions (can be disabled for performance)
  assert property (sbtx_clk_frequency) else 
    $warning("TX clock frequency may be out of specification");
    
  assert property (sbrx_clk_frequency) else 
    $warning("RX clock frequency may be out of specification");

endinterface : ucie_sb_interface