interface sideband_interface(input logic sb_reset);
  
  // UCIe Sideband signals - separate TX and RX paths
  logic SBTX_DATA;   // Sideband TX data (driven by TX driver)
  logic SBTX_CLK;    // Sideband TX clock (driven by TX driver)
  logic SBRX_DATA;   // Sideband RX data (driven by RX driver)
  logic SBRX_CLK;    // Sideband RX clock (driven by RX driver)
  
  // Initialize signals
  initial begin
    SBTX_CLK = 0;
    SBRX_CLK = 0;
    SBTX_DATA = 0;
    SBRX_DATA = 0;
  end
  
  // Modports for driver (TX path)
  modport driver_mp (
    input sb_reset, SBRX_CLK, SBRX_DATA,
    output SBTX_DATA, SBTX_CLK
  );
  
  // Modports for monitor (RX path)
  modport monitor_mp (
    input sb_reset, SBTX_CLK, SBTX_DATA,
    output SBRX_DATA, SBRX_CLK
  );
  
  // Protocol checking properties for TX path
  
  // Property: Minimum gap between TX packets (32 bits low)
  property min_gap_between_tx_packets;
    bit [5:0] gap_counter;
    @(posedge SBTX_CLK) disable iff (sb_reset)
    ($fell(SBTX_DATA), gap_counter = 0) |-> 
    (SBTX_DATA == 1'b0, gap_counter++) [*32] ##1 
    (SBTX_DATA == 1'b1 || gap_counter >= 32);
  endproperty
  
  // Property: TX serial packet is exactly 64 bits when active
  property tx_packet_length_64bits;
    int bit_counter;
    @(posedge SBTX_CLK) disable iff (sb_reset)
    ($rose(SBTX_DATA), bit_counter = 1) |-> 
    (SBTX_DATA, bit_counter++) [*63] ##1 bit_counter == 64;
  endproperty
  
  // Property: TX data should be stable during clock edges
  property tx_data_stable_on_clock;
    @(posedge SBTX_CLK) disable iff (sb_reset)
    $stable(SBTX_DATA);
  endproperty
  
  // Property: Minimum gap between RX packets (32 bits low)
  property min_gap_between_rx_packets;
    bit [5:0] gap_counter;
    @(posedge SBRX_CLK) disable iff (sb_reset)
    ($fell(SBRX_DATA), gap_counter = 0) |-> 
    (SBRX_DATA == 1'b0, gap_counter++) [*32] ##1 
    (SBRX_DATA == 1'b1 || gap_counter >= 32);
  endproperty
  
  // Property: RX serial packet is exactly 64 bits when active
  property rx_packet_length_64bits;
    int bit_counter;
    @(posedge SBRX_CLK) disable iff (sb_reset)
    ($rose(SBRX_DATA), bit_counter = 1) |-> 
    (SBRX_DATA, bit_counter++) [*63] ##1 bit_counter == 64;
  endproperty
  
  // Property: RX data should be stable during clock edges
  property rx_data_stable_on_clock;
    @(posedge SBRX_CLK) disable iff (sb_reset)
    $stable(SBRX_DATA);
  endproperty
  
  // Bind assertions (can be disabled for performance)
  `ifdef ENABLE_SIDEBAND_ASSERTIONS
    // TX path assertions
    assert property (min_gap_between_tx_packets) else
      $error("Sideband TX: Minimum gap between packets violated");
      
    assert property (tx_packet_length_64bits) else
      $warning("Sideband TX: Packet length not exactly 64 bits");
      
    assert property (tx_data_stable_on_clock) else
      $error("Sideband TX: Data not stable on clock edge");
    
    // RX path assertions
    assert property (min_gap_between_rx_packets) else
      $error("Sideband RX: Minimum gap between packets violated");
      
    assert property (rx_packet_length_64bits) else
      $warning("Sideband RX: Packet length not exactly 64 bits");
      
    assert property (rx_data_stable_on_clock) else
      $error("Sideband RX: Data not stable on clock edge");
  `endif
  
  // Coverage for TX sideband activity
  covergroup sideband_tx_activity_cg @(posedge SBTX_CLK);
    option.per_instance = 1;
    option.name = "sideband_tx_cov";
    
    tx_data_transitions: coverpoint SBTX_DATA {
      bins low = {1'b0};
      bins high = {1'b1};
      bins low_to_high = (1'b0 => 1'b1);
      bins high_to_low = (1'b1 => 1'b0);
    }
    
    reset_activity: coverpoint sb_reset {
      bins reset_active = {1'b1};
      bins reset_inactive = {1'b0};
    }
    
    // Cross coverage
    tx_data_reset_cross: cross tx_data_transitions, reset_activity;
  endgroup
  
  // Coverage for RX sideband activity
  covergroup sideband_rx_activity_cg @(posedge SBRX_CLK);
    option.per_instance = 1;
    option.name = "sideband_rx_cov";
    
    rx_data_transitions: coverpoint SBRX_DATA {
      bins low = {1'b0};
      bins high = {1'b1};
      bins low_to_high = (1'b0 => 1'b1);
      bins high_to_low = (1'b1 => 1'b0);
    }
    
    reset_activity: coverpoint sb_reset {
      bins reset_active = {1'b1};
      bins reset_inactive = {1'b0};
    }
    
    // Cross coverage
    rx_data_reset_cross: cross rx_data_transitions, reset_activity;
  endgroup
  
  // Instantiate coverage groups
  sideband_tx_activity_cg sideband_tx_cov = new();
  sideband_rx_activity_cg sideband_rx_cov = new();
  
  // Utility tasks for testbench use
  
  // Task to wait for a complete TX packet transmission
  task wait_for_tx_packet_complete();
    @(posedge SBTX_DATA);  // Wait for packet start
    repeat(64) @(posedge SBTX_CLK);  // Wait for 64 bits
    @(negedge SBTX_DATA);  // Wait for packet end
  endtask
  
  // Task to wait for a complete RX packet reception
  task wait_for_rx_packet_complete();
    @(posedge SBRX_DATA);  // Wait for packet start
    repeat(64) @(posedge SBRX_CLK);  // Wait for 64 bits
    @(negedge SBRX_DATA);  // Wait for packet end
  endtask
  
  // Task to wait for TX idle condition (minimum gap)
  task wait_for_tx_idle();
    int idle_count = 0;
    while (idle_count < 32) begin
      @(posedge SBTX_CLK);
      if (SBTX_DATA == 1'b0)
        idle_count++;
      else
        idle_count = 0;
    end
  endtask
  
  // Task to wait for RX idle condition (minimum gap)
  task wait_for_rx_idle();
    int idle_count = 0;
    while (idle_count < 32) begin
      @(posedge SBRX_CLK);
      if (SBRX_DATA == 1'b0)
        idle_count++;
      else
        idle_count = 0;
    end
  endtask
  
  // Function to check if TX interface is idle
  function bit is_tx_idle();
    return (SBTX_DATA == 1'b0);
  endfunction
  
  // Function to check if RX interface is idle
  function bit is_rx_idle();
    return (SBRX_DATA == 1'b0);
  endfunction
  
  // Function to sample current TX data
  function bit sample_tx_data();
    return SBTX_DATA;
  endfunction
  
  // Function to sample current RX data
  function bit sample_rx_data();
    return SBRX_DATA;
  endfunction
  
endinterface