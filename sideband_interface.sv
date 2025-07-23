interface sideband_interface(input logic sb_reset);
  
  // UCIe Sideband signals - separate TX and RX paths
  logic sbtx_data;   // Sideband TX data
  logic sbtx_clk;    // Sideband TX clock
  logic sbrx_data;   // Sideband RX data  
  logic sbrx_clk;    // Sideband RX clock
  
  // Clocking blocks for TX (driver) - synchronous to TX clock
  clocking driver_cb @(posedge sbtx_clk);
    default input #1step output #0;
    output sbtx_data;
  endclocking
  
  // Clocking blocks for RX (monitor) - synchronous to RX clock
  clocking monitor_cb @(posedge sbrx_clk);
    default input #1step;
    input sbrx_data;
  endclocking
  
  // Modports for driver (TX path)
  modport driver_mp (
    clocking driver_cb,
    input sb_reset, sbrx_clk, sbrx_data,
    output sbtx_data, sbtx_clk
  );
  
  // Modports for monitor (RX path)
  modport monitor_mp (
    clocking monitor_cb,
    input sb_reset, sbtx_clk, sbtx_data,
    output sbrx_data, sbrx_clk
  );
  
  // Protocol checking properties for TX path
  
  // Property: Minimum gap between TX packets (32 bits low)
  property min_gap_between_tx_packets;
    bit [5:0] gap_counter;
    @(posedge sbtx_clk) disable iff (sb_reset)
    ($fell(sbtx_data), gap_counter = 0) |-> 
    (sbtx_data == 1'b0, gap_counter++) [*32] ##1 
    (sbtx_data == 1'b1 || gap_counter >= 32);
  endproperty
  
  // Property: TX serial packet is exactly 64 bits when active
  property tx_packet_length_64bits;
    int bit_counter;
    @(posedge sbtx_clk) disable iff (sb_reset)
    ($rose(sbtx_data), bit_counter = 1) |-> 
    (sbtx_data, bit_counter++) [*63] ##1 bit_counter == 64;
  endproperty
  
  // Property: TX data should be stable during clock edges
  property tx_data_stable_on_clock;
    @(posedge sbtx_clk) disable iff (sb_reset)
    $stable(sbtx_data);
  endproperty
  
  // Property: Minimum gap between RX packets (32 bits low)
  property min_gap_between_rx_packets;
    bit [5:0] gap_counter;
    @(posedge sbrx_clk) disable iff (sb_reset)
    ($fell(sbrx_data), gap_counter = 0) |-> 
    (sbrx_data == 1'b0, gap_counter++) [*32] ##1 
    (sbrx_data == 1'b1 || gap_counter >= 32);
  endproperty
  
  // Property: RX serial packet is exactly 64 bits when active
  property rx_packet_length_64bits;
    int bit_counter;
    @(posedge sbrx_clk) disable iff (sb_reset)
    ($rose(sbrx_data), bit_counter = 1) |-> 
    (sbrx_data, bit_counter++) [*63] ##1 bit_counter == 64;
  endproperty
  
  // Property: RX data should be stable during clock edges
  property rx_data_stable_on_clock;
    @(posedge sbrx_clk) disable iff (sb_reset)
    $stable(sbrx_data);
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
  covergroup sideband_tx_activity_cg @(posedge sbtx_clk);
    option.per_instance = 1;
    option.name = "sideband_tx_cov";
    
    tx_data_transitions: coverpoint sbtx_data {
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
  covergroup sideband_rx_activity_cg @(posedge sbrx_clk);
    option.per_instance = 1;
    option.name = "sideband_rx_cov";
    
    rx_data_transitions: coverpoint sbrx_data {
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
    @(posedge sbtx_data);  // Wait for packet start
    repeat(64) @(posedge sbtx_clk);  // Wait for 64 bits
    @(negedge sbtx_data);  // Wait for packet end
  endtask
  
  // Task to wait for a complete RX packet reception
  task wait_for_rx_packet_complete();
    @(posedge sbrx_data);  // Wait for packet start
    repeat(64) @(posedge sbrx_clk);  // Wait for 64 bits
    @(negedge sbrx_data);  // Wait for packet end
  endtask
  
  // Task to wait for TX idle condition (minimum gap)
  task wait_for_tx_idle();
    int idle_count = 0;
    while (idle_count < 32) begin
      @(posedge sbtx_clk);
      if (sbtx_data == 1'b0)
        idle_count++;
      else
        idle_count = 0;
    end
  endtask
  
  // Task to wait for RX idle condition (minimum gap)
  task wait_for_rx_idle();
    int idle_count = 0;
    while (idle_count < 32) begin
      @(posedge sbrx_clk);
      if (sbrx_data == 1'b0)
        idle_count++;
      else
        idle_count = 0;
    end
  endtask
  
  // Function to check if TX interface is idle
  function bit is_tx_idle();
    return (sbtx_data == 1'b0);
  endfunction
  
  // Function to check if RX interface is idle
  function bit is_rx_idle();
    return (sbrx_data == 1'b0);
  endfunction
  
  // Function to sample current TX data
  function bit sample_tx_data();
    return sbtx_data;
  endfunction
  
  // Function to sample current RX data
  function bit sample_rx_data();
    return sbrx_data;
  endfunction
  
endinterface