interface sideband_interface(input logic sb_clk, input logic sb_reset);
  
  // Sideband signals - serial interface
  logic sb_data;
  
  // Clocking blocks for synchronous operation
  clocking driver_cb @(posedge sb_clk);
    default input #1step output #0;
    output sb_data;
  endclocking
  
  clocking monitor_cb @(posedge sb_clk);
    default input #1step;
    input sb_data;
  endclocking
  
  // Modports for driver and monitor
  modport driver_mp (
    clocking driver_cb,
    input sb_clk, sb_reset,
    output sb_data
  );
  
  modport monitor_mp (
    clocking monitor_cb,
    input sb_clk, sb_reset, sb_data
  );
  
  // Protocol checking properties
  
  // Property: Minimum gap between packets (32 bits low)
  property min_gap_between_packets;
    bit [5:0] gap_counter;
    @(posedge sb_clk) disable iff (sb_reset)
    ($fell(sb_data), gap_counter = 0) |-> 
    (sb_data == 1'b0, gap_counter++) [*32] ##1 
    (sb_data == 1'b1 || gap_counter >= 32);
  endproperty
  
  // Property: Serial packet is exactly 64 bits when active
  property packet_length_64bits;
    int bit_counter;
    @(posedge sb_clk) disable iff (sb_reset)
    ($rose(sb_data), bit_counter = 1) |-> 
    (sb_data, bit_counter++) [*63] ##1 bit_counter == 64;
  endproperty
  
  // Property: Data should be stable during clock edges
  property data_stable_on_clock;
    @(posedge sb_clk) disable iff (sb_reset)
    $stable(sb_data);
  endproperty
  
  // Bind assertions (can be disabled for performance)
  `ifdef ENABLE_SIDEBAND_ASSERTIONS
    assert property (min_gap_between_packets) else
      $error("Sideband: Minimum gap between packets violated");
      
    assert property (packet_length_64bits) else
      $warning("Sideband: Packet length not exactly 64 bits");
      
    assert property (data_stable_on_clock) else
      $error("Sideband: Data not stable on clock edge");
  `endif
  
  // Coverage for sideband activity
  covergroup sideband_activity_cg @(posedge sb_clk);
    option.per_instance = 1;
    
    data_transitions: coverpoint sb_data {
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
    data_reset_cross: cross data_transitions, reset_activity;
  endgroup
  
  // Instantiate coverage
  sideband_activity_cg sideband_cov = new();
  
  // Utility tasks for testbench use
  
  // Task to wait for a complete packet transmission
  task wait_for_packet_complete();
    @(posedge sb_data);  // Wait for packet start
    repeat(64) @(posedge sb_clk);  // Wait for 64 bits
    @(negedge sb_data);  // Wait for packet end
  endtask
  
  // Task to wait for idle condition (minimum gap)
  task wait_for_idle();
    int idle_count = 0;
    while (idle_count < 32) begin
      @(posedge sb_clk);
      if (sb_data == 1'b0)
        idle_count++;
      else
        idle_count = 0;
    end
  endtask
  
  // Function to check if interface is idle
  function bit is_idle();
    return (sb_data == 1'b0);
  endfunction
  
  // Function to sample current data
  function bit sample_data();
    return sb_data;
  endfunction
  
endinterface