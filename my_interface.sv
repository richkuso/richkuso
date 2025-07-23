interface my_interface(input logic clk, input logic reset);
  
  // Interface signals
  logic [31:0] data;
  logic [7:0]  addr;
  logic        read_write;
  logic        valid;
  logic        ready;
  
  // Clocking blocks for synchronous operation
  clocking driver_cb @(posedge clk);
    default input #1step output #0;
    output data, addr, read_write, valid;
    input  ready;
  endclocking
  
  clocking monitor_cb @(posedge clk);
    default input #1step;
    input data, addr, read_write, valid, ready;
  endclocking
  
  // Modports for driver and monitor
  modport driver_mp (
    clocking driver_cb,
    input clk, reset
  );
  
  modport monitor_mp (
    clocking monitor_cb,
    input clk, reset
  );
  
  // Properties and assertions for protocol checking
  property valid_ready_handshake;
    @(posedge clk) disable iff (reset)
    valid |-> ##[1:10] ready;
  endproperty
  
  property data_stable_during_valid;
    @(posedge clk) disable iff (reset)
    valid && !ready |=> $stable({data, addr, read_write});
  endproperty
  
  // Bind assertions
  assert property (valid_ready_handshake) else
    $error("Valid-Ready handshake violation");
    
  assert property (data_stable_during_valid) else
    $error("Data not stable during valid period");
  
endinterface