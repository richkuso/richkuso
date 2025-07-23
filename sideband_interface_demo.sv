// Demonstration of UCIe Sideband Interface with separate TX/RX paths
// This module shows the proper signal connections for SBTX_DATA, SBTX_CLK, SBRX_DATA, SBRX_CLK

module sideband_interface_demo;
  import uvm_pkg::*;
  import sideband_pkg::*;
  `include "uvm_macros.svh"
  
  // Reset signal
  logic sb_reset = 1;
  
  // Instantiate the sideband interface
  sideband_interface sb_intf(sb_reset);
  
  // Clock generation for TX and RX paths
  initial begin
    sb_intf.sbtx_clk = 0;
    sb_intf.sbrx_clk = 0;
    sb_intf.sbtx_data = 0;
    sb_intf.sbrx_data = 0;
    
    // Generate independent TX and RX clocks
    fork
      forever #2.5 sb_intf.sbtx_clk = ~sb_intf.sbtx_clk; // 200MHz TX clock
      forever #2.5 sb_intf.sbrx_clk = ~sb_intf.sbrx_clk; // 200MHz RX clock
    join_none
    
    // Reset sequence
    sb_reset = 1;
    #100;
    sb_reset = 0;
    `uvm_info("DEMO", "Reset released, starting sideband demo", UVM_LOW)
  end
  
  // Example: Manual packet transmission to demonstrate interface
  initial begin
    bit [63:0] test_header;
    bit [63:0] test_data;
    
    // Wait for reset to be released
    wait(!sb_reset);
    #1000;
    
    `uvm_info("DEMO", "Starting manual packet transmission", UVM_LOW)
    
    // Create a test header for 32-bit memory write (opcode=00001b)
    // Phase 0: srcid=001, tag=10101, be=11110000, ep=0, opcode=00001
    // Phase 1: dp=0, cp=0, cr=0, dstid=010, addr=0x1234
    test_header[31:0]  = {3'b001, 2'b00, 5'b10101, 8'b11110000, 3'b000, 1'b0, 5'b00001, 2'b00};
    test_header[63:32] = {1'b0, 1'b0, 1'b0, 4'b0000, 3'b010, 6'b000000, 16'h1234};
    
    test_data = 64'hDEADBEEFCAFEBABE;
    
    // Transmit header
    `uvm_info("DEMO", "Transmitting header packet", UVM_LOW)
    transmit_64bit_packet(test_header);
    
    // Wait minimum gap (32 bits low)
    repeat(32) @(posedge sb_intf.sbtx_clk);
    
    // Transmit data (32-bit data padded to 64-bit)
    `uvm_info("DEMO", "Transmitting data packet", UVM_LOW)
    transmit_64bit_packet({32'h0, test_data[31:0]});
    
    // Wait and finish
    #2000;
    `uvm_info("DEMO", "Manual packet transmission completed", UVM_LOW)
    
    $finish;
  end
  
  // Task to transmit a 64-bit packet
  task transmit_64bit_packet(bit [63:0] packet);
    `uvm_info("DEMO", $sformatf("Transmitting packet: 0x%016h", packet), UVM_MEDIUM)
    
    for (int i = 0; i < 64; i++) begin
      @(posedge sb_intf.sbtx_clk);
      sb_intf.sbtx_data <= packet[i];
      if (i % 16 == 15) 
        `uvm_info("DEMO", $sformatf("Transmitted bits %0d-%0d", i-15, i), UVM_HIGH)
    end
    
    // Drive low after packet
    @(posedge sb_intf.sbtx_clk);
    sb_intf.sbtx_data <= 1'b0;
  endtask
  
  // Simple receiver to demonstrate RX monitoring
  always @(posedge sb_intf.sbrx_clk) begin
    static bit [63:0] rx_shift_reg;
    static int bit_count = 0;
    static bit receiving = 0;
    
    if (sb_reset) begin
      rx_shift_reg = 0;
      bit_count = 0;
      receiving = 0;
    end else begin
      // Detect start of packet
      if (!receiving && sb_intf.sbrx_data) begin
        receiving = 1;
        bit_count = 1;
        rx_shift_reg[0] = sb_intf.sbrx_data;
        `uvm_info("DEMO", "RX: Packet reception started", UVM_MEDIUM)
      end
      // Continue receiving
      else if (receiving && bit_count < 64) begin
        rx_shift_reg[bit_count] = sb_intf.sbrx_data;
        bit_count++;
        if (bit_count == 64) begin
          `uvm_info("DEMO", $sformatf("RX: Received complete packet: 0x%016h", rx_shift_reg), UVM_LOW)
          receiving = 0;
          bit_count = 0;
        end
      end
      // Reset on gap
      else if (receiving && !sb_intf.sbrx_data) begin
        receiving = 0;
        bit_count = 0;
      end
    end
  end
  
  // Loopback connection (in real system, this would be physical connection)
  always_comb begin
    sb_intf.sbrx_data = sb_intf.sbtx_data;
  end
  
  // Signal monitoring for debug
  initial begin
    `uvm_info("DEMO", "Starting signal monitoring", UVM_LOW)
    
    fork
      // Monitor TX signals
      forever begin
        @(posedge sb_intf.sbtx_clk);
        if (sb_intf.sbtx_data)
          `uvm_info("DEMO", "TX: Data bit = 1", UVM_DEBUG)
      end
      
      // Monitor RX signals  
      forever begin
        @(posedge sb_intf.sbrx_clk);
        if (sb_intf.sbrx_data)
          `uvm_info("DEMO", "RX: Data bit = 1", UVM_DEBUG)
      end
    join_none
  end
  
  // Waveform generation
  initial begin
    $dumpfile("sideband_interface_demo.vcd");
    $dumpvars(0, sideband_interface_demo);
  end
  
  // Timeout
  initial begin
    #50000;
    `uvm_error("DEMO", "Simulation timeout")
    $finish;
  end
  
endmodule