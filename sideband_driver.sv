// UCIe Sideband Driver Class
// Converts UVM transactions to serial bit stream on TX path

class sideband_driver extends uvm_driver #(sideband_transaction);
  `uvm_component_utils(sideband_driver)
  
  virtual sideband_interface vif;
  
  function new(string name = "sideband_driver", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual sideband_interface)::get(this, "", "vif", vif))
      `uvm_fatal("DRIVER", "Virtual interface not found")
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    sideband_transaction trans;
    forever begin
      seq_item_port.get_next_item(trans);
      drive_transaction(trans);
      seq_item_port.item_done();
    end
  endtask
  
  virtual task drive_transaction(sideband_transaction trans);
    bit [63:0] header;
    bit [63:0] data_payload;
    
    `uvm_info("SIDEBAND_DRIVER", trans.convert2string(), UVM_MEDIUM)
    
    // Wait for interface to be ready
    wait(!vif.sb_reset);
    
    // Get header and data
    header = trans.get_header();
    data_payload = trans.data;
    
    // Drive header (64-bit serial packet)
    drive_serial_packet(header);
    
    // Wait minimum 32 bits low between packets
    repeat(32) @(posedge vif.sbtx_clk);
    
    // Drive data if present
    if (trans.has_data) begin
      if (trans.is_64bit) begin
        drive_serial_packet(data_payload);
      end else begin
        // For 32-bit data, pad MSBs with 0
        drive_serial_packet({32'h0, data_payload[31:0]});
      end
      
      // Wait minimum 32 bits low after data
      repeat(32) @(posedge vif.sbtx_clk);
    end
  endtask
  
  // Drive a 64-bit serial packet on TX path
  virtual task drive_serial_packet(bit [63:0] packet);
    // Generate TX clock and drive data
    for (int i = 0; i < 64; i++) begin
      @(posedge vif.sbtx_clk);
      vif.sbtx_data <= packet[i];
    end
    
    // Drive low after packet
    @(posedge vif.sbtx_clk);
    vif.sbtx_data <= 1'b0;
  endtask
  
  // Additional utility tasks
  
  // Task to drive idle state (all zeros)
  virtual task drive_idle(int num_cycles = 32);
    repeat(num_cycles) begin
      @(posedge vif.sbtx_clk);
      vif.sbtx_data <= 1'b0;
    end
  endtask
  
  // Task to wait for specific number of clock cycles
  virtual task wait_cycles(int num_cycles);
    repeat(num_cycles) @(posedge vif.sbtx_clk);
  endtask
  
  // Task to check if interface is ready for transmission
  virtual task wait_for_ready();
    // Wait for reset to be released
    wait(!vif.sb_reset);
    
    // Ensure we start from idle state
    while (vif.sbtx_data !== 1'b0) begin
      @(posedge vif.sbtx_clk);
    end
  endtask
  
  // Function to get current TX clock state
  virtual function bit get_tx_clk_state();
    return vif.sbtx_clk;
  endfunction
  
  // Function to get current TX data state
  virtual function bit get_tx_data_state();
    return vif.sbtx_data;
  endfunction
  
  // Task for debug - drive specific pattern
  virtual task drive_debug_pattern(bit [63:0] pattern, string pattern_name = "DEBUG");
    `uvm_info("SIDEBAND_DRIVER", $sformatf("Driving debug pattern %s: 0x%016h", pattern_name, pattern), UVM_LOW)
    drive_serial_packet(pattern);
  endtask
  
endclass