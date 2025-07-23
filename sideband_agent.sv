// UCIe Sideband Agent Class
// Container that manages driver, monitor, and sequencer components

class sideband_agent extends uvm_agent;
  `uvm_component_utils(sideband_agent)
  
  sideband_driver    driver;
  sideband_monitor   monitor;
  sideband_sequencer sequencer;
  
  // Configuration options
  bit enable_driver_debug = 0;
  bit enable_monitor_checking = 1;
  bit enable_coverage = 1;
  
  function new(string name = "sideband_agent", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    // Get configuration options
    void'(uvm_config_db#(bit)::get(this, "", "enable_driver_debug", enable_driver_debug));
    void'(uvm_config_db#(bit)::get(this, "", "enable_monitor_checking", enable_monitor_checking));
    void'(uvm_config_db#(bit)::get(this, "", "enable_coverage", enable_coverage));
    
    // Always create monitor
    monitor = sideband_monitor::type_id::create("monitor", this);
    
    // Set monitor configuration
    uvm_config_db#(bit)::set(this, "monitor", "enable_protocol_checking", enable_monitor_checking);
    
    // Create driver and sequencer only if agent is active
    if (get_is_active() == UVM_ACTIVE) begin
      driver = sideband_driver::type_id::create("driver", this);
      sequencer = sideband_sequencer::type_id::create("sequencer", this);
      
      `uvm_info("AGENT", "Created active sideband agent", UVM_MEDIUM)
    end else begin
      `uvm_info("AGENT", "Created passive sideband agent", UVM_MEDIUM)
    end
  endfunction
  
  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    
    if (get_is_active() == UVM_ACTIVE) begin
      driver.seq_item_port.connect(sequencer.seq_item_export);
      `uvm_info("AGENT", "Connected driver to sequencer", UVM_HIGH)
    end
  endfunction
  
  // Additional utility functions
  
  // Function to get agent statistics
  virtual function void get_agent_stats(output int packet_count, output int error_count);
    if (monitor != null) begin
      packet_count = monitor.packet_count;
      error_count = monitor.error_count;
    end else begin
      packet_count = 0;
      error_count = 0;
    end
  endfunction
  
  // Task to wait for agent to be ready
  virtual task wait_for_ready();
    if (get_is_active() == UVM_ACTIVE && driver != null) begin
      driver.wait_for_ready();
    end
  endtask
  
  // Function to check if agent is idle
  virtual function bit is_idle();
    if (monitor != null) begin
      return monitor.is_rx_idle();
    end
    return 1'b1;
  endfunction
  
  // Task to drive idle state (active agents only)
  virtual task drive_idle(int num_cycles = 32);
    if (get_is_active() == UVM_ACTIVE && driver != null) begin
      driver.drive_idle(num_cycles);
    end else begin
      `uvm_warning("AGENT", "Cannot drive idle - agent is passive or driver not available")
    end
  endtask
  
  // Function to enable/disable protocol checking at runtime
  virtual function void set_protocol_checking(bit enable);
    enable_monitor_checking = enable;
    if (monitor != null) begin
      monitor.enable_protocol_checking = enable;
      `uvm_info("AGENT", $sformatf("Protocol checking %s", enable ? "enabled" : "disabled"), UVM_LOW)
    end
  endfunction
  
  // Function to enable/disable packet logging at runtime
  virtual function void set_packet_logging(bit enable);
    if (monitor != null) begin
      monitor.enable_packet_logging = enable;
      `uvm_info("AGENT", $sformatf("Packet logging %s", enable ? "enabled" : "disabled"), UVM_LOW)
    end
  endfunction
  
  // Debug function to get interface states
  virtual function void get_interface_states(output bit tx_clk, output bit tx_data, 
                                           output bit rx_clk, output bit rx_data);
    if (get_is_active() == UVM_ACTIVE && driver != null) begin
      tx_clk = driver.get_tx_clk_state();
      tx_data = driver.get_tx_data_state();
    end else begin
      tx_clk = 1'b0;
      tx_data = 1'b0;
    end
    
    if (monitor != null) begin
      rx_clk = monitor.get_rx_clk_state();
      rx_data = monitor.get_rx_data_state();
    end else begin
      rx_clk = 1'b0;
      rx_data = 1'b0;
    end
  endfunction
  
  // Report phase - print agent summary
  virtual function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    
    `uvm_info("AGENT", "=== Sideband Agent Summary ===", UVM_LOW)
    `uvm_info("AGENT", $sformatf("Agent Mode: %s", get_is_active() == UVM_ACTIVE ? "ACTIVE" : "PASSIVE"), UVM_LOW)
    `uvm_info("AGENT", $sformatf("Protocol Checking: %s", enable_monitor_checking ? "ENABLED" : "DISABLED"), UVM_LOW)
    `uvm_info("AGENT", $sformatf("Coverage Collection: %s", enable_coverage ? "ENABLED" : "DISABLED"), UVM_LOW)
    
    if (monitor != null) begin
      int pkt_count, err_count;
      get_agent_stats(pkt_count, err_count);
      `uvm_info("AGENT", $sformatf("Packets Processed: %0d", pkt_count), UVM_LOW)
      `uvm_info("AGENT", $sformatf("Errors Detected: %0d", err_count), UVM_LOW)
    end
    
    `uvm_info("AGENT", "=== End Agent Summary ===", UVM_LOW)
  endfunction
  
endclass