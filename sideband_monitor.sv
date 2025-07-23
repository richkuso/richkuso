// UCIe Sideband Monitor Class
// Captures serial data from RX path and reconstructs transactions

class sideband_monitor extends uvm_monitor;
  `uvm_component_utils(sideband_monitor)
  
  virtual sideband_interface vif;
  uvm_analysis_port #(sideband_transaction) analysis_port;
  
  // Configuration options
  bit enable_protocol_checking = 1;
  bit enable_packet_logging = 1;
  
  function new(string name = "sideband_monitor", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual sideband_interface)::get(this, "", "vif", vif))
      `uvm_fatal("MONITOR", "Virtual interface not found")
    analysis_port = new("analysis_port", this);
    
    // Get configuration options
    void'(uvm_config_db#(bit)::get(this, "", "enable_protocol_checking", enable_protocol_checking));
    void'(uvm_config_db#(bit)::get(this, "", "enable_packet_logging", enable_packet_logging));
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    sideband_transaction trans;
    bit [63:0] header, data_payload;
    
    forever begin
      // Wait for start of packet (RX data goes high)
      wait_for_packet_start();
      
      // Capture header
      header = capture_serial_packet();
      
      // Create transaction from header
      trans = decode_header(header);
      
      // Wait for gap between packets
      wait_for_packet_gap();
      
      // Capture data if present
      if (trans.has_data) begin
        data_payload = capture_serial_packet();
        if (trans.is_64bit)
          trans.data = data_payload;
        else
          trans.data = {32'h0, data_payload[31:0]};
        
        // Recalculate data parity
        trans.calculate_parity();
        
        wait_for_packet_gap();
      end
      
      // Perform protocol checking
      if (enable_protocol_checking) begin
        check_transaction_validity(trans);
      end
      
      if (enable_packet_logging) begin
        `uvm_info("SIDEBAND_MONITOR", trans.convert2string(), UVM_MEDIUM)
      end
      
      analysis_port.write(trans);
    end
  endtask
  
  // Wait for start of packet on RX path
  virtual task wait_for_packet_start();
    // Wait for data to go high (start of packet)
    wait(vif.sbrx_data == 1'b1);
    @(vif.monitor_cb); // Sync to clock edge
  endtask
  
  // Wait for minimum gap between packets (32 bits low) on RX path
  virtual task wait_for_packet_gap();
    int low_count = 0;
    while (low_count < 32) begin
      @(vif.monitor_cb);
      if (vif.monitor_cb.sbrx_data == 1'b0)
        low_count++;
      else
        low_count = 0;
    end
  endtask
  
  // Capture a 64-bit serial packet from RX path using clocking block
  virtual function bit [63:0] capture_serial_packet();
    bit [63:0] packet;
    for (int i = 0; i < 64; i++) begin
      @(vif.monitor_cb);
      packet[i] = vif.monitor_cb.sbrx_data;
    end
    return packet;
  endfunction
  
  // Decode header into transaction
  virtual function sideband_transaction decode_header(bit [63:0] header);
    sideband_transaction trans;
    bit [31:0] phase0, phase1;
    
    trans = sideband_transaction::type_id::create("monitored_trans");
    
    // Split header into phases
    phase0 = header[31:0];
    phase1 = header[63:32];
    
    // Decode Phase 0
    trans.srcid = phase0[31:29];
    trans.tag = phase0[25:21];
    trans.be = phase0[20:13];
    trans.ep = phase0[7];
    trans.opcode = sideband_opcode_e'(phase0[6:2]);
    
    // Decode Phase 1
    trans.dp = phase1[31];
    trans.cp = phase1[30];
    trans.cr = phase1[29];
    trans.dstid = phase1[24:22];
    
    // Update packet information
    trans.update_packet_info();
    
    // Decode address or status
    if (trans.pkt_type == PKT_COMPLETION)
      trans.status = phase1[15:0];
    else
      trans.addr = {8'h0, phase1[15:0]};
    
    return trans;
  endfunction
  
  // Protocol checking function
  virtual function void check_transaction_validity(sideband_transaction trans);
    bit parity_error = 0;
    bit addr_alignment_error = 0;
    bit be_error = 0;
    
    // Check parity
    bit expected_cp, expected_dp;
    bit [63:0] header_bits;
    
    header_bits = {trans.srcid, 2'b00, trans.tag, trans.be, 3'b000, trans.ep, trans.opcode, 
                   1'b0, 1'b0, trans.cr, 4'b0000, trans.dstid, 
                   (trans.pkt_type == PKT_COMPLETION) ? trans.status : trans.addr[15:0]};
    expected_cp = ^header_bits;
    
    if (trans.has_data) begin
      if (trans.is_64bit)
        expected_dp = ^trans.data;
      else
        expected_dp = ^trans.data[31:0];
    end else begin
      expected_dp = 1'b0;
    end
    
    if (trans.cp !== expected_cp) begin
      `uvm_error("MONITOR", $sformatf("Control parity error: expected=%0b, actual=%0b", expected_cp, trans.cp))
      parity_error = 1;
    end
    
    if (trans.dp !== expected_dp) begin
      `uvm_error("MONITOR", $sformatf("Data parity error: expected=%0b, actual=%0b", expected_dp, trans.dp))
      parity_error = 1;
    end
    
    // Check address alignment
    if (trans.is_64bit && (trans.addr[2:0] != 3'b000)) begin
      `uvm_error("MONITOR", $sformatf("64-bit address alignment error: addr=0x%0h", trans.addr))
      addr_alignment_error = 1;
    end else if (!trans.is_64bit && trans.opcode inside {MEM_READ_32B, MEM_WRITE_32B, DMS_READ_32B, DMS_WRITE_32B, CFG_READ_32B, CFG_WRITE_32B}) begin
      if (trans.addr[1:0] != 2'b00) begin
        `uvm_error("MONITOR", $sformatf("32-bit address alignment error: addr=0x%0h", trans.addr))
        addr_alignment_error = 1;
      end
    end
    
    // Check byte enables for 32-bit operations
    if (trans.opcode inside {MEM_READ_32B, MEM_WRITE_32B, DMS_READ_32B, DMS_WRITE_32B, CFG_READ_32B, CFG_WRITE_32B}) begin
      if (trans.be[7:4] != 4'b0000) begin
        `uvm_error("MONITOR", $sformatf("32-bit byte enable error: be=0x%0h", trans.be))
        be_error = 1;
      end
    end
    
    // Report overall status
    if (!parity_error && !addr_alignment_error && !be_error) begin
      `uvm_info("MONITOR", "Transaction passed all protocol checks", UVM_DEBUG)
    end
  endfunction
  
  // Additional utility functions
  
  // Function to get current RX clock state
  virtual function bit get_rx_clk_state();
    return vif.sbrx_clk;
  endfunction
  
  // Function to get current RX data state
  virtual function bit get_rx_data_state();
    return vif.sbrx_data;
  endfunction
  
  // Task to wait for specific number of RX clock cycles
  virtual task wait_rx_cycles(int num_cycles);
    repeat(num_cycles) @(vif.monitor_cb);
  endtask
  
  // Function to check if RX interface is idle
  virtual function bit is_rx_idle();
    return (vif.sbrx_data == 1'b0);
  endfunction
  
  // Task to wait for RX idle condition
  virtual task wait_for_rx_idle();
    while (vif.sbrx_data !== 1'b0) begin
      @(vif.monitor_cb);
    end
  endtask
  
  // Statistics collection
  int packet_count = 0;
  int error_count = 0;
  int [string] opcode_count;
  
  // Function to update statistics
  virtual function void update_statistics(sideband_transaction trans);
    packet_count++;
    
    // Count by opcode
    string opcode_name = trans.opcode.name();
    if (opcode_count.exists(opcode_name))
      opcode_count[opcode_name]++;
    else
      opcode_count[opcode_name] = 1;
  endfunction
  
  // Function to print statistics
  virtual function void print_statistics();
    `uvm_info("MONITOR", $sformatf("Total packets monitored: %0d", packet_count), UVM_LOW)
    `uvm_info("MONITOR", $sformatf("Total errors detected: %0d", error_count), UVM_LOW)
    
    foreach (opcode_count[opcode]) begin
      `uvm_info("MONITOR", $sformatf("Opcode %s: %0d packets", opcode, opcode_count[opcode]), UVM_MEDIUM)
    end
  endfunction
  
  // End of test reporting
  virtual function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    print_statistics();
  endfunction
  
endclass