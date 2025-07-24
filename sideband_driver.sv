// UCIe Sideband Driver Class
// Converts UVM transactions to serial bit stream on TX path

// Driver configuration class
class sideband_driver_config extends uvm_object;
  `uvm_object_utils(sideband_driver_config)
  
  int min_gap_cycles = 32;
  bit enable_protocol_checking = 1;
  bit enable_statistics = 1;
  real setup_time = 0.1; // ns
  real hold_time = 0.1;   // ns
  
  function new(string name = "sideband_driver_config");
    super.new(name);
  endfunction
endclass

class sideband_driver extends uvm_driver #(sideband_transaction);
  `uvm_component_utils(sideband_driver)
  
  // Configuration and interface
  virtual sideband_interface vif;
  sideband_driver_config cfg;
  
  // Parameters based on UCIe specification
  parameter int MIN_GAP_CYCLES = 32;
  parameter int PACKET_SIZE_BITS = 64;
  parameter real DEFAULT_CLOCK_PERIOD = 5.0; // 200MHz
  
  // Statistics
  int packets_driven = 0;
  int bits_driven = 0;
  int errors_detected = 0;
  time last_packet_time;
  

  
  function new(string name = "sideband_driver", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    // Get virtual interface
    if (!uvm_config_db#(virtual sideband_interface)::get(this, "", "vif", vif))
      `uvm_fatal("DRIVER", "Virtual interface not found")
    
    // Get configuration or create default
    if (!uvm_config_db#(sideband_driver_config)::get(this, "", "cfg", cfg)) begin
      cfg = sideband_driver_config::type_id::create("cfg");
      `uvm_info("DRIVER", "Using default driver configuration", UVM_MEDIUM)
    end
    
    // Validate configuration
    if (cfg.min_gap_cycles < 32) begin
      `uvm_warning("DRIVER", $sformatf("min_gap_cycles=%0d is less than UCIe minimum of 32", cfg.min_gap_cycles))
    end
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    sideband_transaction trans;
    
    // Wait for reset to be released before starting
    wait_for_reset_release();
    
    // Ensure clock is running (generated externally)
    wait_for_clock_active();
    
    forever begin
      seq_item_port.get_next_item(trans);
      
      // Validate transaction before driving
      if (validate_transaction(trans)) begin
        drive_transaction(trans);
        update_statistics();
      end else begin
        `uvm_error("DRIVER", {"Invalid transaction: ", trans.convert2string()})
        errors_detected++;
      end
      
      seq_item_port.item_done();
    end
  endtask
  
  // Wait for external clock to be active
  virtual task wait_for_clock_active();
    int clock_toggle_count = 0;
    logic prev_clk_state;
    
    `uvm_info("DRIVER", "Waiting for TX clock to be active...", UVM_MEDIUM)
    
    prev_clk_state = vif.sbtx_clk;
    
    fork
      begin
        // Wait for at least 3 clock toggles to confirm clock is running
        while (clock_toggle_count < 3) begin
          @(vif.sbtx_clk);
          if (vif.sbtx_clk !== prev_clk_state) begin
            clock_toggle_count++;
            prev_clk_state = vif.sbtx_clk;
          end
        end
        `uvm_info("DRIVER", "TX clock confirmed active", UVM_MEDIUM)
      end
      begin
        #1ms; // Timeout
        `uvm_fatal("DRIVER", "TX clock not detected - ensure clock is generated externally")
      end
    join_any
    disable fork;
  endtask
  
  // Enhanced reset handling with timeout
  virtual task wait_for_reset_release();
    fork
      begin
        wait(!vif.sb_reset);
        `uvm_info("DRIVER", "Reset released, driver ready", UVM_MEDIUM)
      end
      begin
        #10ms; // Timeout
        if (vif.sb_reset) 
          `uvm_fatal("DRIVER", "Reset timeout - reset never released")
      end
    join_any
    disable fork;
    
    // Additional settling time after reset
    #100ns;
  endtask
  
  // Transaction validation
  virtual function bit validate_transaction(sideband_transaction trans);
    if (cfg.enable_protocol_checking) begin
      // Check UCIe specification compliance
      
      // Validate srcid encoding (Table 7-4)
      if (!(trans.srcid inside {3'b001, 3'b010, 3'b011})) begin
        `uvm_error("DRIVER", $sformatf("Invalid srcid=0x%0h, must be 001b, 010b, or 011b", trans.srcid))
        return 0;
      end
      
      // Validate dstid encoding based on packet type
      if (trans.pkt_type == PKT_REG_ACCESS) begin
        if (trans.dstid[1:0] != 2'b00) begin
          `uvm_error("DRIVER", $sformatf("Register access dstid[1:0] must be reserved (00b), got 0x%0h", trans.dstid[1:0]))
          return 0;
        end
      end
      
      // Validate address alignment
      if (trans.is_64bit && (trans.addr[2:0] != 3'b000)) begin
        `uvm_error("DRIVER", $sformatf("64-bit request address must be 8-byte aligned, addr=0x%0h", trans.addr))
        return 0;
      end else if (!trans.is_64bit && trans.pkt_type == PKT_REG_ACCESS && (trans.addr[1:0] != 2'b00)) begin
        `uvm_error("DRIVER", $sformatf("32-bit request address must be 4-byte aligned, addr=0x%0h", trans.addr))
        return 0;
      end
      
      // Validate byte enables for 32-bit requests
      if (!trans.is_64bit && trans.pkt_type == PKT_REG_ACCESS && (trans.be[7:4] != 4'b0000)) begin
        `uvm_error("DRIVER", $sformatf("32-bit request BE[7:4] must be reserved (0000b), got 0x%0h", trans.be[7:4]))
        return 0;
      end
    end
    
    return 1;
  endfunction
  
  virtual task drive_transaction(sideband_transaction trans);
    bit [63:0] header;
    bit [63:0] data_payload;
    
    `uvm_info("SIDEBAND_DRIVER", trans.convert2string(), UVM_MEDIUM)
    
    // Ensure we're not in reset
    if (vif.sb_reset) begin
      `uvm_warning("DRIVER", "Attempting to drive during reset")
      return;
    end
    
    // Get header and data
    header = trans.get_header();
    data_payload = trans.data;
    
    // Drive header (64-bit serial packet)
    if (!drive_serial_packet(header)) begin
      `uvm_error("DRIVER", "Failed to drive header packet")
      return;
    end
    
    // Drive gap with actual low data
    drive_gap(cfg.min_gap_cycles);
    
    // Drive data if present
    if (trans.has_data) begin
      if (trans.is_64bit) begin
        if (!drive_serial_packet(data_payload)) begin
          `uvm_error("DRIVER", "Failed to drive 64-bit data packet")
          return;
        end
      end else begin
        // For 32-bit data, pad MSBs with 0
        if (!drive_serial_packet({32'h0, data_payload[31:0]})) begin
          `uvm_error("DRIVER", "Failed to drive 32-bit data packet")
          return;
        end
      end
      
      // Drive gap after data
      drive_gap(cfg.min_gap_cycles);
    end
  endtask
  
  // Drive a 64-bit serial packet on TX path with error checking
  virtual function bit drive_serial_packet(bit [63:0] packet);
    if (vif.sb_reset) begin
      `uvm_warning("DRIVER", "Cannot drive packet during reset")
      return 0;
    end
    
    `uvm_info("DRIVER", $sformatf("Driving 64-bit packet: 0x%016h", packet), UVM_HIGH)
    
    // Drive each bit with proper timing
    for (int i = 0; i < PACKET_SIZE_BITS; i++) begin
      @(posedge vif.sbtx_clk);
      #(cfg.setup_time * 1ns); // Setup time
      vif.sbtx_data <= packet[i];
      #(cfg.hold_time * 1ns);   // Hold time
    end
    
    return 1;
  endfunction
  
  // Drive minimum gap with data low
  virtual task drive_gap(int num_cycles = MIN_GAP_CYCLES);
    `uvm_info("DRIVER", $sformatf("Driving %0d cycle gap", num_cycles), UVM_DEBUG)
    
    repeat(num_cycles) begin
      @(posedge vif.sbtx_clk);
      #(cfg.setup_time * 1ns);
      vif.sbtx_data <= 1'b0;
      #(cfg.hold_time * 1ns);
    end
  endtask
  
  // Update statistics
  virtual function void update_statistics();
    if (cfg.enable_statistics) begin
      packets_driven++;
      bits_driven += PACKET_SIZE_BITS;
      last_packet_time = $time;
    end
  endfunction
  
  // Additional utility tasks
  
  // Task to drive idle state (all zeros)
  virtual task drive_idle(int num_cycles = MIN_GAP_CYCLES);
    `uvm_info("DRIVER", $sformatf("Driving idle for %0d cycles", num_cycles), UVM_DEBUG)
    drive_gap(num_cycles);
  endtask
  
  // Task to wait for specific number of clock cycles
  virtual task wait_cycles(int num_cycles);
    repeat(num_cycles) @(posedge vif.sbtx_clk);
  endtask
  
  // Task to check if interface is ready for transmission
  virtual task wait_for_ready();
    wait_for_reset_release();
    
    // Ensure we start from idle state
    while (vif.sbtx_data !== 1'b0) begin
      @(posedge vif.sbtx_clk);
    end
    `uvm_info("DRIVER", "Interface ready for transmission", UVM_MEDIUM)
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
    void'(drive_serial_packet(pattern));
    drive_gap();
  endtask
  

  
  // Get driver statistics
  virtual function void get_statistics(output int pkts, output int bits, output int errs, output time last_time);
    pkts = packets_driven;
    bits = bits_driven;
    errs = errors_detected;
    last_time = last_packet_time;
  endfunction
  
  // Report phase - print statistics
  virtual function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    
    if (cfg.enable_statistics) begin
      `uvm_info("DRIVER", "=== Sideband Driver Statistics ===", UVM_LOW)
      `uvm_info("DRIVER", $sformatf("Packets Driven: %0d", packets_driven), UVM_LOW)
      `uvm_info("DRIVER", $sformatf("Bits Driven: %0d", bits_driven), UVM_LOW)
      `uvm_info("DRIVER", $sformatf("Errors Detected: %0d", errors_detected), UVM_LOW)
      `uvm_info("DRIVER", $sformatf("Last Packet Time: %0t", last_packet_time), UVM_LOW)
      
      if (packets_driven > 0) begin
        real avg_rate = (bits_driven * 1.0) / ($time / 1ns) * 1e9; // bits per second
        `uvm_info("DRIVER", $sformatf("Average Bit Rate: %.2f Mbps", avg_rate / 1e6), UVM_LOW)
      end
      
      `uvm_info("DRIVER", "=== End Driver Statistics ===", UVM_LOW)
    end
  endfunction
  
  // Final phase - cleanup
  virtual function void final_phase(uvm_phase phase);
    super.final_phase(phase);
    // Driver cleanup if needed
  endfunction
  
endclass