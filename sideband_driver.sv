// UCIe Sideband Driver Class
// Converts UVM transactions to serial bit stream on TX path

// Driver configuration class
class sideband_driver_config extends uvm_object;
  `uvm_object_utils(sideband_driver_config)
  
  // Clock timing parameters
  real clock_period = 1.25;       // ns (800MHz default)
  real clock_high_time = 0.625;   // ns (50% duty cycle)
  real clock_low_time = 0.625;    // ns (50% duty cycle)
  
  // Protocol parameters
  int min_gap_cycles = 32;        // Minimum gap between packets
  bit enable_protocol_checking = 1;
  bit enable_statistics = 1;
  
  // Timing parameters
  real setup_time = 0.1;          // ns - data setup time before clock edge
  real hold_time = 0.1;           // ns - data hold time after clock edge
  real gap_time = 0.0;            // ns - additional time during gaps
  
  function new(string name = "sideband_driver_config");
    super.new(name);
  endfunction
  
  // Helper function to set frequency
  function void set_frequency(real freq_hz);
    clock_period = (1.0 / freq_hz) * 1e9; // Convert to ns
    clock_high_time = clock_period / 2.0;
    clock_low_time = clock_period / 2.0;
    `uvm_info("CONFIG", $sformatf("Set frequency to %.1f MHz (period=%.3f ns)", freq_hz/1e6, clock_period), UVM_LOW)
  endfunction
  
  // Helper function to set duty cycle
  function void set_duty_cycle(real duty_percent);
    clock_high_time = clock_period * (duty_percent / 100.0);
    clock_low_time = clock_period - clock_high_time;
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
    
    if (cfg.clock_period <= 0) begin
      `uvm_error("DRIVER", "Invalid clock_period - must be positive")
      cfg.clock_period = 1.25; // Default to 800MHz
    end
    
    if (cfg.clock_high_time + cfg.clock_low_time != cfg.clock_period) begin
      `uvm_warning("DRIVER", "clock_high_time + clock_low_time != clock_period, adjusting...")
      cfg.clock_low_time = cfg.clock_period - cfg.clock_high_time;
    end
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    sideband_transaction trans;
    
    // Wait for reset to be released before starting
    wait_for_reset_release();
    
    // Initialize TX signals to idle state
    vif.SBTX_CLK = 0;
    vif.SBTX_DATA = 0;
    
    `uvm_info("DRIVER", "Sideband driver ready - clock and data will be generated per transaction", UVM_LOW)
    
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
  
  // Drive transaction with source-synchronous clock and data
  virtual task drive_transaction(sideband_transaction trans);
    bit [63:0] header_packet;
    bit [63:0] data_packet;
    
    if (vif.sb_reset) begin
      `uvm_warning("DRIVER", "Cannot drive transaction during reset")
      return;
    end
    
    `uvm_info("DRIVER", {"Driving transaction: ", trans.convert2string()}, UVM_MEDIUM)
    
    // Calculate and set parity bits
    trans.calculate_parity();
    
    // Pack transaction header into 64-bit packet
    header_packet = trans.get_header();
    
    // Drive the header packet with source-synchronous clock
    if (drive_packet_with_clock(header_packet)) begin
      last_packet_time = $time;
      `uvm_info("DRIVER", $sformatf("Successfully drove header packet: 0x%016h", header_packet), UVM_HIGH)
    end else begin
      `uvm_error("DRIVER", "Failed to drive header packet")
      errors_detected++;
      return;
    end
    
    // Drive gap after header
    drive_gap();
    
    // Drive data packet if transaction has data
    if (trans.has_data) begin
      // Pack data according to transaction width
      if (trans.is_64bit) begin
        data_packet = trans.data;
      end else begin
        // For 32-bit data, pad MSBs with 0
        data_packet = {32'h0, trans.data[31:0]};
      end
      
      `uvm_info("DRIVER", $sformatf("Driving data packet: 0x%016h", data_packet), UVM_HIGH)
      
      // Drive the data packet
      if (drive_packet_with_clock(data_packet)) begin
        `uvm_info("DRIVER", "Successfully drove data packet", UVM_HIGH)
      end else begin
        `uvm_error("DRIVER", "Failed to drive data packet")
        errors_detected++;
        return;
      end
      
      // Drive gap after data
      drive_gap();
    end
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
  

  
  // Drive a 64-bit packet with source-synchronous clock generation
  virtual function bit drive_packet_with_clock(bit [63:0] packet);
    if (vif.sb_reset) begin
      `uvm_warning("DRIVER", "Cannot drive packet during reset")
      return 0;
    end
    
    `uvm_info("DRIVER", $sformatf("Driving 64-bit packet with clock: 0x%016h", packet), UVM_HIGH)
    
    // Drive each bit with source-synchronous clock
    for (int i = 0; i < PACKET_SIZE_BITS; i++) begin
      // Clock low phase - setup data
      vif.SBTX_CLK = 1'b0;
      #(cfg.setup_time * 1ns);
      vif.SBTX_DATA = packet[i];
      #(cfg.clock_low_time * 1ns - cfg.setup_time * 1ns);
      
      // Clock high phase - data is valid
      vif.SBTX_CLK = 1'b1;
      #(cfg.clock_high_time * 1ns);
    end
    
    // Return clock to idle (low) state
    vif.SBTX_CLK = 1'b0;
    
    return 1;
  endfunction
  
  // Drive minimum gap with clock and data low
  virtual task drive_gap(int num_cycles = MIN_GAP_CYCLES);
    `uvm_info("DRIVER", $sformatf("Driving %0d cycle gap (clock and data low)", num_cycles), UVM_DEBUG)
    
    // During gap: both clock and data are low
    vif.SBTX_CLK = 1'b0;
    vif.SBTX_DATA = 1'b0;
    
    // Hold for the gap duration (minimum 32 clock periods)
    #(num_cycles * cfg.clock_period * 1ns + cfg.gap_time * 1ns);
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
  

  
  // Function to get current TX clock state
  virtual function bit get_tx_clk_state();
    return vif.SBTX_CLK;
  endfunction
  
  // Function to get current TX data state
  virtual function bit get_tx_data_state();
    return vif.SBTX_DATA;
  endfunction
  
  // Task for debug - drive specific pattern with clock
  virtual task drive_debug_pattern(bit [63:0] pattern, string pattern_name = "DEBUG");
    `uvm_info("SIDEBAND_DRIVER", $sformatf("Driving debug pattern %s: 0x%016h", pattern_name, pattern), UVM_LOW)
    void'(drive_packet_with_clock(pattern));
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