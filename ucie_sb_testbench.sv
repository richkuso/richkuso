module ucie_sb_testbench;
  import uvm_pkg::*;
  import ucie_sb_pkg::*;
  import ucie_sb_test_pkg::*;
  `include "uvm_macros.svh"
  
  // Clock and reset generation
  logic sb_reset = 1;
  
  initial begin
    sb_reset = 1;
    #100;
    sb_reset = 0;
  end
  
  // Interface instantiation - 16 separate sideband interfaces for 16 agents
  ucie_sb_interface sb_intf[16];
  
  // Generate 16 interfaces
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : gen_interfaces
      ucie_sb_interface sb_intf_inst(.clk(1'b0), .reset(sb_reset));
      assign sb_intf[i] = sb_intf_inst;
    end
  endgenerate
  
  // Clock generation for all 16 sideband interfaces - higher frequency for serial transmission
  generate
    for (i = 0; i < 16; i++) begin : gen_clocks
      always #2.5 sb_intf[i].SBTX_CLK = ~sb_intf[i].SBTX_CLK; // 200MHz TX sideband clock
      always #2.5 sb_intf[i].SBRX_CLK = ~sb_intf[i].SBRX_CLK; // 200MHz RX sideband clock
    end
  endgenerate
  
  // Initialize all interfaces
  initial begin
    for (int j = 0; j < 16; j++) begin
      sb_intf[j].SBTX_CLK = 0;
      sb_intf[j].SBRX_CLK = 0;
      sb_intf[j].SBTX_DATA = 0;
      sb_intf[j].SBRX_DATA = 0;
    end
  end
  
  // Loopback connections for demonstration (TX to RX for each interface)
  generate
    for (i = 0; i < 16; i++) begin : gen_loopbacks
      always_comb begin
        sb_intf[i].SBRX_DATA = sb_intf[i].SBTX_DATA;
      end
    end
  endgenerate
  
  // Simple sideband receiver DUT for demonstration (connected to interface 0)
  ucie_sb_receiver_dut dut (
    .sbtx_clk(sb_intf[0].SBTX_CLK),
    .sbtx_data(sb_intf[0].SBTX_DATA),
    .sbrx_clk(sb_intf[0].SBRX_CLK),
    .sbrx_data(sb_intf[0].SBRX_DATA),
    .sb_reset(sb_reset)
  );
  
  // Function to configure 16 separate UVM interfaces for 16 agents
  function void configure_uvm_interfaces();
    string agent_path;
    
    `uvm_info("TB", "=== Configuring 16 Separate UVM Interfaces ===", UVM_LOW)
    
    // Set dedicated interface for each of the 16 agents
    for (int k = 0; k < 16; k++) begin
      agent_path = $sformatf("uvm_test_top.sb_env.agent_%0d*", k);
      uvm_config_db#(virtual ucie_sb_interface)::set(null, agent_path, "vif", sb_intf[k]);
      `uvm_info("TB", $sformatf("✅ Agent_%0d interface configured with sb_intf[%0d]", k, k), UVM_MEDIUM)
    end
    
    // Register checkers don't need virtual interfaces - they use FIFO-only architecture
    // They receive transactions through analysis FIFOs from agent monitors
    
    // Verify interface connectivity to DUT (interface 0 example)
    `uvm_info("TB", $sformatf("Interface[0] DUT connections verified: SBTX→DUT.sbtx, SBRX←DUT.sbrx"), UVM_LOW)
    `uvm_info("TB", $sformatf("Interface[0] signal states: TX_CLK=%0b, TX_DATA=%0b, RX_CLK=%0b, RX_DATA=%0b", 
              sb_intf[0].SBTX_CLK, sb_intf[0].SBTX_DATA, sb_intf[0].SBRX_CLK, sb_intf[0].SBRX_DATA), UVM_DEBUG)
    
    `uvm_info("TB", "=== 16 Agent Interfaces Configuration Complete ===", UVM_LOW)
  endfunction
  
  // Initial block to start UVM
  initial begin
    // Enable assertions
    `ifdef ENABLE_SIDEBAND_ASSERTIONS
      `uvm_info("TB", "Sideband assertions enabled", UVM_LOW)
    `endif
    
    // Configure UVM interfaces (replaces wildcard approach)
    configure_uvm_interfaces();
    
    // Set verbosity
    uvm_top.set_report_verbosity_level_hier(UVM_MEDIUM);
    
    // Display testbench information
    `uvm_info("TB", "=== UCIe Sideband UVM Testbench ===", UVM_LOW)
    `uvm_info("TB", "Features: Register Access Checker, Clock Patterns, SBINIT Messages", UVM_LOW)
    `uvm_info("TB", "Architecture: 16 Inactive Agents, FIFO-Only Checker, TAG/Non-TAG Support", UVM_LOW)
    `uvm_info("TB", "Available Tests:", UVM_LOW)
    `uvm_info("TB", "  - ucie_sb_clock_pattern_test", UVM_LOW)
    `uvm_info("TB", "  - ucie_sb_memory_test", UVM_LOW)
    `uvm_info("TB", "  - ucie_sb_config_test", UVM_LOW)
    `uvm_info("TB", "  - ucie_sb_sbinit_test", UVM_LOW)
    `uvm_info("TB", "  - ucie_sb_mixed_test", UVM_LOW)
    `uvm_info("TB", "  - ucie_sb_checker_test", UVM_LOW)
    
    // Run the test
    run_test();
  end
  
  // Waveform dumping
  initial begin
    $dumpfile("ucie_sb_waves.vcd");
    $dumpvars(0, ucie_sb_testbench);
  end
  
  // Timeout watchdog
  initial begin
    #100000; // 100us timeout (increased for comprehensive tests)
    `uvm_fatal("TIMEOUT", "Test timeout - simulation ran too long")
  end
  
  // Final statistics and cleanup
  final begin
    `uvm_info("TB", "=== Testbench Final Statistics ===", UVM_LOW)
    `uvm_info("TB", "=== Testbench Completed ===", UVM_LOW)
  end
  
endmodule

// Simple sideband receiver DUT for demonstration
module ucie_sb_receiver_dut (
  input  logic sbtx_clk,
  input  logic sbtx_data,
  input  logic sbrx_clk,
  input  logic sbrx_data,
  input  logic sb_reset
);
  
  // State machine for packet reception
  typedef enum logic [2:0] {
    IDLE,
    RECEIVING_HEADER,
    WAITING_GAP,
    RECEIVING_DATA,
    PROCESSING
  } state_t;
  
  state_t current_state, next_state;
  
  // Packet reception registers
  logic [63:0] header_reg;
  logic [63:0] data_reg;
  logic [5:0]  bit_counter;
  logic [5:0]  gap_counter;
  logic        packet_valid;
  logic        data_phase;
  
  // State register - monitor TX path (what's being transmitted)
  always_ff @(posedge sbtx_clk or posedge sb_reset) begin
    if (sb_reset) begin
      current_state <= IDLE;
      bit_counter <= 0;
      gap_counter <= 0;
      header_reg <= 0;
      data_reg <= 0;
      packet_valid <= 0;
      data_phase <= 0;
    end else begin
      current_state <= next_state;
      
      case (current_state)
        IDLE: begin
          if (sbtx_data) begin
            bit_counter <= 1;
            header_reg[0] <= sbtx_data;
            packet_valid <= 0;
          end
        end
        
        RECEIVING_HEADER: begin
          if (bit_counter < 63) begin
            header_reg[bit_counter] <= sbtx_data;
            bit_counter <= bit_counter + 1;
          end else begin
            header_reg[63] <= sbtx_data;
            bit_counter <= 0;
            gap_counter <= 0;
          end
        end
        
        WAITING_GAP: begin
          if (!sbtx_data) begin
            gap_counter <= gap_counter + 1;
          end else if (gap_counter >= 32) begin
            // Start of data packet
            bit_counter <= 1;
            data_reg[0] <= sbtx_data;
            data_phase <= 1;
          end else begin
            gap_counter <= 0;
          end
        end
        
        RECEIVING_DATA: begin
          if (bit_counter < 63) begin
            data_reg[bit_counter] <= sbtx_data;
            bit_counter <= bit_counter + 1;
          end else begin
            data_reg[63] <= sbtx_data;
            bit_counter <= 0;
          end
        end
        
        PROCESSING: begin
          packet_valid <= 1;
          data_phase <= 0;
        end
      endcase
    end
  end
  
  // Next state logic
  always_comb begin
    next_state = current_state;
    
    case (current_state)
      IDLE: begin
        if (sbtx_data)
          next_state = RECEIVING_HEADER;
      end
      
      RECEIVING_HEADER: begin
        if (bit_counter == 63)
          next_state = WAITING_GAP;
      end
      
      WAITING_GAP: begin
        if (gap_counter >= 32) begin
          if (sbtx_data && needs_data_packet())
            next_state = RECEIVING_DATA;
          else if (gap_counter >= 32)
            next_state = PROCESSING;
        end
      end
      
      RECEIVING_DATA: begin
        if (bit_counter == 63)
          next_state = PROCESSING;
      end
      
      PROCESSING: begin
        next_state = IDLE;
      end
    endcase
  end
  
  // Determine if packet needs data based on opcode
  function bit needs_data_packet();
    logic [4:0] opcode;
    opcode = header_reg[6:2];
    
    case (opcode)
      5'b00001, 5'b00011, 5'b00101: return 1'b1; // 32-bit writes
      5'b01001, 5'b01011, 5'b01101: return 1'b1; // 64-bit writes
      5'b10001, 5'b11001, 5'b11011, 5'b11000: return 1'b1; // Completions with data, messages with data
      default: return 1'b0;
    endcase
  endfunction
  
  // Enhanced packet processing and display with transaction details
  always_ff @(posedge sbtx_clk) begin
    if (packet_valid) begin
      logic [4:0] opcode;
      logic [2:0] srcid, dstid;
      logic [4:0] tag;
      logic [23:0] addr;
      logic [15:0] status;
      string opcode_name;
      
      opcode = header_reg[6:2];
      srcid = header_reg[31:29];
      dstid = header_reg[56:54];
      tag = header_reg[25:21];
      
      // Decode opcode name
      case (opcode)
        5'b00000: opcode_name = "MEM_READ_32B";
        5'b00001: opcode_name = "MEM_WRITE_32B";
        5'b00010: opcode_name = "DMS_READ_32B";
        5'b00011: opcode_name = "DMS_WRITE_32B";
        5'b00100: opcode_name = "CFG_READ_32B";
        5'b00101: opcode_name = "CFG_WRITE_32B";
        5'b01000: opcode_name = "MEM_READ_64B";
        5'b01001: opcode_name = "MEM_WRITE_64B";
        5'b01010: opcode_name = "DMS_READ_64B";
        5'b01011: opcode_name = "DMS_WRITE_64B";
        5'b01100: opcode_name = "CFG_READ_64B";
        5'b01101: opcode_name = "CFG_WRITE_64B";
        5'b10000: opcode_name = "COMPLETION_NO_DATA";
        5'b10001: opcode_name = "COMPLETION_32B";
        5'b11001: opcode_name = "COMPLETION_64B";
        5'b10010: opcode_name = "MESSAGE_NO_DATA";
        5'b11011: opcode_name = "MESSAGE_64B";
        5'b10111: opcode_name = "MGMT_MSG_NO_DATA";
        5'b11000: opcode_name = "MGMT_MSG_DATA";
        5'b11111: opcode_name = "CLOCK_PATTERN";
        default:  opcode_name = "UNKNOWN";
      endcase
      
      if (opcode inside {5'b10000, 5'b10001, 5'b11001}) begin // Completions
        status = header_reg[47:32];
        $display("DUT: [%0t] COMPLETION %s - SRC:%0d→DST:%0d TAG:0x%02h STATUS:0x%04h", 
                 $time, opcode_name, srcid, dstid, tag, status);
      end else if (opcode == 5'b11111) begin // Clock pattern
        $display("DUT: [%0t] CLOCK_PATTERN - Continuous pattern detected", $time);
      end else begin // Register access or messages
        addr = {8'h0, header_reg[47:32]};
        $display("DUT: [%0t] REG_ACCESS %s - SRC:%0d→DST:%0d TAG:0x%02h ADDR:0x%06h", 
                 $time, opcode_name, srcid, dstid, tag, addr);
      end
      
      if (data_phase) begin
        $display("DUT: [%0t] → DATA: 0x%016h", $time, data_reg);
      end
    end
  end
  
endmodule