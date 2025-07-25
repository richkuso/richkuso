module ucie_sb_testbench;
  import uvm_pkg::*;
  import ucie_sb_pkg::*;
  `include "uvm_macros.svh"
  
  // Clock and reset generation
  logic sb_reset = 1;
  
  initial begin
    sb_reset = 1;
    #100;
    sb_reset = 0;
  end
  
  // Interface instantiation
  ucie_sb_interface sb_intf(sb_reset);
  
  // Clock generation for sideband TX and RX - higher frequency for serial transmission
  always #2.5 sb_intf.SBTX_CLK = ~sb_intf.SBTX_CLK; // 200MHz TX sideband clock
  always #2.5 sb_intf.SBRX_CLK = ~sb_intf.SBRX_CLK; // 200MHz RX sideband clock
  
  initial begin
    sb_intf.SBTX_CLK = 0;
    sb_intf.SBRX_CLK = 0;
    sb_intf.SBTX_DATA = 0;
    sb_intf.SBRX_DATA = 0;
  end
  
  // Loopback connection for demonstration (TX to RX)
  always_comb begin
    sb_intf.SBRX_DATA = sb_intf.SBTX_DATA;
  end
  
  // Simple sideband receiver DUT for demonstration
  ucie_sb_receiver_dut dut (
    .SBTX_CLK(sb_intf.SBTX_CLK),
    .SBTX_DATA(sb_intf.SBTX_DATA),
    .SBRX_CLK(sb_intf.SBRX_CLK),
    .SBRX_DATA(sb_intf.SBRX_DATA),
    .sb_reset(sb_reset)
  );
  
  // UVM Environment
  class ucie_sb_env extends uvm_env;
    `uvm_component_utils(ucie_sb_env)
    
    ucie_sb_agent agent;
    
    function new(string name = "ucie_sb_env", uvm_component parent = null);
      super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      agent = ucie_sb_agent::type_id::create("agent", this);
    endfunction
  endclass
  
  // Base test class
  class ucie_sb_base_test extends uvm_test;
    `uvm_component_utils(ucie_sb_base_test)
    
    ucie_sb_env env;
    
    function new(string name = "ucie_sb_base_test", uvm_component parent = null);
      super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      
      // Create environment
      env = ucie_sb_env::type_id::create("env", this);
      
      // Configure the agent as active
      uvm_config_db#(uvm_active_passive_enum)::set(this, "env.agent", "is_active", UVM_ACTIVE);
      
      // Set the virtual interface
      uvm_config_db#(virtual ucie_sb_interface)::set(this, "env.agent.*", "vif", sb_intf);
    endfunction
    
    virtual function void end_of_elaboration_phase(uvm_phase phase);
      super.end_of_elaboration_phase(phase);
      uvm_top.print_topology();
    endfunction
  endclass
  
  // Memory access test
  class ucie_sb_memory_test extends ucie_sb_base_test;
    `uvm_component_utils(ucie_sb_memory_test)
    
    function new(string name = "ucie_sb_memory_test", uvm_component parent = null);
      super.new(name, parent);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
      ucie_sb_mem_write_seq write_seq;
      ucie_sb_mem_read_seq read_seq;
      
      phase.raise_objection(this);
      
      `uvm_info("MEMORY_TEST", "Starting memory access test", UVM_LOW)
      
      // Run memory write sequence
      write_seq = ucie_sb_mem_write_seq::type_id::create("write_seq");
      assert(write_seq.randomize() with {
        num_transactions == 5;
        use_64bit == 1'b0; // Use 32-bit first
      });
      write_seq.start(env.agent.sequencer);
      
      #1000; // Gap between sequences
      
      // Run memory read sequence
      read_seq = ucie_sb_mem_read_seq::type_id::create("read_seq");
      assert(read_seq.randomize() with {
        num_transactions == 5;
        use_64bit == 1'b0; // Use 32-bit first
      });
      read_seq.start(env.agent.sequencer);
      
      #1000;
      
      // Run 64-bit memory operations
      write_seq = ucie_sb_mem_write_seq::type_id::create("write_seq_64");
      assert(write_seq.randomize() with {
        num_transactions == 3;
        use_64bit == 1'b1; // Use 64-bit
      });
      write_seq.start(env.agent.sequencer);
      
      #1000;
      
      read_seq = ucie_sb_mem_read_seq::type_id::create("read_seq_64");
      assert(read_seq.randomize() with {
        num_transactions == 3;
        use_64bit == 1'b1; // Use 64-bit
      });
      read_seq.start(env.agent.sequencer);
      
      #2000;
      
      `uvm_info("MEMORY_TEST", "Memory access test completed", UVM_LOW)
      
      phase.drop_objection(this);
    endtask
  endclass
  
  // Configuration access test
  class ucie_sb_config_test extends ucie_sb_base_test;
    `uvm_component_utils(ucie_sb_config_test)
    
    function new(string name = "ucie_sb_config_test", uvm_component parent = null);
      super.new(name, parent);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
      ucie_sb_cfg_seq cfg_seq;
      
      phase.raise_objection(this);
      
      `uvm_info("CONFIG_TEST", "Starting configuration access test", UVM_LOW)
      
      // Run 32-bit configuration sequence
      cfg_seq = ucie_sb_cfg_seq::type_id::create("cfg_seq_32");
      assert(cfg_seq.randomize() with {
        num_reads == 3;
        num_writes == 3;
        use_64bit == 1'b0;
      });
      cfg_seq.start(env.agent.sequencer);
      
      #1000;
      
      // Run 64-bit configuration sequence
      cfg_seq = ucie_sb_cfg_seq::type_id::create("cfg_seq_64");
      assert(cfg_seq.randomize() with {
        num_reads == 2;
        num_writes == 2;
        use_64bit == 1'b1;
      });
      cfg_seq.start(env.agent.sequencer);
      
      #2000;
      
      `uvm_info("CONFIG_TEST", "Configuration access test completed", UVM_LOW)
      
      phase.drop_objection(this);
    endtask
  endclass
  
  // Mixed traffic test
  class ucie_sb_mixed_test extends ucie_sb_base_test;
    `uvm_component_utils(ucie_sb_mixed_test)
    
    function new(string name = "ucie_sb_mixed_test", uvm_component parent = null);
      super.new(name, parent);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
      ucie_sb_base_sequence sequences[];
      
      phase.raise_objection(this);
      
      `uvm_info("MIXED_TEST", "Starting mixed traffic test", UVM_LOW)
      
      // Create array of different sequences
      sequences = new[6];
      sequences[0] = ucie_sb_mem_write_seq::type_id::create("mem_wr_32");
      sequences[1] = ucie_sb_mem_read_seq::type_id::create("mem_rd_32");
      sequences[2] = ucie_sb_cfg_seq::type_id::create("cfg_32");
      sequences[3] = ucie_sb_mem_write_seq::type_id::create("mem_wr_64");
      sequences[4] = ucie_sb_mem_read_seq::type_id::create("mem_rd_64");
      sequences[5] = ucie_sb_cfg_seq::type_id::create("cfg_64");
      
      // Configure sequences
      void'($cast(sequences[0], ucie_sb_mem_write_seq::type_id::create("mem_wr_32")));
      assert(sequences[0].randomize() with {
        ucie_sb_mem_write_seq::num_transactions == 2;
        ucie_sb_mem_write_seq::use_64bit == 1'b0;
      });
      
      void'($cast(sequences[1], ucie_sb_mem_read_seq::type_id::create("mem_rd_32")));
      assert(sequences[1].randomize() with {
        ucie_sb_mem_read_seq::num_transactions == 2;
        ucie_sb_mem_read_seq::use_64bit == 1'b0;
      });
      
      void'($cast(sequences[2], ucie_sb_cfg_seq::type_id::create("cfg_32")));
      assert(sequences[2].randomize() with {
        ucie_sb_cfg_seq::num_reads == 1;
        ucie_sb_cfg_seq::num_writes == 1;
        ucie_sb_cfg_seq::use_64bit == 1'b0;
      });
      
      void'($cast(sequences[3], ucie_sb_mem_write_seq::type_id::create("mem_wr_64")));
      assert(sequences[3].randomize() with {
        ucie_sb_mem_write_seq::num_transactions == 2;
        ucie_sb_mem_write_seq::use_64bit == 1'b1;
      });
      
      void'($cast(sequences[4], ucie_sb_mem_read_seq::type_id::create("mem_rd_64")));
      assert(sequences[4].randomize() with {
        ucie_sb_mem_read_seq::num_transactions == 2;
        ucie_sb_mem_read_seq::use_64bit == 1'b1;
      });
      
      void'($cast(sequences[5], ucie_sb_cfg_seq::type_id::create("cfg_64")));
      assert(sequences[5].randomize() with {
        ucie_sb_cfg_seq::num_reads == 1;
        ucie_sb_cfg_seq::num_writes == 1;
        ucie_sb_cfg_seq::use_64bit == 1'b1;
      });
      
      // Run sequences in random order
      sequences.shuffle();
      
      foreach(sequences[i]) begin
        sequences[i].start(env.agent.sequencer);
        #500; // Small gap between different sequence types
      end
      
      #2000;
      
      `uvm_info("MIXED_TEST", "Mixed traffic test completed", UVM_LOW)
      
      phase.drop_objection(this);
    endtask
  endclass
  
  // Initial block to start UVM
  initial begin
    // Enable assertions
    `ifdef ENABLE_SIDEBAND_ASSERTIONS
      `uvm_info("TB", "Sideband assertions enabled", UVM_LOW)
    `endif
    
    // Set up UVM configuration
    uvm_config_db#(virtual ucie_sb_interface)::set(null, "*", "vif", sb_intf);
    
    // Set verbosity
    uvm_top.set_report_verbosity_level_hier(UVM_MEDIUM);
    
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
    #50000; // 50us timeout
    `uvm_fatal("TIMEOUT", "Test timeout - simulation ran too long")
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
  
  // Packet processing and display
  always_ff @(posedge sbtx_clk) begin
    if (packet_valid) begin
      logic [4:0] opcode;
      logic [2:0] srcid, dstid;
      logic [4:0] tag;
      logic [23:0] addr;
      logic [15:0] status;
      
      opcode = header_reg[6:2];
      srcid = header_reg[31:29];
      dstid = header_reg[56:54];
      tag = header_reg[25:21];
      
      if (opcode inside {5'b10000, 5'b10001, 5'b11001}) begin // Completions
        status = header_reg[47:32];
        $display("DUT: Received COMPLETION - opcode=%0d, srcid=%0d, dstid=%0d, tag=%0d, status=0x%0h", 
                 opcode, srcid, dstid, tag, status);
      end else begin // Register access
        addr = {8'h0, header_reg[47:32]};
        $display("DUT: Received REG_ACCESS - opcode=%0d, srcid=%0d, dstid=%0d, tag=%0d, addr=0x%0h", 
                 opcode, srcid, dstid, tag, addr);
      end
      
      if (data_phase) begin
        $display("DUT: Packet data = 0x%016h", data_reg);
      end
    end
  end
  
endmodule