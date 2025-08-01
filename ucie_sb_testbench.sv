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
  ucie_sb_interface sb_intf(.clk(1'b0), .reset(sb_reset));
  
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
    .sbtx_clk(sb_intf.SBTX_CLK),
    .sbtx_data(sb_intf.SBTX_DATA),
    .sbrx_clk(sb_intf.SBRX_CLK),
    .sbrx_data(sb_intf.SBRX_DATA),
    .sb_reset(sb_reset)
  );
  
  // UVM Environment with checker support
  class ucie_sb_env extends uvm_env;
    `uvm_component_utils(ucie_sb_env)
    
    ucie_sb_agent tx_agent;
    ucie_sb_agent rx_agent;
    ucie_sb_reg_access_checker reg_checker;
    
    function new(string name = "ucie_sb_env", uvm_component parent = null);
      super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      
      // Create TX agent (active)
      tx_agent = ucie_sb_agent::type_id::create("tx_agent", this);
      
      // Create RX agent (passive monitor only)
      rx_agent = ucie_sb_agent::type_id::create("rx_agent", this);
      
      // Create register access checker
      reg_checker = ucie_sb_reg_access_checker::type_id::create("reg_checker", this);
      
      // Configure agents
      uvm_config_db#(uvm_active_passive_enum)::set(this, "tx_agent", "is_active", UVM_ACTIVE);
      uvm_config_db#(uvm_active_passive_enum)::set(this, "rx_agent", "is_active", UVM_PASSIVE);
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      
      // Connect agents to checker using FIFO-only architecture
      tx_agent.monitor.ap.connect(reg_checker.tx_fifo.analysis_export);
      rx_agent.monitor.ap.connect(reg_checker.rx_fifo.analysis_export);
      
      `uvm_info("ENV", "=== Checker Connections Established ===", UVM_LOW)
      `uvm_info("ENV", "TX Agent Monitor → reg_checker.tx_fifo", UVM_LOW)
      `uvm_info("ENV", "RX Agent Monitor → reg_checker.rx_fifo", UVM_LOW)
    endfunction
  endclass
  
  // Base test class
  class ucie_sb_base_test extends uvm_test;
    `uvm_component_utils(ucie_sb_base_test)
    
    ucie_sb_env env;
    ucie_sb_config cfg;
    
    function new(string name = "ucie_sb_base_test", uvm_component parent = null);
      super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      
      // Create configuration
      cfg = ucie_sb_config::type_id::create("cfg");
      assert(cfg.randomize() with {
        srcid == 3'h1;
        dstid == 3'h2;
        enable_initial_flow == 1;
      });
      
      // Create environment
      env = ucie_sb_env::type_id::create("env", this);
      
      // Set configuration in database
      uvm_config_db#(ucie_sb_config)::set(this, "*", "cfg", cfg);
      
      // Set the virtual interface for both agents
      uvm_config_db#(virtual ucie_sb_interface)::set(this, "env.tx_agent.*", "vif", sb_intf);
      uvm_config_db#(virtual ucie_sb_interface)::set(this, "env.rx_agent.*", "vif", sb_intf);
    endfunction
    
    virtual function void end_of_elaboration_phase(uvm_phase phase);
      super.end_of_elaboration_phase(phase);
      uvm_top.print_topology();
    endfunction
  endclass
  
  // Clock pattern test
  class ucie_sb_clock_pattern_test extends ucie_sb_base_test;
    `uvm_component_utils(ucie_sb_clock_pattern_test)
    
    function new(string name = "ucie_sb_clock_pattern_test", uvm_component parent = null);
      super.new(name, parent);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
      ucie_sb_clock_pattern_sequence clk_seq;
      
      phase.raise_objection(this);
      
      `uvm_info("CLOCK_PATTERN_TEST", "=== Starting Clock Pattern Test ===", UVM_LOW)
      
      // Configure checker for non-TAG mode (clock patterns don't use tags)
      env.reg_checker.enable_tag_support = 0;
      
      // Run clock pattern sequence
      clk_seq = ucie_sb_clock_pattern_sequence::type_id::create("clk_seq");
      assert(clk_seq.randomize() with {
        num_patterns == 10;
      });
      clk_seq.start(env.tx_agent.sequencer);
      
      #5000; // Allow time for patterns to complete
      
      `uvm_info("CLOCK_PATTERN_TEST", "=== Clock Pattern Test Completed ===", UVM_LOW)
      
      phase.drop_objection(this);
    endtask
  endclass
  
  // Memory access test with TAG support
  class ucie_sb_memory_test extends ucie_sb_base_test;
    `uvm_component_utils(ucie_sb_memory_test)
    
    function new(string name = "ucie_sb_memory_test", uvm_component parent = null);
      super.new(name, parent);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
      ucie_sb_register_access_sequence reg_seq;
      
      phase.raise_objection(this);
      
      `uvm_info("MEMORY_TEST", "=== Starting Memory Access Test with TAG Support ===", UVM_LOW)
      
      // Configure checker for TAG mode
      env.reg_checker.enable_tag_support = 1;
      
      // Run memory access sequence with various operations
      reg_seq = ucie_sb_register_access_sequence::type_id::create("reg_seq");
      assert(reg_seq.randomize() with {
        num_transactions == 8;
        enable_mem_read == 1;
        enable_mem_write == 1;
        enable_cfg_read == 1;
        enable_cfg_write == 1;
        enable_32bit == 1;
        enable_64bit == 1;
      });
      reg_seq.start(env.tx_agent.sequencer);
      
      #10000; // Allow time for all transactions
      
      `uvm_info("MEMORY_TEST", "=== Memory Access Test Completed ===", UVM_LOW)
      
      phase.drop_objection(this);
    endtask
  endclass
  
  // Configuration access test without TAG support
  class ucie_sb_config_test extends ucie_sb_base_test;
    `uvm_component_utils(ucie_sb_config_test)
    
    function new(string name = "ucie_sb_config_test", uvm_component parent = null);
      super.new(name, parent);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
      ucie_sb_register_access_sequence reg_seq;
      
      phase.raise_objection(this);
      
      `uvm_info("CONFIG_TEST", "=== Starting Config Access Test without TAG Support ===", UVM_LOW)
      
      // Configure checker for non-TAG mode (blocking behavior)
      env.reg_checker.enable_tag_support = 0;
      
      // Run configuration sequence (one at a time due to blocking)
      reg_seq = ucie_sb_register_access_sequence::type_id::create("reg_seq");
      assert(reg_seq.randomize() with {
        num_transactions == 4;
        enable_mem_read == 0;
        enable_mem_write == 0;
        enable_cfg_read == 1;
        enable_cfg_write == 1;
        enable_32bit == 1;
        enable_64bit == 0;
        force_tag_zero == 1; // Force TAG=0 for non-TAG mode
      });
      reg_seq.start(env.tx_agent.sequencer);
      
      #8000;
      
      `uvm_info("CONFIG_TEST", "=== Config Access Test Completed ===", UVM_LOW)
      
      phase.drop_objection(this);
    endtask
  endclass
  
  // SBINIT message test
  class ucie_sb_sbinit_test extends ucie_sb_base_test;
    `uvm_component_utils(ucie_sb_sbinit_test)
    
    function new(string name = "ucie_sb_sbinit_test", uvm_component parent = null);
      super.new(name, parent);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
      ucie_sb_sbinit_sequence sbinit_seq;
      
      phase.raise_objection(this);
      
      `uvm_info("SBINIT_TEST", "=== Starting SBINIT Message Test ===", UVM_LOW)
      
      // Configure checker to ignore messages (focus on register access)
      env.reg_checker.enable_tag_support = 1;
      
      // Run SBINIT sequence
      sbinit_seq = ucie_sb_sbinit_sequence::type_id::create("sbinit_seq");
      assert(sbinit_seq.randomize() with {
        include_out_of_reset == 1;
        include_done_req == 1;
        include_done_resp == 1;
        num_repetitions == 2;
      });
      sbinit_seq.start(env.tx_agent.sequencer);
      
      #6000;
      
      `uvm_info("SBINIT_TEST", "=== SBINIT Message Test Completed ===", UVM_LOW)
      
      phase.drop_objection(this);
    endtask
  endclass
  
  // Mixed traffic test with comprehensive coverage
  class ucie_sb_mixed_test extends ucie_sb_base_test;
    `uvm_component_utils(ucie_sb_mixed_test)
    
    function new(string name = "ucie_sb_mixed_test", uvm_component parent = null);
      super.new(name, parent);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
      ucie_sb_base_sequence sequences[];
      
      phase.raise_objection(this);
      
      `uvm_info("MIXED_TEST", "=== Starting Comprehensive Mixed Traffic Test ===", UVM_LOW)
      
      // Configure checker for TAG mode
      env.reg_checker.enable_tag_support = 1;
      
      // Create array of different sequences
      sequences = new[5];
      sequences[0] = ucie_sb_clock_pattern_sequence::type_id::create("clk_pattern");
      sequences[1] = ucie_sb_register_access_sequence::type_id::create("reg_32bit");
      sequences[2] = ucie_sb_register_access_sequence::type_id::create("reg_64bit");
      sequences[3] = ucie_sb_sbinit_sequence::type_id::create("sbinit_msgs");
      sequences[4] = ucie_sb_register_access_sequence::type_id::create("mixed_reg");
      
      // Configure clock pattern sequence
      assert(sequences[0].randomize() with {
        ucie_sb_clock_pattern_sequence::num_patterns == 5;
      });
      
      // Configure 32-bit register sequence
      assert(sequences[1].randomize() with {
        ucie_sb_register_access_sequence::num_transactions == 4;
        ucie_sb_register_access_sequence::enable_32bit == 1;
        ucie_sb_register_access_sequence::enable_64bit == 0;
      });
      
      // Configure 64-bit register sequence
      assert(sequences[2].randomize() with {
        ucie_sb_register_access_sequence::num_transactions == 3;
        ucie_sb_register_access_sequence::enable_32bit == 0;
        ucie_sb_register_access_sequence::enable_64bit == 1;
      });
      
      // Configure SBINIT sequence
      assert(sequences[3].randomize() with {
        ucie_sb_sbinit_sequence::include_out_of_reset == 1;
        ucie_sb_sbinit_sequence::include_done_req == 1;
        ucie_sb_sbinit_sequence::num_repetitions == 1;
      });
      
      // Configure mixed register sequence
      assert(sequences[4].randomize() with {
        ucie_sb_register_access_sequence::num_transactions == 6;
        ucie_sb_register_access_sequence::enable_mem_read == 1;
        ucie_sb_register_access_sequence::enable_cfg_write == 1;
      });
      
      // Run sequences with gaps
      foreach(sequences[i]) begin
        `uvm_info("MIXED_TEST", $sformatf("Running sequence %0d: %s", i, sequences[i].get_name()), UVM_MEDIUM)
        sequences[i].start(env.tx_agent.sequencer);
        #2000; // Gap between different sequence types
      end
      
      #5000; // Final settling time
      
      `uvm_info("MIXED_TEST", "=== Mixed Traffic Test Completed ===", UVM_LOW)
      
      phase.drop_objection(this);
    endtask
  endclass
  
  // Checker validation test - specifically tests checker functionality
  class ucie_sb_checker_test extends ucie_sb_base_test;
    `uvm_component_utils(ucie_sb_checker_test)
    
    function new(string name = "ucie_sb_checker_test", uvm_component parent = null);
      super.new(name, parent);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
      ucie_sb_single_transaction_sequence single_seq;
      ucie_sb_transaction req_trans, comp_trans;
      
      phase.raise_objection(this);
      
      `uvm_info("CHECKER_TEST", "=== Starting Checker Validation Test ===", UVM_LOW)
      
      // Test TAG mode first
      `uvm_info("CHECKER_TEST", "--- Testing TAG Mode ---", UVM_LOW)
      env.reg_checker.enable_tag_support = 1;
      
      // Send a memory read request
      single_seq = ucie_sb_single_transaction_sequence::type_id::create("mem_read_req");
      req_trans = ucie_sb_transaction::type_id::create("req_trans");
      assert(req_trans.randomize() with {
        opcode == MEM_READ_32B;
        srcid == 3'h1;
        dstid == 3'h2;
        tag == 5'h05;
        addr == 24'h001000;
      });
      single_seq.trans = req_trans;
      single_seq.start(env.tx_agent.sequencer);
      
      #1000;
      
      // Send corresponding completion
      single_seq = ucie_sb_single_transaction_sequence::type_id::create("mem_read_comp");
      comp_trans = ucie_sb_transaction::type_id::create("comp_trans");
      assert(comp_trans.randomize() with {
        opcode == COMPLETION_32B;
        srcid == 3'h2; // Swapped for completion
        dstid == 3'h1;
        tag == 5'h05;   // Matching tag
        status == 16'h0000; // Success
        data == 64'hDEADBEEF_CAFEBABE;
      });
      single_seq.trans = comp_trans;
      single_seq.start(env.tx_agent.sequencer);
      
      #2000;
      
      // Test non-TAG mode
      `uvm_info("CHECKER_TEST", "--- Testing Non-TAG Mode ---", UVM_LOW)
      env.reg_checker.enable_tag_support = 0;
      
      // Send config write (no completion expected)
      single_seq = ucie_sb_single_transaction_sequence::type_id::create("cfg_write");
      req_trans = ucie_sb_transaction::type_id::create("cfg_write_trans");
      assert(req_trans.randomize() with {
        opcode == CFG_WRITE_32B;
        srcid == 3'h1;
        dstid == 3'h2;
        tag == 5'h00;    // Must be 0 in non-TAG mode
        addr == 24'h002000;
        data == 64'h12345678_9ABCDEF0;
      });
      single_seq.trans = req_trans;
      single_seq.start(env.tx_agent.sequencer);
      
      #3000;
      
      `uvm_info("CHECKER_TEST", "=== Checker Validation Test Completed ===", UVM_LOW)
      
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
    
    // Display testbench information
    `uvm_info("TB", "=== UCIe Sideband UVM Testbench ===", UVM_LOW)
    `uvm_info("TB", "Features: Register Access Checker, Clock Patterns, SBINIT Messages", UVM_LOW)
    `uvm_info("TB", "Architecture: FIFO-Only Checker, TAG/Non-TAG Support", UVM_LOW)
    
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
    if (env != null && env.reg_checker != null) begin
      `uvm_info("TB", $sformatf("TX Transactions Processed: %0d", env.reg_checker.tx_transactions_processed), UVM_LOW)
      `uvm_info("TB", $sformatf("RX Transactions Processed: %0d", env.reg_checker.rx_transactions_processed), UVM_LOW)
      `uvm_info("TB", $sformatf("Outstanding Requests: %0d", env.reg_checker.outstanding_requests.size()), UVM_LOW)
      `uvm_info("TB", $sformatf("Successful Matches: %0d", env.reg_checker.successful_matches), UVM_LOW)
    end
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