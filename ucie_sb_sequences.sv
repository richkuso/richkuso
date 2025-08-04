// UCIe Sideband Sequence Classes
// Contains base sequence and specialized sequences for different traffic patterns

// Base sequence class
class ucie_sb_base_sequence extends uvm_sequence #(ucie_sb_transaction);
  `uvm_object_utils(ucie_sb_base_sequence)
  
  function new(string name = "ucie_sb_base_sequence");
    super.new(name);
  endfunction
endclass

// Memory read sequence
class ucie_sb_mem_read_seq extends ucie_sb_base_sequence;
  `uvm_object_utils(ucie_sb_mem_read_seq)
  
  rand int num_transactions;
  rand bit use_64bit;
  
  constraint num_trans_c { num_transactions inside {[1:10]}; }
  
  function new(string name = "ucie_sb_mem_read_seq");
    super.new(name);
  endfunction
  
  virtual task body();
    ucie_sb_transaction trans;
    repeat(num_transactions) begin
      trans = ucie_sb_transaction::type_id::create("trans");
      start_item(trans);
      assert(trans.randomize() with {
        opcode == (use_64bit ? MEM_READ_64B : MEM_READ_32B);
        addr inside {[0:24'hFFFFFF]};
      });
      finish_item(trans);
    end
  endtask
endclass

// Memory write sequence
class ucie_sb_mem_write_seq extends ucie_sb_base_sequence;
  `uvm_object_utils(ucie_sb_mem_write_seq)
  
  rand int num_transactions;
  rand bit use_64bit;
  
  constraint num_trans_c { num_transactions inside {[1:10]}; }
  
  function new(string name = "ucie_sb_mem_write_seq");
    super.new(name);
  endfunction
  
  virtual task body();
    ucie_sb_transaction trans;
    repeat(num_transactions) begin
      trans = ucie_sb_transaction::type_id::create("trans");
      start_item(trans);
      assert(trans.randomize() with {
        opcode == (use_64bit ? MEM_WRITE_64B : MEM_WRITE_32B);
        addr inside {[0:24'hFFFFFF]};
        data != 64'h0;
      });
      finish_item(trans);
    end
  endtask
endclass

// Configuration access sequence
class ucie_sb_cfg_seq extends ucie_sb_base_sequence;
  `uvm_object_utils(ucie_sb_cfg_seq)
  
  rand int num_reads;
  rand int num_writes;
  rand bit use_64bit;
  
  constraint num_trans_c { 
    num_reads inside {[1:5]};
    num_writes inside {[1:5]};
  }
  
  function new(string name = "ucie_sb_cfg_seq");
    super.new(name);
  endfunction
  
  virtual task body();
    ucie_sb_transaction trans;
    
    // Generate writes first
    repeat(num_writes) begin
      trans = ucie_sb_transaction::type_id::create("trans");
      start_item(trans);
      assert(trans.randomize() with {
        opcode == (use_64bit ? CFG_WRITE_64B : CFG_WRITE_32B);
        addr inside {[0:24'hFFFF]};
      });
      finish_item(trans);
    end
    
    // Then generate reads
    repeat(num_reads) begin
      trans = ucie_sb_transaction::type_id::create("trans");
      start_item(trans);
      assert(trans.randomize() with {
        opcode == (use_64bit ? CFG_READ_64B : CFG_READ_32B);
        addr inside {[0:24'hFFFF]};
      });
      finish_item(trans);
    end
  endtask
endclass

// DMS register access sequence
class ucie_sb_dms_seq extends ucie_sb_base_sequence;
  `uvm_object_utils(ucie_sb_dms_seq)
  
  rand int num_reads;
  rand int num_writes;
  rand bit use_64bit;
  
  constraint num_trans_c { 
    num_reads inside {[1:3]};
    num_writes inside {[1:3]};
  }
  
  function new(string name = "ucie_sb_dms_seq");
    super.new(name);
  endfunction
  
  virtual task body();
    ucie_sb_transaction trans;
    
    // Generate DMS writes
    repeat(num_writes) begin
      trans = ucie_sb_transaction::type_id::create("trans");
      start_item(trans);
      assert(trans.randomize() with {
        opcode == (use_64bit ? DMS_WRITE_64B : DMS_WRITE_32B);
        addr inside {[0:24'hFFF]};
      });
      finish_item(trans);
    end
    
    // Generate DMS reads
    repeat(num_reads) begin
      trans = ucie_sb_transaction::type_id::create("trans");
      start_item(trans);
      assert(trans.randomize() with {
        opcode == (use_64bit ? DMS_READ_64B : DMS_READ_32B);
        addr inside {[0:24'hFFF]};
      });
      finish_item(trans);
    end
  endtask
endclass

// Completion sequence (for response generation)
class ucie_sb_completion_seq extends ucie_sb_base_sequence;
  `uvm_object_utils(ucie_sb_completion_seq)
  
  rand int num_completions;
  rand bit include_data;
  rand bit use_64bit_data;
  
  constraint num_comp_c { num_completions inside {[1:5]}; }
  
  function new(string name = "ucie_sb_completion_seq");
    super.new(name);
  endfunction
  
  virtual task body();
    ucie_sb_transaction trans;
    repeat(num_completions) begin
      trans = ucie_sb_transaction::type_id::create("trans");
      start_item(trans);
      assert(trans.randomize() with {
        if (include_data) {
          opcode == (use_64bit_data ? COMPLETION_64B : COMPLETION_32B);
          data != 64'h0;
        } else {
          opcode == COMPLETION_NO_DATA;
        }
        status inside {16'h0000, 16'h0001, 16'h0002}; // Success, UR, CA
      });
      finish_item(trans);
    end
  endtask
endclass

// Message sequence
class ucie_sb_message_seq extends ucie_sb_base_sequence;
  `uvm_object_utils(ucie_sb_message_seq)
  
  rand int num_messages;
  rand bit include_data;
  
  constraint num_msg_c { num_messages inside {[1:3]}; }
  
  function new(string name = "ucie_sb_message_seq");
    super.new(name);
  endfunction
  
  virtual task body();
    ucie_sb_transaction trans;
    repeat(num_messages) begin
      trans = ucie_sb_transaction::type_id::create("trans");
      start_item(trans);
      assert(trans.randomize() with {
        if (include_data) {
          opcode == MESSAGE_64B;
          data != 64'h0;
        } else {
          opcode == MESSAGE_NO_DATA;
        }
      });
      finish_item(trans);
    end
  endtask
endclass

// Management transport message sequence
class ucie_sb_mgmt_seq extends ucie_sb_base_sequence;
  `uvm_object_utils(ucie_sb_mgmt_seq)
  
  rand int num_messages;
  rand bit include_data;
  
  constraint num_mgmt_c { num_messages inside {[1:2]}; }
  
  function new(string name = "ucie_sb_mgmt_seq");
    super.new(name);
  endfunction
  
  virtual task body();
    ucie_sb_transaction trans;
    repeat(num_messages) begin
      trans = ucie_sb_transaction::type_id::create("trans");
      start_item(trans);
      assert(trans.randomize() with {
        if (include_data) {
          opcode == MGMT_MSG_DATA;
          data != 64'h0;
        } else {
          opcode == MGMT_MSG_NO_DATA;
        }
      });
      finish_item(trans);
    end
  endtask
endclass

// Random traffic sequence - generates mixed packet types
class ucie_sb_random_seq extends ucie_sb_base_sequence;
  `uvm_object_utils(ucie_sb_random_seq)
  
  rand int num_transactions;
  rand bit enable_completions;
  rand bit enable_messages;
  rand bit enable_mgmt;
  rand bit enable_clock_patterns;
  
  constraint num_trans_c { num_transactions inside {[5:20]}; }
  
  function new(string name = "ucie_sb_random_seq");
    super.new(name);
  endfunction
  
  virtual task body();
    ucie_sb_transaction trans;
    repeat(num_transactions) begin
      trans = ucie_sb_transaction::type_id::create("trans");
      start_item(trans);
      assert(trans.randomize() with {
        // Weight register accesses more heavily
        opcode dist {
          [MEM_READ_32B:CFG_WRITE_64B] := 65,
          [COMPLETION_NO_DATA:COMPLETION_64B] := (enable_completions ? 20 : 0),
          [MESSAGE_NO_DATA:MESSAGE_64B] := (enable_messages ? 5 : 0),
          [MGMT_MSG_NO_DATA:MGMT_MSG_DATA] := (enable_mgmt ? 5 : 0),
          CLOCK_PATTERN := (enable_clock_patterns ? 5 : 0)
        };
      });
      finish_item(trans);
    end
  endtask
endclass

// Clock pattern sequence - generates clock pattern for timing synchronization
class ucie_sb_clock_pattern_seq extends ucie_sb_base_sequence;
  `uvm_object_utils(ucie_sb_clock_pattern_seq)
  
  rand int num_patterns;
  rand int gap_cycles;       // Number of gap cycles between patterns
  rand bit [2:0] pattern_srcid;
  rand bit [2:0] pattern_dstid;
  
  constraint pattern_c { 
    num_patterns inside {[1:5]};
    gap_cycles inside {[32:100]};  // Minimum 32 UI gap, up to 100 UI
  }
  
  function new(string name = "ucie_sb_clock_pattern_seq");
    super.new(name);
  endfunction
  
  virtual task body();
    ucie_sb_transaction trans;
    
    `uvm_info("CLOCK_PATTERN_SEQ", $sformatf("Starting clock pattern sequence: %0d patterns, %0d gap cycles", 
              num_patterns, gap_cycles), UVM_MEDIUM)
    
    repeat(num_patterns) begin
      trans = ucie_sb_transaction::type_id::create("clock_pattern_trans");
      start_item(trans);
      assert(trans.randomize() with {
        opcode == CLOCK_PATTERN;
        is_clock_pattern == 1;
        srcid == pattern_srcid;
        dstid == pattern_dstid;
      });
      finish_item(trans);
      
      `uvm_info("CLOCK_PATTERN_SEQ", $sformatf("Generated clock pattern: srcid=%0d, dstid=%0d", 
                trans.srcid, trans.dstid), UVM_HIGH)
      
      // Add gap between patterns if multiple patterns
      if (num_patterns > 1) begin
        // Note: Gap timing is handled by the driver automatically
        // This just provides spacing between pattern transactions
        #(gap_cycles * 1.25ns); // 1.25ns per UI for 800MHz
      end
    end
    
    `uvm_info("CLOCK_PATTERN_SEQ", "Clock pattern sequence completed", UVM_MEDIUM)
  endtask
endclass

// UCIe sideband advanced package initialization sequence with redundant lanes
class ucie_sb_init_seq extends ucie_sb_base_sequence;
  `uvm_object_utils(ucie_sb_init_seq)
  
  // Configuration parameters
  rand bit [2:0] init_srcid;
  rand bit [2:0] init_dstid;
  rand bit [3:0] reset_result;           // Result code for SBINIT out of reset
  rand bit enable_advanced_package;     // Enable advanced package sequence
  rand bit simulate_detection_failure;  // Simulate pattern detection failure for testing
  rand bit [3:0] lane_detection_result; // Simulated detection result [3:0]
  
  // Timing parameters
  rand int pattern_iterations;          // Number of initial pattern iterations
  rand int timeout_ms;                  // Timeout in milliseconds
  rand int pattern_cycle_ms;            // Pattern cycle time in ms
  
  constraint init_c { 
    pattern_iterations inside {[4:10]};
    timeout_ms inside {[8:8]};           // Fixed 8ms timeout per spec
    pattern_cycle_ms inside {[1:1]};     // Fixed 1ms cycle per spec
    reset_result inside {[0:15]};        // 4-bit result field
    init_srcid != init_dstid;           // Source != Destination
    lane_detection_result inside {[1:15]}; // At least one lane must work for success
  }
  
  // Internal variables
  typedef enum {
    LANE_DATASB_CKSB,      // Primary lane
    LANE_DATASB_CKSBRD,    // DATASB with redundant clock
    LANE_DATASBRD_CKSB,    // Redundant data with primary clock  
    LANE_DATASBRD_CKSBRD   // Redundant lane
  } lane_selection_e;
  
  lane_selection_e selected_lane;
  bit pattern_detected;
  bit timeout_occurred;
  
  function new(string name = "ucie_sb_init_seq");
    super.new(name);
  endfunction
  
  virtual task body();
    if (enable_advanced_package) begin
      advanced_package_init();
    end else begin
      basic_package_init();
    end
  endtask
  
  // Advanced package initialization sequence
  virtual task advanced_package_init();
    `uvm_info("INIT_SEQ", "Starting UCIe Advanced Package SBINIT sequence", UVM_LOW)
    
    // Step 1-3: Clock pattern transmission and detection
    clock_pattern_detection_phase();
    
    if (pattern_detected && !timeout_occurred) begin
      // Step 4: Stop after 4 more iterations
      send_final_pattern_iterations();
      
      // Step 6: Lane selection based on detection results
      select_functional_lane();
      
      // Step 7: Send SBINIT Out of Reset messages
      send_sbinit_out_of_reset_phase();
      
      // Step 8-10: Apply lane assignment and complete handshake
      complete_initialization_handshake();
      
    end else begin
      // Step 5: Timeout occurred - enter TRAINERROR state
      handle_initialization_timeout();
    end
    
    `uvm_info("INIT_SEQ", "UCIe Advanced Package SBINIT sequence completed", UVM_LOW)
  endtask
  
  // Steps 1-3: Clock pattern detection phase
  virtual task clock_pattern_detection_phase();
    ucie_sb_transaction trans;
    int cycle_count = 0;
    int max_cycles = timeout_ms; // 8ms timeout
    
    `uvm_info("INIT_SEQ", "Phase 1-3: Clock pattern transmission and detection", UVM_MEDIUM)
    
    pattern_detected = 0;
    timeout_occurred = 0;
    
    // Continue pattern transmission until detection or timeout
    while (!pattern_detected && cycle_count < max_cycles) begin
      `uvm_info("INIT_SEQ", $sformatf("Pattern cycle %0d/%0d", cycle_count + 1, max_cycles), UVM_HIGH)
      
      // Send pattern iterations for 1ms
      send_pattern_burst(pattern_cycle_ms);
      
      // Hold low for 1ms (simulated by delay)
      `uvm_info("INIT_SEQ", "Holding sideband low for 1ms", UVM_HIGH)
      #(1ms);
      
      // Simulate pattern detection check
      check_pattern_detection();
      
      cycle_count++;
    end
    
    if (cycle_count >= max_cycles) begin
      timeout_occurred = 1;
      `uvm_warning("INIT_SEQ", "Pattern detection timeout after 8ms")
    end
  endtask
  
  // Send burst of clock patterns
  virtual task send_pattern_burst(int duration_ms);
    ucie_sb_transaction trans;
    int num_patterns = duration_ms * 800; // Approximate patterns per ms at 800MHz
    
    repeat(num_patterns) begin
      trans = ucie_sb_transaction::type_id::create("clock_pattern");
      start_item(trans);
      assert(trans.randomize() with {
        opcode == CLOCK_PATTERN;
        is_clock_pattern == 1;
        srcid == init_srcid;
        dstid == init_dstid;
      });
      finish_item(trans);
      
      // 64 UI pattern + 32 UI gap = 96 UI = 120ns at 800MHz
      #(120ns);
    end
  endtask
  
  // Simulate pattern detection (would be hardware-based in real implementation)
  virtual task check_pattern_detection();
    if (simulate_detection_failure) begin
      // Simulate random detection for testing
      pattern_detected = ($urandom_range(0, 100) > 70); // 30% success rate
    end else begin
      // Normal operation - assume detection succeeds
      pattern_detected = 1;
    end
    
    if (pattern_detected) begin
      `uvm_info("INIT_SEQ", "128 UI clock pattern detected successfully", UVM_MEDIUM)
    end
  endtask
  
  // Step 4: Send final 4 pattern iterations
  virtual task send_final_pattern_iterations();
    ucie_sb_transaction trans;
    
    `uvm_info("INIT_SEQ", "Step 4: Sending final 4 pattern iterations", UVM_MEDIUM)
    
    repeat(4) begin
      trans = ucie_sb_transaction::type_id::create("final_pattern");
      start_item(trans);
      assert(trans.randomize() with {
        opcode == CLOCK_PATTERN;
        is_clock_pattern == 1;
        srcid == init_srcid;
        dstid == init_dstid;
      });
      finish_item(trans);
      
      `uvm_info("INIT_SEQ", "Sent final pattern iteration", UVM_HIGH)
      #(120ns); // 64 UI pattern + 32 UI gap
    end
  endtask
  
  // Step 6: Lane selection based on detection results
  virtual task select_functional_lane();
    `uvm_info("INIT_SEQ", "Step 6: Selecting functional sideband lane", UVM_MEDIUM)
    
    // Pseudocode implementation from spec:
    // Result[0] = CKSB sampling DATASB
    // Result[1] = CKSBRD sampling DATASB  
    // Result[2] = CKSB sampling DATASBRD
    // Result[3] = CKSBRD sampling DATASBRD
    
    case (1'b1)
      lane_detection_result[0]: begin // XXX1
        selected_lane = LANE_DATASB_CKSB;
        `uvm_info("INIT_SEQ", "Selected lane: DATASB/CKSB (primary)", UVM_MEDIUM)
      end
      lane_detection_result[1]: begin // XX10  
        selected_lane = LANE_DATASB_CKSBRD;
        `uvm_info("INIT_SEQ", "Selected lane: DATASB/CKSBRD", UVM_MEDIUM)
      end
      lane_detection_result[2]: begin // X100
        selected_lane = LANE_DATASBRD_CKSB;
        `uvm_info("INIT_SEQ", "Selected lane: DATASBRD/CKSB", UVM_MEDIUM)
      end
      lane_detection_result[3]: begin // 1000
        selected_lane = LANE_DATASBRD_CKSBRD;  
        `uvm_info("INIT_SEQ", "Selected lane: DATASBRD/CKSBRD (redundant)", UVM_MEDIUM)
      end
      default: begin
        `uvm_error("INIT_SEQ", "No functional sideband detected - all lanes failed")
        return;
      end
    endcase
    
    `uvm_info("INIT_SEQ", $sformatf("Lane detection result: 4'b%04b, Selected: %s", 
              lane_detection_result, selected_lane.name()), UVM_LOW)
  endtask
  
  // Step 7: Send SBINIT Out of Reset messages
  virtual task send_sbinit_out_of_reset_phase();
    ucie_sb_transaction trans;
    int cycle_count = 0;
    int max_cycles = 8; // 8ms timeout
    bit message_detected = 0;
    
    `uvm_info("INIT_SEQ", "Step 7: Sending SBINIT Out of Reset messages", UVM_MEDIUM)
    
    while (!message_detected && cycle_count < max_cycles) begin
      // Send SBINIT Out of Reset message
      trans = ucie_sb_transaction::type_id::create("sbinit_out_of_reset");
      start_item(trans);
      assert(trans.randomize() with {
        opcode == MESSAGE_NO_DATA;
        msgcode == MSG_SBINIT_OUT_OF_RESET;  // 0x91
        msgsubcode == SUBCODE_SBINIT_OUT_OF_RESET;  // 0x00
        msginfo == {12'h000, reset_result};  // Result includes lane info
        srcid == init_srcid;
        dstid == init_dstid;
      });
      finish_item(trans);
      
      `uvm_info("INIT_SEQ", $sformatf("Sent SBINIT Out of Reset: result=0x%01h", reset_result), UVM_HIGH)
      
      // Simulate message detection (would check receiver in real implementation)
      #(1ms);
      message_detected = ($urandom_range(0, 100) > 20); // 80% success rate
      cycle_count++;
    end
    
    if (!message_detected) begin
      `uvm_error("INIT_SEQ", "SBINIT Out of Reset message detection timeout")
    end else begin
      `uvm_info("INIT_SEQ", "SBINIT Out of Reset message detected successfully", UVM_MEDIUM)
    end
  endtask
  
  // Steps 8-10: Complete initialization handshake
  virtual task complete_initialization_handshake();
    ucie_sb_transaction trans;
    
    `uvm_info("INIT_SEQ", "Steps 8-10: Completing initialization handshake", UVM_MEDIUM)
    
    // Step 8: Apply functional sideband assignment (simulated)
    `uvm_info("INIT_SEQ", $sformatf("Applied functional sideband: %s", selected_lane.name()), UVM_MEDIUM)
    
    // Step 10: SBINIT done handshake
    // Send SBINIT done request
    trans = ucie_sb_transaction::type_id::create("sbinit_done_req");
    start_item(trans);
    assert(trans.randomize() with {
      opcode == MESSAGE_NO_DATA;
      msgcode == MSG_SBINIT_DONE_REQ;  // 0x95
      msgsubcode == SUBCODE_SBINIT_DONE;  // 0x01
      msginfo == 16'h0000;  // Always 0000h for done request
      srcid == init_srcid;
      dstid == init_dstid;
    });
    finish_item(trans);
    
    `uvm_info("INIT_SEQ", "Sent SBINIT done request", UVM_MEDIUM)
    
    // Simulate processing delay
    #(100ns);
    
    // Send SBINIT done response
    trans = ucie_sb_transaction::type_id::create("sbinit_done_resp");
    start_item(trans);
    assert(trans.randomize() with {
      opcode == MESSAGE_NO_DATA;
      msgcode == MSG_SBINIT_DONE_RESP;  // 0x9A
      msgsubcode == SUBCODE_SBINIT_DONE;  // 0x01
      msginfo == 16'h0000;  // Always 0000h for done response
      srcid == init_dstid;  // Response comes from destination
      dstid == init_srcid;  // Back to original source
    });
    finish_item(trans);
    
    `uvm_info("INIT_SEQ", "Sent SBINIT done response - Ready to exit to MBINIT", UVM_MEDIUM)
  endtask
  
  // Step 5: Handle timeout and enter TRAINERROR state
  virtual task handle_initialization_timeout();
    `uvm_error("INIT_SEQ", "SBINIT timeout occurred - entering TRAINERROR state")
    `uvm_info("INIT_SEQ", "Sideband initialization FAILED due to timeout", UVM_LOW)
  endtask
  
  // Basic package initialization (original sequence for compatibility)
  virtual task basic_package_init();
    ucie_sb_transaction trans;
    
    `uvm_info("INIT_SEQ", "Starting basic UCIe sideband initialization sequence", UVM_LOW)
    
    // Step 1: Generate clock patterns for synchronization
    repeat(pattern_iterations) begin
      trans = ucie_sb_transaction::type_id::create("init_clock_pattern");
      start_item(trans);
      assert(trans.randomize() with {
        opcode == CLOCK_PATTERN;
        is_clock_pattern == 1;
        srcid == init_srcid;
        dstid == init_dstid;
      });
      finish_item(trans);
      
      `uvm_info("INIT_SEQ", "Generated initialization clock pattern", UVM_MEDIUM)
      #(40 * 1.25ns); // 40 UI gap
    end
    
    // Step 2: Send SBINIT out of reset message
    trans = ucie_sb_transaction::type_id::create("sbinit_out_of_reset");
    start_item(trans);
    assert(trans.randomize() with {
      opcode == MESSAGE_NO_DATA;
      msgcode == MSG_SBINIT_OUT_OF_RESET;  // 0x91
      msgsubcode == SUBCODE_SBINIT_OUT_OF_RESET;  // 0x00
      msginfo == {12'h000, reset_result};  // Result in lower 4 bits
      srcid == init_srcid;
      dstid == init_dstid;
    });
    finish_item(trans);
    
    `uvm_info("INIT_SEQ", $sformatf("Generated SBINIT out of reset: result=0x%01h", reset_result), UVM_MEDIUM)
    
    // Step 3: SBINIT done handshake
    complete_initialization_handshake();
    
    `uvm_info("INIT_SEQ", "Basic UCIe sideband initialization sequence completed", UVM_LOW)
  endtask
  
endclass

// Burst sequence - generates back-to-back transactions
class ucie_sb_burst_seq extends ucie_sb_base_sequence;
  `uvm_object_utils(ucie_sb_burst_seq)
  
  rand int burst_length;
  rand ucie_sb_opcode_e burst_opcode;
  rand bit [23:0] base_addr;
  rand bit [2:0] burst_srcid;
  rand bit [2:0] burst_dstid;
  
  constraint burst_c { 
    burst_length inside {[4:8]};
    burst_opcode inside {MEM_WRITE_32B, MEM_WRITE_64B, CFG_WRITE_32B, CFG_WRITE_64B};
  }
  
  function new(string name = "ucie_sb_burst_seq");
    super.new(name);
  endfunction
  
  virtual task body();
    ucie_sb_transaction trans;
    for (int i = 0; i < burst_length; i++) begin
      trans = ucie_sb_transaction::type_id::create($sformatf("burst_trans_%0d", i));
      start_item(trans);
      assert(trans.randomize() with {
        opcode == burst_opcode;
        srcid == burst_srcid;
        dstid == burst_dstid;
        addr == (base_addr + (i * 4)); // Increment by 4 bytes
        data != 64'h0;
      });
      finish_item(trans);
    end
  endtask
endclass