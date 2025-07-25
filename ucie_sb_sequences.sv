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

// UCIe sideband initialization sequence - combines clock pattern and initialization messages
class ucie_sb_init_seq extends ucie_sb_base_sequence;
  `uvm_object_utils(ucie_sb_init_seq)
  
  rand bit [2:0] init_srcid;
  rand bit [2:0] init_dstid;
  rand bit [3:0] reset_result;  // Result code for SBINIT out of reset
  rand int num_clock_patterns;
  rand bit include_done_handshake;
  
  constraint init_c { 
    num_clock_patterns inside {[1:3]};
    reset_result inside {[0:15]};  // 4-bit result field
    init_srcid != init_dstid;     // Source != Destination
  }
  
  function new(string name = "ucie_sb_init_seq");
    super.new(name);
  endfunction
  
  virtual task body();
    ucie_sb_transaction trans;
    
    `uvm_info("INIT_SEQ", $sformatf("Starting UCIe sideband initialization sequence: srcid=%0d, dstid=%0d", 
              init_srcid, init_dstid), UVM_LOW)
    
    // Step 1: Generate clock patterns for synchronization
    repeat(num_clock_patterns) begin
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
      
      // Small gap between clock patterns
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
    
    // Step 3: Optional SBINIT done handshake
    if (include_done_handshake) begin
      // Send SBINIT done request
      trans = ucie_sb_transaction::type_id::create("sbinit_done_req");
      start_item(trans);
      assert(trans.randomize() with {
        opcode == MESSAGE_NO_DATA;
        msgcode == MSG_SBINIT_DONE_REQ;  // 0x95
        msgsubcode == SUBCODE_SBINIT_DONE_REQ;  // 0x01
        msginfo == 16'h0000;  // Always 0000h for done request
        srcid == init_srcid;
        dstid == init_dstid;
      });
      finish_item(trans);
      
      `uvm_info("INIT_SEQ", "Generated SBINIT done request", UVM_MEDIUM)
      
      // Small delay before response
      #(50 * 1.25ns); // 50 UI delay
      
      // Send SBINIT done response
      trans = ucie_sb_transaction::type_id::create("sbinit_done_resp");
      start_item(trans);
      assert(trans.randomize() with {
        opcode == MESSAGE_NO_DATA;
        msgcode == MSG_SBINIT_DONE_RESP;  // 0x9A
        msgsubcode == SUBCODE_SBINIT_DONE_RESP;  // 0x01
        msginfo == 16'h0000;  // Always 0000h for done response
        srcid == init_dstid;  // Response comes from destination
        dstid == init_srcid;  // Back to original source
      });
      finish_item(trans);
      
      `uvm_info("INIT_SEQ", "Generated SBINIT done response", UVM_MEDIUM)
    end
    
    `uvm_info("INIT_SEQ", "UCIe sideband initialization sequence completed", UVM_LOW)
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