package sideband_pkg;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // Sideband packet opcodes as per Table 7-1
  typedef enum bit [4:0] {
    MEM_READ_32B      = 5'b00000,
    MEM_WRITE_32B     = 5'b00001,
    DMS_READ_32B      = 5'b00010,
    DMS_WRITE_32B     = 5'b00011,
    CFG_READ_32B      = 5'b00100,
    CFG_WRITE_32B     = 5'b00101,
    MEM_READ_64B      = 5'b01000,
    MEM_WRITE_64B     = 5'b01001,
    DMS_READ_64B      = 5'b01010,
    DMS_WRITE_64B     = 5'b01011,
    CFG_READ_64B      = 5'b01100,
    CFG_WRITE_64B     = 5'b01101,
    COMPLETION_NO_DATA = 5'b10000,
    COMPLETION_32B    = 5'b10001,
    MESSAGE_NO_DATA   = 5'b10010,
    MGMT_MSG_NO_DATA  = 5'b10111,
    MGMT_MSG_DATA     = 5'b11000,
    COMPLETION_64B    = 5'b11001,
    MESSAGE_64B       = 5'b11011
  } sideband_opcode_e;

  // Packet types for easier categorization
  typedef enum {
    PKT_REG_ACCESS,
    PKT_COMPLETION,
    PKT_MESSAGE,
    PKT_MGMT
  } packet_type_e;

  // Transaction item for sideband packets
  class sideband_transaction extends uvm_sequence_item;
    // Header fields
    rand sideband_opcode_e opcode;
    rand bit [2:0]         srcid;
    rand bit [2:0]         dstid;
    rand bit [4:0]         tag;
    rand bit [7:0]         be;        // Byte enables
    rand bit               ep;        // Error poison
    rand bit               cr;        // Credit return
    rand bit [23:0]        addr;      // Address (for register access)
    rand bit [15:0]        status;    // Status (for completions)
    
    // Data payload
    rand bit [63:0]        data;
    
    // Control bits
    bit                    cp;        // Control parity
    bit                    dp;        // Data parity
    
    // Derived information
    packet_type_e          pkt_type;
    bit                    has_data;
    bit                    is_64bit;
    
    `uvm_object_utils_begin(sideband_transaction)
      `uvm_field_enum(sideband_opcode_e, opcode, UVM_ALL_ON)
      `uvm_field_int(srcid, UVM_ALL_ON)
      `uvm_field_int(dstid, UVM_ALL_ON)
      `uvm_field_int(tag, UVM_ALL_ON)
      `uvm_field_int(be, UVM_ALL_ON)
      `uvm_field_int(ep, UVM_ALL_ON)
      `uvm_field_int(cr, UVM_ALL_ON)
      `uvm_field_int(addr, UVM_ALL_ON)
      `uvm_field_int(status, UVM_ALL_ON)
      `uvm_field_int(data, UVM_ALL_ON)
      `uvm_field_int(cp, UVM_ALL_ON)
      `uvm_field_int(dp, UVM_ALL_ON)
      `uvm_field_enum(packet_type_e, pkt_type, UVM_ALL_ON)
      `uvm_field_int(has_data, UVM_ALL_ON)
      `uvm_field_int(is_64bit, UVM_ALL_ON)
    `uvm_object_utils_end

    function new(string name = "sideband_transaction");
      super.new(name);
    endfunction

    // Constraints
    constraint valid_opcode_c {
      opcode inside {
        MEM_READ_32B, MEM_WRITE_32B, DMS_READ_32B, DMS_WRITE_32B, CFG_READ_32B, CFG_WRITE_32B,
        MEM_READ_64B, MEM_WRITE_64B, DMS_READ_64B, DMS_WRITE_64B, CFG_READ_64B, CFG_WRITE_64B,
        COMPLETION_NO_DATA, COMPLETION_32B, COMPLETION_64B,
        MESSAGE_NO_DATA, MESSAGE_64B, MGMT_MSG_NO_DATA, MGMT_MSG_DATA
      };
    }
    
    constraint srcid_c { srcid inside {[0:7]}; }
    constraint dstid_c { dstid inside {[0:7]}; }
    constraint tag_c { tag inside {[0:31]}; }
    
    // Address alignment constraints
    constraint addr_alignment_c {
      if (is_64bit) addr[2:0] == 3'b000;
      else if (opcode inside {MEM_READ_32B, MEM_WRITE_32B, DMS_READ_32B, DMS_WRITE_32B, CFG_READ_32B, CFG_WRITE_32B})
        addr[1:0] == 2'b00;
    }
    
    // Byte enable constraints
    constraint be_c {
      if (opcode inside {MEM_READ_32B, MEM_WRITE_32B, DMS_READ_32B, DMS_WRITE_32B, CFG_READ_32B, CFG_WRITE_32B})
        be[7:4] == 4'b0000;
    }

    // Post-randomize to set derived fields
    function void post_randomize();
      update_packet_info();
      calculate_parity();
    endfunction

    // Update packet type and data information based on opcode
    function void update_packet_info();
      case (opcode)
        MEM_READ_32B, MEM_WRITE_32B, DMS_READ_32B, DMS_WRITE_32B, CFG_READ_32B, CFG_WRITE_32B,
        MEM_READ_64B, MEM_WRITE_64B, DMS_READ_64B, DMS_WRITE_64B, CFG_READ_64B, CFG_WRITE_64B: begin
          pkt_type = PKT_REG_ACCESS;
          has_data = (opcode inside {MEM_WRITE_32B, DMS_WRITE_32B, CFG_WRITE_32B, MEM_WRITE_64B, DMS_WRITE_64B, CFG_WRITE_64B});
          is_64bit = (opcode inside {MEM_READ_64B, MEM_WRITE_64B, DMS_READ_64B, DMS_WRITE_64B, CFG_READ_64B, CFG_WRITE_64B});
        end
        COMPLETION_NO_DATA, COMPLETION_32B, COMPLETION_64B: begin
          pkt_type = PKT_COMPLETION;
          has_data = (opcode != COMPLETION_NO_DATA);
          is_64bit = (opcode == COMPLETION_64B);
        end
        MESSAGE_NO_DATA, MESSAGE_64B: begin
          pkt_type = PKT_MESSAGE;
          has_data = (opcode == MESSAGE_64B);
          is_64bit = (opcode == MESSAGE_64B);
        end
        MGMT_MSG_NO_DATA, MGMT_MSG_DATA: begin
          pkt_type = PKT_MGMT;
          has_data = (opcode == MGMT_MSG_DATA);
          is_64bit = (opcode == MGMT_MSG_DATA);
        end
        default: begin
          pkt_type = PKT_REG_ACCESS;
          has_data = 1'b0;
          is_64bit = 1'b0;
        end
      endcase
    endfunction

    // Calculate parity bits
    function void calculate_parity();
      bit [63:0] header_bits;
      
      // Pack header for parity calculation (excluding CP and DP)
      header_bits = {srcid, 2'b00, tag, be, 3'b000, ep, opcode, 
                     1'b0, 1'b0, cr, 4'b0000, dstid, 
                     (pkt_type == PKT_COMPLETION) ? status : addr[15:0]};
      
      // Calculate control parity (even parity of header bits excluding DP)
      cp = ^header_bits;
      
      // Calculate data parity (even parity of data payload)
      if (has_data) begin
        if (is_64bit)
          dp = ^data;
        else
          dp = ^data[31:0];
      end else begin
        dp = 1'b0;
      end
    endfunction

    // Convert to 64-bit header format
    function bit [63:0] get_header();
      bit [63:0] header;
      bit [31:0] phase0, phase1;
      
      // Phase 0: srcid[31:28], rsvd[27:26], tag[25:21], be[20:13], rsvd[12:8], ep[7], opcode[6:2], rsvd[1:0]
      phase0 = {srcid, 2'b00, tag, be, 3'b000, ep, opcode, 2'b00};
      
      // Phase 1: dp[31], cp[30], cr[29], rsvd[28:25], dstid[24:22], rsvd[21:16], addr/status[15:0]
      phase1 = {dp, cp, cr, 4'b0000, dstid, 6'b000000, 
                (pkt_type == PKT_COMPLETION) ? status : addr[15:0]};
      
      header = {phase1, phase0};
      return header;
    endfunction

    // Convert to string for debug
    function string convert2string();
      string s;
      s = $sformatf("SIDEBAND_TXN: opcode=%s, srcid=%0d, dstid=%0d, tag=%0d", 
                    opcode.name(), srcid, dstid, tag);
      if (pkt_type == PKT_REG_ACCESS)
        s = {s, $sformatf(", addr=0x%0h, be=0x%0h", addr, be)};
      if (pkt_type == PKT_COMPLETION)
        s = {s, $sformatf(", status=0x%0h", status)};
      if (has_data)
        s = {s, $sformatf(", data=0x%0h", is_64bit ? data : data[31:0])};
      return s;
    endfunction
  endclass

  // Base sequence class
  class sideband_base_sequence extends uvm_sequence #(sideband_transaction);
    `uvm_object_utils(sideband_base_sequence)
    
    function new(string name = "sideband_base_sequence");
      super.new(name);
    endfunction
  endclass

  // Memory read sequence
  class sideband_mem_read_seq extends sideband_base_sequence;
    `uvm_object_utils(sideband_mem_read_seq)
    
    rand int num_transactions;
    rand bit use_64bit;
    
    constraint num_trans_c { num_transactions inside {[1:10]}; }
    
    function new(string name = "sideband_mem_read_seq");
      super.new(name);
    endfunction
    
    virtual task body();
      sideband_transaction trans;
      repeat(num_transactions) begin
        trans = sideband_transaction::type_id::create("trans");
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
  class sideband_mem_write_seq extends sideband_base_sequence;
    `uvm_object_utils(sideband_mem_write_seq)
    
    rand int num_transactions;
    rand bit use_64bit;
    
    constraint num_trans_c { num_transactions inside {[1:10]}; }
    
    function new(string name = "sideband_mem_write_seq");
      super.new(name);
    endfunction
    
    virtual task body();
      sideband_transaction trans;
      repeat(num_transactions) begin
        trans = sideband_transaction::type_id::create("trans");
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
  class sideband_cfg_seq extends sideband_base_sequence;
    `uvm_object_utils(sideband_cfg_seq)
    
    rand int num_reads;
    rand int num_writes;
    rand bit use_64bit;
    
    constraint num_trans_c { 
      num_reads inside {[1:5]};
      num_writes inside {[1:5]};
    }
    
    function new(string name = "sideband_cfg_seq");
      super.new(name);
    endfunction
    
    virtual task body();
      sideband_transaction trans;
      
      // Generate writes first
      repeat(num_writes) begin
        trans = sideband_transaction::type_id::create("trans");
        start_item(trans);
        assert(trans.randomize() with {
          opcode == (use_64bit ? CFG_WRITE_64B : CFG_WRITE_32B);
          addr inside {[0:24'hFFFF]};
        });
        finish_item(trans);
      end
      
      // Then generate reads
      repeat(num_reads) begin
        trans = sideband_transaction::type_id::create("trans");
        start_item(trans);
        assert(trans.randomize() with {
          opcode == (use_64bit ? CFG_READ_64B : CFG_READ_32B);
          addr inside {[0:24'hFFFF]};
        });
        finish_item(trans);
      end
    endtask
  endclass

  // Driver class
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
      repeat(32) @(posedge vif.sb_clk);
      
      // Drive data if present
      if (trans.has_data) begin
        if (trans.is_64bit) begin
          drive_serial_packet(data_payload);
        end else begin
          // For 32-bit data, pad MSBs with 0
          drive_serial_packet({32'h0, data_payload[31:0]});
        end
        
        // Wait minimum 32 bits low after data
        repeat(32) @(posedge vif.sb_clk);
      end
    endtask
    
    // Drive a 64-bit serial packet
    virtual task drive_serial_packet(bit [63:0] packet);
      for (int i = 0; i < 64; i++) begin
        @(posedge vif.sb_clk);
        vif.sb_data <= packet[i];
      end
      
      // Drive low after packet
      @(posedge vif.sb_clk);
      vif.sb_data <= 1'b0;
    endtask
  endclass

  // Monitor class
  class sideband_monitor extends uvm_monitor;
    `uvm_component_utils(sideband_monitor)
    
    virtual sideband_interface vif;
    uvm_analysis_port #(sideband_transaction) analysis_port;
    
    function new(string name = "sideband_monitor", uvm_component parent = null);
      super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      if (!uvm_config_db#(virtual sideband_interface)::get(this, "", "vif", vif))
        `uvm_fatal("MONITOR", "Virtual interface not found")
      analysis_port = new("analysis_port", this);
    endfunction
    
    virtual task run_phase(uvm_phase phase);
      sideband_transaction trans;
      bit [63:0] header, data_payload;
      
      forever begin
        // Wait for start of packet (data goes high)
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
        
        `uvm_info("SIDEBAND_MONITOR", trans.convert2string(), UVM_MEDIUM)
        analysis_port.write(trans);
      end
    endtask
    
    // Wait for start of packet
    virtual task wait_for_packet_start();
      @(posedge vif.sb_data);
    endtask
    
    // Wait for minimum gap between packets (32 bits low)
    virtual task wait_for_packet_gap();
      int low_count = 0;
      while (low_count < 32) begin
        @(posedge vif.sb_clk);
        if (vif.sb_data == 1'b0)
          low_count++;
        else
          low_count = 0;
      end
    endtask
    
    // Capture a 64-bit serial packet
    virtual function bit [63:0] capture_serial_packet();
      bit [63:0] packet;
      for (int i = 0; i < 64; i++) begin
        @(posedge vif.sb_clk);
        packet[i] = vif.sb_data;
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
  endclass

  // Sequencer
  typedef uvm_sequencer #(sideband_transaction) sideband_sequencer;

  // Agent
  class sideband_agent extends uvm_agent;
    `uvm_component_utils(sideband_agent)
    
    sideband_driver    driver;
    sideband_monitor   monitor;
    sideband_sequencer sequencer;
    
    function new(string name = "sideband_agent", uvm_component parent = null);
      super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      
      // Always create monitor
      monitor = sideband_monitor::type_id::create("monitor", this);
      
      // Create driver and sequencer only if agent is active
      if (get_is_active() == UVM_ACTIVE) begin
        driver = sideband_driver::type_id::create("driver", this);
        sequencer = sideband_sequencer::type_id::create("sequencer", this);
      end
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      
      if (get_is_active() == UVM_ACTIVE) begin
        driver.seq_item_port.connect(sequencer.seq_item_export);
      end
    endfunction
  endclass

endpackage