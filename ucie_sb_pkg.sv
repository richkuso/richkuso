package ucie_sb_pkg;
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
    MESSAGE_64B       = 5'b11011,
    CLOCK_PATTERN     = 5'b11111  // Special clock pattern transaction
  } ucie_sb_opcode_e;

  // Packet types for easier categorization
  typedef enum {
    PKT_REG_ACCESS,
    PKT_COMPLETION,
    PKT_MESSAGE,
    PKT_MGMT,
    PKT_CLOCK_PATTERN
  } packet_type_e;

  // Message codes for messages without data (Table 7-8)
  typedef enum bit [7:0] {
    MSG_SBINIT_OUT_OF_RESET = 8'h91,
    MSG_SBINIT_DONE_REQ     = 8'h95,
    MSG_SBINIT_DONE_RESP    = 8'h9A
  } ucie_sb_msgcode_e;

  // Message subcodes for messages without data (Table 7-8)
  typedef enum bit [7:0] {
    SUBCODE_SBINIT_OUT_OF_RESET = 8'h00,
    SUBCODE_SBINIT_DONE_REQ     = 8'h01,
    SUBCODE_SBINIT_DONE_RESP    = 8'h02
  } ucie_sb_msgsubcode_e;

  // Clock pattern constants
  parameter bit [31:0] CLOCK_PATTERN_PHASE0 = 32'h5555_5555;
  parameter bit [31:0] CLOCK_PATTERN_PHASE1 = 32'h5555_5555;

  // Include all class files
  `include "ucie_sb_config.sv"
  `include "ucie_sb_transaction.sv"
  `include "ucie_sb_sequences.sv"
  `include "ucie_sb_driver.sv"
  `include "ucie_sb_monitor.sv"
  `include "ucie_sb_reg_access_checker.sv"
  
  // Sequencer typedef
  typedef uvm_sequencer #(ucie_sb_transaction) ucie_sb_sequencer;
  
  `include "ucie_sb_agent.sv"

endpackage