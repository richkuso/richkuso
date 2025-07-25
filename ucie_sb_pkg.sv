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
    MESSAGE_64B       = 5'b11011
  } ucie_sb_opcode_e;

  // Packet types for easier categorization
  typedef enum {
    PKT_REG_ACCESS,
    PKT_COMPLETION,
    PKT_MESSAGE,
    PKT_MGMT
  } packet_type_e;

  // Include all class files
  `include "ucie_sb_transaction.sv"
  `include "ucie_sb_sequences.sv"
  `include "ucie_sb_driver.sv"
  `include "ucie_sb_monitor.sv"
  
  // Sequencer typedef
  typedef uvm_sequencer #(ucie_sb_transaction) ucie_sb_sequencer;
  
  `include "ucie_sb_agent.sv"

endpackage