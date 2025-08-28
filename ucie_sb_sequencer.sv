/*******************************************************************************
 * UCIe Sideband Protocol Sequencer
 * 
 * OVERVIEW:
 *   UVM sequencer component for UCIe (Universal Chiplet Interconnect Express)
 *   sideband protocol transaction management. Extends standard UVM sequencer
 *   to provide sideband-specific transaction flow control.
 *
 * FUNCTIONALITY:
 *   • Transaction flow management to driver component
 *   • Standard UVM sequencer interface compliance
 *   • UCIe sideband transaction type specialization
 *   • Sequence execution and arbitration support
 *
 * INTEGRATION:
 *   • Seamless integration with UCIe sideband agent
 *   • Compatible with all standard UVM sequence types
 *   • Factory registration for polymorphic usage
 *
 * COMPLIANCE:
 *   • IEEE 1800-2017 SystemVerilog
 *   • UVM 1.2 methodology
 *   • UCIe 1.1 specification
 *
 * AUTHOR: UCIe Sideband UVM Agent
 * VERSION: 3.0 - Production-grade sequencer
 ******************************************************************************/

class ucie_sb_sequencer extends uvm_sequencer #(ucie_sb_transaction);
  `uvm_component_utils(ucie_sb_sequencer)
  
  //=============================================================================
  // CONSTRUCTOR
  //=============================================================================

  //-----------------------------------------------------------------------------
  // FUNCTION: new
  // Creates a new UCIe sideband sequencer component
  //
  // PARAMETERS:
  //   name   - Component name for UVM hierarchy
  //   parent - Parent component reference
  //-----------------------------------------------------------------------------
  function new(string name = "ucie_sb_sequencer", uvm_component parent = null);
    super.new(name, parent);
  endfunction

endclass : ucie_sb_sequencer