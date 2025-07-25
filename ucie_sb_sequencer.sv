// UCIe Sideband Sequencer Class
// Basic sequencer for UCIe sideband transactions

//=============================================================================
// CLASS: ucie_sb_sequencer
//
// DESCRIPTION:
//   UCIe sideband sequencer that manages the flow of transactions to the driver.
//   Extends the standard UVM sequencer to provide UCIe sideband specific
//   functionality and transaction management.
//
// AUTHOR: UCIe Sideband UVM Agent
// VERSION: 1.0
//=============================================================================

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