// UCIe Sideband Test Package
// Contains all test classes for the UCIe sideband testbench

package ucie_sb_test_pkg;
  import uvm_pkg::*;
  import ucie_sb_pkg::*;
  `include "uvm_macros.svh"
  
  // Include all test-related classes
  `include "ucie_sb_env.sv"
  `include "ucie_sb_base_test.sv"
  `include "ucie_sb_clock_pattern_test.sv"
  `include "ucie_sb_memory_test.sv"
  `include "ucie_sb_config_test.sv"
  `include "ucie_sb_sbinit_test.sv"
  `include "ucie_sb_mixed_test.sv"
  `include "ucie_sb_checker_test.sv"
  
endpackage