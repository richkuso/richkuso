# UCIe Sideband UVM Agent File List
# Use this file list for compilation with simulators

# Interface and package definition
ucie_sb_inf.sv

# Individual class files (in dependency order)
ucie_sb_config.sv
ucie_sb_transaction.sv
ucie_sb_sequences.sv
ucie_sb_driver.sv
ucie_sb_monitor.sv
ucie_sb_sequencer.sv
ucie_sb_agent.sv

# Main package file that includes all classes
ucie_sb_pkg.sv

# Test environment and classes
ucie_sb_env.sv
ucie_sb_base_test.sv
ucie_sb_clock_pattern_test.sv
ucie_sb_memory_test.sv
ucie_sb_config_test.sv
ucie_sb_sbinit_test.sv
ucie_sb_mixed_test.sv
ucie_sb_checker_test.sv

# Test package
ucie_sb_test_pkg.sv

# Testbench files
ucie_sb_testbench.sv

# Example files (optional)
ucie_sb_clock_pattern_example.sv
ucie_sb_source_sync_example.sv
ucie_sb_transaction_extern_example.sv

# Checker components
ucie_sb_reg_access_checker.sv
ucie_sb_reg_checker_example.sv

# Compilation example for VCS:
# vcs -f ucie_sb_files.f +incdir+$UVM_HOME/src $UVM_HOME/src/uvm_pkg.sv -ntb_opts uvm-1.2

# Compilation example for Questa:
# vlog -f ucie_sb_files.f +incdir+$UVM_HOME/src $UVM_HOME/src/uvm_pkg.sv -uvm

# Compilation example for Xcelium:
# xmvlog -f ucie_sb_files.f +incdir+$UVM_HOME/src $UVM_HOME/src/uvm_pkg.sv -uvm