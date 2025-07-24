# UCIe Sideband UVM Agent File List
# Use this file list for compilation with simulators

# Interface and package definition
sideband_interface.sv

# Individual class files (in dependency order)
sideband_transaction.sv
sideband_sequences.sv
sideband_driver.sv
sideband_monitor.sv
sideband_agent.sv

# Updated package file that includes all classes
sideband_pkg_updated.sv

# Testbench files
sideband_testbench.sv

# Compilation example for VCS:
# vcs -f sideband_files.f +incdir+$UVM_HOME/src $UVM_HOME/src/uvm_pkg.sv -ntb_opts uvm-1.2

# Compilation example for Questa:
# vlog -f sideband_files.f +incdir+$UVM_HOME/src $UVM_HOME/src/uvm_pkg.sv -uvm

# Compilation example for Xcelium:
# xmvlog -f sideband_files.f +incdir+$UVM_HOME/src $UVM_HOME/src/uvm_pkg.sv -uvm