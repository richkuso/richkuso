# Makefile for UVM Agent Testbench
# Supports multiple simulators: VCS, Questa, Xcelium

# Default simulator
SIM ?= vcs

# Source files
SOURCES = my_interface.sv uvm_agent_pkg.sv testbench.sv

# Common UVM arguments
UVM_HOME ?= $(VCS_HOME)/etc/uvm-1.2
UVM_ARGS = +incdir+$(UVM_HOME)/src $(UVM_HOME)/src/uvm_pkg.sv

# VCS specific settings
VCS_ARGS = -sverilog -ntb_opts uvm-1.2 -debug_access+all -kdb -lca
VCS_RUN_ARGS = +UVM_TESTNAME=my_test +UVM_VERBOSITY=UVM_MEDIUM

# Questa specific settings
QUESTA_ARGS = -sv -uvm +incdir+$(UVM_HOME)/src
QUESTA_RUN_ARGS = +UVM_TESTNAME=my_test +UVM_VERBOSITY=UVM_MEDIUM

# Xcelium specific settings
XCELIUM_ARGS = -sv -uvm +incdir+$(UVM_HOME)/src
XCELIUM_RUN_ARGS = +UVM_TESTNAME=my_test +UVM_VERBOSITY=UVM_MEDIUM

# Default target
all: compile run

# Compilation targets
compile: compile_$(SIM)

compile_vcs:
	vcs $(VCS_ARGS) $(UVM_ARGS) $(SOURCES) -o simv

compile_questa:
	vlog $(QUESTA_ARGS) $(UVM_ARGS) $(SOURCES)
	vopt testbench -o testbench_opt

compile_xcelium:
	xmvlog $(XCELIUM_ARGS) $(UVM_ARGS) $(SOURCES)
	xmelab testbench -access +rwc

# Run targets
run: run_$(SIM)

run_vcs:
	./simv $(VCS_RUN_ARGS)

run_questa:
	vsim testbench_opt -c -do "run -all; quit" $(QUESTA_RUN_ARGS)

run_xcelium:
	xmsim testbench $(XCELIUM_RUN_ARGS) -exit

# Clean targets
clean: clean_$(SIM)

clean_vcs:
	rm -rf simv* csrc *.daidir *.log *.vpd *.vcd ucli.key vc_hdrs.h

clean_questa:
	rm -rf work *.log *.wlf transcript *.vstf

clean_xcelium:
	rm -rf xcelium.d *.log *.shm *.trn *.dsn

# Help target
help:
	@echo "UVM Agent Makefile"
	@echo "Available targets:"
	@echo "  compile     - Compile the testbench"
	@echo "  run         - Run the simulation"
	@echo "  all         - Compile and run (default)"
	@echo "  clean       - Clean generated files"
	@echo "  help        - Show this help"
	@echo ""
	@echo "Supported simulators (set SIM variable):"
	@echo "  vcs         - Synopsys VCS (default)"
	@echo "  questa      - Mentor Questa"
	@echo "  xcelium     - Cadence Xcelium"
	@echo ""
	@echo "Examples:"
	@echo "  make SIM=vcs"
	@echo "  make SIM=questa compile"
	@echo "  make clean"

.PHONY: all compile run clean help compile_vcs compile_questa compile_xcelium run_vcs run_questa run_xcelium clean_vcs clean_questa clean_xcelium