# Makefile for SystemVerilog UVM Counter Testbench

# Simulator selection (default to VCS, can be overridden)
SIM ?= vcs

# UVM version
UVM_VERSION = 1.2

# Source files
DESIGN_FILES = counter.sv
INTERFACE_FILES = counter_interface.sv
PACKAGE_FILES = counter_pkg.sv advanced_tests.sv
TESTBENCH_FILES = testbench.sv

ALL_FILES = $(DESIGN_FILES) $(INTERFACE_FILES) $(PACKAGE_FILES) $(TESTBENCH_FILES)

# Compilation and simulation options
VCS_OPTS = -sverilog -ntb_opts uvm-$(UVM_VERSION) +incdir+$(UVM_HOME)/src \
           -timescale=1ns/1ps -full64 -debug_access+all +vcs+lic+wait \
           -CFLAGS -DVCS

QUESTA_OPTS = -sv -uvm +incdir+$(UVM_HOME)/src -timescale 1ns/1ps

# Default target
all: compile run

# VCS compilation and simulation
vcs_compile:
	vcs $(VCS_OPTS) $(ALL_FILES) -o simv

vcs_run:
	./simv +UVM_TESTNAME=counter_test +UVM_VERBOSITY=UVM_MEDIUM

# Questa compilation and simulation
questa_compile:
	vlog $(QUESTA_OPTS) $(ALL_FILES)

questa_run:
	vsim -c -do "run -all; quit" testbench +UVM_TESTNAME=counter_test +UVM_VERBOSITY=UVM_MEDIUM

# Generic targets
ifeq ($(SIM), vcs)
compile: vcs_compile
run: vcs_run
else ifeq ($(SIM), questa)
compile: questa_compile
run: questa_run
else
compile: vcs_compile
run: vcs_run
endif

# Clean generated files
clean:
	rm -rf simv* csrc *.log *.vcd *.wlf work transcript vsim.wlf
	rm -rf DVEfiles inter.vpd ucli.key vc_hdrs.h
	rm -rf .vlogansetup.env .vlogansetup.args .synopsys_vss.setup

# Run with different verbosity levels
run_low:
	$(MAKE) run UVM_VERBOSITY=UVM_LOW

run_medium:
	$(MAKE) run UVM_VERBOSITY=UVM_MEDIUM

run_high:
	$(MAKE) run UVM_VERBOSITY=UVM_HIGH

run_full:
	$(MAKE) run UVM_VERBOSITY=UVM_FULL

# Run with specific test
run_test:
	@echo "Available tests:"
	@echo "  counter_test (default)"
	@echo "  counter_advanced_test"
	@echo "Usage: make run_test TEST=<test_name>"
	$(MAKE) run UVM_TESTNAME=$(TEST)

# Run advanced test
run_advanced:
	$(MAKE) run UVM_TESTNAME=counter_advanced_test

# View waveforms
waves:
	dve -vpd vcdplus.vpd &

# Help target
help:
	@echo "Available targets:"
	@echo "  all          - Compile and run (default)"
	@echo "  compile      - Compile only"
	@echo "  run          - Run simulation"
	@echo "  run_low      - Run with UVM_LOW verbosity"
	@echo "  run_medium   - Run with UVM_MEDIUM verbosity"
	@echo "  run_high     - Run with UVM_HIGH verbosity"
	@echo "  run_full     - Run with UVM_FULL verbosity"
	@echo "  run_test     - Run specific test (TEST=<name>)"
	@echo "  waves        - View waveforms"
	@echo "  clean        - Clean generated files"
	@echo "  help         - Show this help"
	@echo ""
	@echo "Simulator selection:"
	@echo "  SIM=vcs      - Use Synopsys VCS (default)"
	@echo "  SIM=questa   - Use Mentor Questa/ModelSim"

.PHONY: all compile run clean help waves run_low run_medium run_high run_full run_test
.PHONY: vcs_compile vcs_run questa_compile questa_run