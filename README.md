# UVM Agent Implementation

This repository contains a complete UVM (Universal Verification Methodology) agent implementation using SystemVerilog and UVM 1.2 library.

## Overview

The UVM agent is a reusable verification component that provides a structured way to drive stimulus to and monitor responses from a Design Under Test (DUT). This implementation includes all the standard UVM agent components:

- **Transaction Item** (`my_transaction`): Defines the data structure for communication
- **Sequence** (`my_sequence`): Generates stimulus patterns
- **Driver** (`my_driver`): Converts transactions to pin-level activity
- **Monitor** (`my_monitor`): Observes pin-level activity and converts to transactions
- **Sequencer** (`my_sequencer`): Controls sequence execution
- **Agent** (`my_agent`): Container that instantiates and connects all components

## File Structure

```
├── uvm_agent_pkg.sv    # Main UVM agent package with all classes
├── my_interface.sv     # SystemVerilog interface definition
├── testbench.sv        # Complete testbench with DUT and test
├── Makefile           # Build and run scripts for multiple simulators
└── README.md          # This documentation
```

## Key Features

### Transaction Item (`my_transaction`)
- 32-bit data field
- 8-bit address field
- Read/write control bit
- Built-in constraints for randomization
- UVM field macros for automatic copy, compare, print functions

### Driver (`my_driver`)
- Implements standard UVM driver protocol
- Uses virtual interface for DUT communication
- Proper handshaking with ready/valid signals
- Comprehensive logging with UVM messaging

### Monitor (`my_monitor`)
- Passive observation of interface signals
- Analysis port for broadcasting observed transactions
- Protocol checking with SystemVerilog assertions
- Synchronized sampling with clock edges

### Agent (`my_agent`)
- Configurable as active or passive
- Automatic component instantiation and connection
- Supports UVM configuration database
- Follows UVM phasing methodology

## Interface Protocol

The agent uses a simple valid/ready handshake protocol:

```
     ┌─────┐       ┌─────┐       ┌─────┐
clk  ┘     └───────┘     └───────┘     └─
     
     ┌─────────────────────────────────────
data ┴─────────────┬─────────────────────
                   │     Valid Data
     
           ┌───────────────────────┐
valid ─────┘                       └─────
     
                           ┌───────────────
ready ─────────────────────┘
```

## Usage Example

### Basic Test Setup

```systemverilog
class my_test extends uvm_test;
  my_agent agent;
  
  function void build_phase(uvm_phase phase);
    agent = my_agent::type_id::create("agent", this);
    uvm_config_db#(virtual my_interface)::set(this, "agent.*", "vif", intf);
  endfunction
  
  task run_phase(uvm_phase phase);
    my_sequence seq = my_sequence::type_id::create("seq");
    seq.start(agent.sequencer);
  endtask
endclass
```

### Custom Sequence Creation

```systemverilog
class custom_sequence extends uvm_sequence #(my_transaction);
  `uvm_object_utils(custom_sequence)
  
  task body();
    my_transaction trans;
    repeat(5) begin
      trans = my_transaction::type_id::create("trans");
      start_item(trans);
      assert(trans.randomize() with {
        addr inside {[0:15]};
        read_write == 1'b1; // Write only
      });
      finish_item(trans);
    end
  endtask
endclass
```

## Building and Running

### Prerequisites
- SystemVerilog simulator (VCS, Questa, or Xcelium)
- UVM 1.2 library
- Make utility

### Compilation and Execution

```bash
# Using VCS (default)
make all

# Using Questa
make SIM=questa all

# Using Xcelium
make SIM=xcelium all

# Compile only
make compile

# Run only (after compilation)
make run

# Clean generated files
make clean
```

### Simulator-Specific Commands

#### VCS
```bash
vcs -sverilog -ntb_opts uvm-1.2 +incdir+$UVM_HOME/src $UVM_HOME/src/uvm_pkg.sv \
    my_interface.sv uvm_agent_pkg.sv testbench.sv -o simv
./simv +UVM_TESTNAME=my_test +UVM_VERBOSITY=UVM_MEDIUM
```

#### Questa
```bash
vlog -sv -uvm +incdir+$UVM_HOME/src $UVM_HOME/src/uvm_pkg.sv \
     my_interface.sv uvm_agent_pkg.sv testbench.sv
vsim testbench -c -do "run -all; quit" +UVM_TESTNAME=my_test
```

#### Xcelium
```bash
xmvlog -sv -uvm +incdir+$UVM_HOME/src $UVM_HOME/src/uvm_pkg.sv \
       my_interface.sv uvm_agent_pkg.sv testbench.sv
xmelab testbench -access +rwc
xmsim testbench +UVM_TESTNAME=my_test -exit
```

## Customization

### Adding New Transaction Fields

1. Modify `my_transaction` class in `uvm_agent_pkg.sv`:
```systemverilog
class my_transaction extends uvm_sequence_item;
  rand bit [31:0] data;
  rand bit [7:0]  addr;
  rand bit        read_write;
  rand bit [3:0]  burst_length; // New field
  
  `uvm_object_utils_begin(my_transaction)
    `uvm_field_int(data, UVM_ALL_ON)
    `uvm_field_int(addr, UVM_ALL_ON)
    `uvm_field_int(read_write, UVM_ALL_ON)
    `uvm_field_int(burst_length, UVM_ALL_ON) // Add new field
  `uvm_object_utils_end
endclass
```

2. Update the interface in `my_interface.sv` to include new signals
3. Modify driver and monitor to handle new signals

### Creating Custom Sequences

Extend the base sequence class to create specific test patterns:

```systemverilog
class burst_sequence extends uvm_sequence #(my_transaction);
  `uvm_object_utils(burst_sequence)
  
  rand int num_bursts;
  constraint num_bursts_c { num_bursts inside {[1:10]}; }
  
  task body();
    repeat(num_bursts) begin
      // Generate burst transactions
    end
  endtask
endclass
```

## Debugging Tips

1. **Increase Verbosity**: Use `+UVM_VERBOSITY=UVM_HIGH` for detailed logs
2. **Enable Waveforms**: The testbench generates `waves.vcd` automatically
3. **Use UVM Messaging**: Add `uvm_info` statements for debug information
4. **Check Interface Connections**: Verify virtual interface configuration

## UVM 1.2 Compliance

This implementation follows UVM 1.2 methodology:
- ✅ Proper use of UVM base classes
- ✅ Correct phasing (build_phase, connect_phase, run_phase)
- ✅ Configuration database usage
- ✅ Analysis ports for communication
- ✅ TLM interfaces (seq_item_port, seq_item_export)
- ✅ UVM factory for object creation
- ✅ UVM messaging and reporting

## License

This code is provided as an educational example of UVM agent implementation using SystemVerilog and UVM 1.2 library.