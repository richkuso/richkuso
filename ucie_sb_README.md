# UCIe Sideband UVM Agent Implementation

This repository contains a comprehensive UVM agent implementation for the UCIe (Universal Chiplet Interconnect Express) sideband protocol using SystemVerilog and UVM 1.2 library.

## Overview

The UCIe sideband agent implements the UCIe sideband transmission protocol as specified in Section 4.1.5 and Chapter 7.0 of the UCIe specification. It supports serial data transmission with proper packet formatting, timing, and protocol compliance.

### Key Protocol Features

- **Serial Interface**: Single data line with clock for packet transmission
- **64-bit Packet Format**: Headers and data transmitted as 64-bit serial packets
- **Multiple Packet Types**: Register access, completions, messages, and management transport
- **Variable Data Sizes**: Support for 32-bit and 64-bit data payloads
- **Minimum Gap Requirement**: 32 bits low between packets
- **Parity Protection**: Control and data parity for error detection

## Key Features

- **UCIe Compliant**: Implements UCIe 1.1 sideband protocol specification
- **Source-Synchronous**: Driver generates both clock and data per transaction (true UCIe behavior)
- **Separate TX/RX Paths**: Full-duplex communication with independent clock domains
- **19 Opcode Support**: All UCIe sideband opcodes (Register Access, Messages, Management, Completions)
- **Comprehensive Validation**: Built-in protocol checking and error detection
- **Modular Design**: Clean separation of transaction, sequences, driver, monitor, and agent
- **Multi-Simulator Support**: Works with VCS, Questa, and Xcelium
- **Configurable Timing**: Adjustable clock frequencies, duty cycles, and gap cycles

## Source-Synchronous Operation

The UCIe sideband protocol is **source-synchronous**, meaning the transmitter generates both the clock and data signals. This is different from system-synchronous protocols where a common clock is shared.

### How It Works

1. **Idle State**: Both `SBTX_CLK` and `SBTX_DATA` are low when no transmission is active
2. **Transaction Start**: Driver receives a UVM transaction from the sequencer
3. **Clock Generation**: Driver generates the clock signal along with data for each bit
4. **Data Transmission**: Each bit is driven at the positive edge of the clock
5. **Gap Period**: After each packet, both clock and data remain low for minimum 32 clock cycles

### Timing Implementation (Updated)

```
Clock:  ___/‾\__/‾\__/‾\__/‾\__________________________
Data:   _____|B0|_|B1|_|B2|_|B3|________________________
        
        |<-low->|<-high->|     |<-- Gap Period -->|
```

**Key Changes**: Data is now driven exactly at the positive edge of the clock without setup time, providing precise timing control.

### 800MHz Timing Considerations

- **Bit Period**: 1.25ns (very fast - requires careful timing)
- **Clock Low Time**: 0.625ns (50% duty cycle)
- **Clock High Time**: 0.625ns (50% duty cycle)
- **Gap Duration**: 40ns minimum (32 × 1.25ns)
- **64-bit Packet**: 80ns transmission time (64 × 1.25ns)
- **Total Transaction**: ~120ns (packet + gap)

## Architecture

### UVM Components

The agent follows standard UVM methodology and includes:

- **`ucie_sb_transaction`**: Transaction item with all packet fields and constraints
- **`ucie_sb_driver`**: Converts transactions to serial bit stream with precise timing
- **`ucie_sb_monitor`**: Captures serial data and reconstructs transactions
- **`ucie_sb_sequencer`**: Controls sequence execution (extends uvm_sequencer)
- **`ucie_sb_agent`**: Container that manages all components
- **Sequences**: Pre-built sequences for different traffic patterns

### Packet Types Supported

Based on UCIe Table 7-1 opcode encodings:

| Opcode | Packet Type | Data Size |
|--------|-------------|-----------|
| 00000b | 32b Memory Read | No Data |
| 00001b | 32b Memory Write | 32-bit Data |
| 00010b | 32b DMS Register Read | No Data |
| 00011b | 32b DMS Register Write | 32-bit Data |
| 00100b | 32b Configuration Read | No Data |
| 00101b | 32b Configuration Write | 32-bit Data |
| 01000b | 64b Memory Read | No Data |
| 01001b | 64b Memory Write | 64-bit Data |
| 01010b | 64b DMS Register Read | No Data |
| 01011b | 64b DMS Register Write | 64-bit Data |
| 01100b | 64b Configuration Read | No Data |
| 01101b | 64b Configuration Write | 64-bit Data |
| 10000b | Completion without Data | No Data |
| 10001b | Completion with 32b Data | 32-bit Data |
| 10010b | Message without Data | No Data |
| 10111b | Management Port Messages without Data | No Data |
| 11000b | Management Port Message with Data | 64-bit Data |
| 11001b | Completion with 64b Data | 64-bit Data |
| 11011b | Message with 64b Data | 64-bit Data |
| 11111b | Clock Pattern | Special Pattern |

## File Structure

```
├── ucie_sb_pkg.sv                           # Main UVM agent package
├── ucie_sb_interface.sv                     # SystemVerilog interface with protocol signals
├── ucie_sb_transaction.sv                   # Transaction class with packet fields
├── ucie_sb_sequences.sv                     # Pre-built sequence library
├── ucie_sb_driver.sv                        # Driver with source-synchronous timing
├── ucie_sb_monitor.sv                       # Monitor for protocol checking
├── ucie_sb_sequencer.sv                     # Sequencer component
├── ucie_sb_agent.sv                         # Top-level agent container
├── ucie_sb_testbench.sv                     # Complete testbench
├── ucie_sb_clock_pattern_example.sv         # Clock pattern sequence example
├── ucie_sb_source_sync_example.sv           # Source-synchronous timing example
├── ucie_sb_transaction_extern_example.sv    # External method example
├── ucie_sb_files.f                          # File list for compilation
├── ucie_sb_Makefile                         # Build system with multi-simulator support
└── ucie_sb_README.md                        # This documentation
```

## Transaction Fields

### Header Fields (64-bit)

```systemverilog
class ucie_sb_transaction extends uvm_sequence_item;
  // Packet identification
  rand ucie_sb_opcode_e opcode;    // 5-bit opcode
  rand bit [2:0]         srcid;     // Source identifier
  rand bit [2:0]         dstid;     // Destination identifier
  rand bit [4:0]         tag;       // Transaction tag
  
  // Control fields
  rand bit [7:0]         be;        // Byte enables
  rand bit               ep;        // Error poison
  rand bit               cr;        // Credit return
  
  // Address/Status (context dependent)
  rand bit [23:0]        addr;      // Address (register access)
  rand bit [15:0]        status;    // Status (completions)
  
  // Data payload
  rand bit [63:0]        data;      // Up to 64-bit data
  
  // Parity bits (automatically calculated)
  bit                    cp;        // Control parity
  bit                    dp;        // Data parity
endclass
```

### Packet Format

Following UCIe specification Section 7.1.2:

**Phase 0 (Header bits 31:0):**
- `[31:29]` - srcid
- `[28:26]` - reserved
- `[25:21]` - tag
- `[20:13]` - be (byte enables)
- `[12:8]`  - reserved
- `[7]`     - ep (error poison)
- `[6:2]`   - opcode
- `[1:0]`   - reserved

**Phase 1 (Header bits 63:32):**
- `[31]`    - dp (data parity)
- `[30]`    - cp (control parity)
- `[29]`    - cr (credit return)
- `[28:25]` - reserved
- `[24:22]` - dstid
- `[21:16]` - reserved
- `[15:0]`  - addr[15:0] or status

## Built-in Sequences

### Memory Access Sequences

```systemverilog
// Memory write sequence
ucie_sb_mem_write_seq write_seq;
write_seq.randomize() with {
  num_transactions == 5;
  use_64bit == 1'b1;  // Use 64-bit operations
};

// Memory read sequence  
ucie_sb_mem_read_seq read_seq;
read_seq.randomize() with {
  num_transactions == 5;
  use_64bit == 1'b0;  // Use 32-bit operations
};
```

### Configuration Sequences

```systemverilog
// Configuration access sequence
ucie_sb_cfg_seq cfg_seq;
cfg_seq.randomize() with {
  num_reads == 3;
  num_writes == 3;
  use_64bit == 1'b0;
};
```

### Clock Pattern Sequence

```systemverilog
// Clock pattern sequence for initialization
ucie_sb_clock_pattern_seq clk_seq;
clk_seq.start(agent.sequencer);
```

## Usage Examples

### Basic Agent Instantiation

```systemverilog
class my_test extends uvm_test;
  ucie_sb_agent agent;
  
  function void build_phase(uvm_phase phase);
    agent = ucie_sb_agent::type_id::create("agent", this);
    
    // Configure as active agent
    uvm_config_db#(uvm_active_passive_enum)::set(
      this, "agent", "is_active", UVM_ACTIVE);
    
    // Set virtual interface
    uvm_config_db#(virtual ucie_sb_interface)::set(
      this, "agent.*", "vif", ucie_sb_intf);
  endfunction
  
  task run_phase(uvm_phase phase);
    ucie_sb_mem_write_seq seq;
    seq = ucie_sb_mem_write_seq::type_id::create("seq");
    seq.start(agent.sequencer);
  endtask
endclass
```

### Custom Transaction Creation

```systemverilog
ucie_sb_transaction trans = ucie_sb_transaction::type_id::create("trans");
assert(trans.randomize() with {
  opcode == CFG_WRITE_64B;
  addr inside {[0:24'hFFFF]};
  srcid == 3'b001;
  dstid == 3'b010;
  data != 64'h0;
});
```

## Building and Running

### Prerequisites
- SystemVerilog simulator (VCS, Questa, or Xcelium)
- UVM 1.2 library
- Make utility

### Quick Start

```bash
# Compile and run memory test (default)
make

# Run specific test
make TEST=ucie_sb_config_test

# Run with different simulator
make SIM=questa TEST=ucie_sb_mixed_test

# Run all tests
make test_all

# Debug with GUI
make debug

# Generate coverage
make coverage
```

### Available Tests

1. **`ucie_sb_memory_test`** - Memory read/write operations (32-bit and 64-bit)
2. **`ucie_sb_config_test`** - Configuration register access
3. **`ucie_sb_mixed_test`** - Mixed traffic with randomized packet types

### Makefile Targets

| Target | Description |
|--------|-------------|
| `compile` | Compile testbench |
| `run` | Run simulation |
| `debug` | Run with GUI |
| `coverage` | Generate coverage report |
| `lint` | Run linting checks |
| `regress` | Run all tests |
| `clean` | Clean generated files |
| `help` | Show all available targets |

## Protocol Compliance

### Timing Requirements

- **Serial Transmission**: Each packet transmitted as 64 consecutive bits
- **Minimum Gap**: 32 clock cycles low between packets
- **Clock Domain**: Separate sideband clock (typically higher frequency)
- **Data Timing**: Data driven at positive edge of clock without setup time

### Error Checking

- **Parity Protection**: Control and data parity automatically calculated
- **Protocol Assertions**: Optional SystemVerilog assertions for protocol checking
- **Address Alignment**: Automatic enforcement of alignment constraints

### Interface Assertions

When `ENABLE_SIDEBAND_ASSERTIONS` is defined:

```systemverilog
// Minimum gap between packets
assert property (min_gap_between_packets);

// Packet length exactly 64 bits
assert property (packet_length_64bits);

// Data stability during transmission
assert property (data_stable_on_clock);
```

## Advanced Features

### Coverage Collection

The interface includes functional coverage for:
- Data transition patterns
- Reset activity
- Protocol state coverage

### Configurable Assertions

```bash
# Enable assertions (default)
make ENABLE_ASSERTIONS=1

# Disable assertions for performance
make ENABLE_ASSERTIONS=0
```

### Debug Features

- **Waveform Generation**: Automatic VCD generation
- **Transaction Logging**: Detailed UVM messaging
- **DUT Integration**: Example receiver DUT included

## Customization

### Adding Custom Sequences

```systemverilog
class my_custom_seq extends ucie_sb_base_sequence;
  `uvm_object_utils(my_custom_seq)
  
  task body();
    ucie_sb_transaction trans;
    // Custom sequence implementation
    repeat(10) begin
      trans = ucie_sb_transaction::type_id::create("trans");
      start_item(trans);
      assert(trans.randomize() with {
        // Custom constraints
        opcode inside {MEM_READ_32B, MEM_WRITE_32B};
        addr[15:0] inside {[16'h1000:16'h1FFF]};
      });
      finish_item(trans);
    end
  endtask
endclass
```

### Extending Transaction Fields

```systemverilog
class extended_ucie_sb_transaction extends ucie_sb_transaction;
  rand bit [7:0] custom_field;
  
  `uvm_object_utils_begin(extended_ucie_sb_transaction)
    `uvm_field_int(custom_field, UVM_ALL_ON)
  `uvm_object_utils_end
  
  constraint custom_c { custom_field inside {[1:255]}; }
endclass
```

## Performance Considerations

### Simulation Speed
- Disable assertions for faster simulation: `ENABLE_ASSERTIONS=0`
- Use appropriate UVM verbosity levels
- Consider using compiled simulation modes

### Memory Usage
- Transaction pools for high-throughput scenarios
- Configurable sequence lengths
- Optional waveform generation

## Troubleshooting

### Common Issues

1. **Interface Not Found**
   ```
   FATAL: Virtual interface not found
   ```
   **Solution**: Ensure virtual interface is properly set in config_db

2. **Timing Violations**
   ```
   ERROR: Minimum gap between packets violated
   ```
   **Solution**: Check clock frequency and reset timing

3. **Parity Errors**
   ```
   WARNING: Parity mismatch detected
   ```
   **Solution**: Verify data integrity and transmission timing

### Debug Commands

```bash
# Run with maximum verbosity
make run VCS_RUN_ARGS="+UVM_VERBOSITY=UVM_HIGH"

# Enable specific debug messages
make run VCS_RUN_ARGS="+UVM_VERBOSITY=UVM_DEBUG"

# Generate detailed waveforms
make debug
```

## UCIe Specification Compliance

This implementation follows:
- UCIe Specification Section 4.1.5 (Sideband transmission)
- UCIe Specification Chapter 7.0 (Packet formats and encodings)
- Table 7-1 (Opcode Encodings Mapped to Packet Types)
- Section 7.1.2 (Packet Formats)

### Verified Features

- ✅ 64-bit serial packet transmission
- ✅ Minimum 32-bit gap between packets
- ✅ All specified packet types and opcodes
- ✅ Proper address alignment constraints
- ✅ Parity calculation and checking
- ✅ Byte enable handling for 32-bit vs 64-bit operations
- ✅ Source-synchronous clock generation
- ✅ Data driven at positive edge without setup time

## Recent Updates

### Driver Timing Enhancement
- Modified `drive_packet_with_clock` function to drive data at positive edge without setup time
- Simplified timing logic for more predictable behavior
- Maintained 800MHz operation with precise clock control

## License

This code is provided as an educational example of UCIe sideband protocol implementation using SystemVerilog and UVM 1.2 library.