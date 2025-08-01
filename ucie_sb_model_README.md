# UCIe Sideband Model (UVM Component)

## Overview

The UCIe Sideband Model is a comprehensive UVM-based component that implements the UCIe sideband initial flow protocol and acts as a DUT's link parameter training engine. This model provides a complete solution for sideband communication testing and validation in UCIe systems.

## Features

### Core Functionality
- **Sideband Initial Flow Implementation**: Complete 7-step initial flow protocol
- **UVM Integration**: Full UVM component with proper phasing and TLM communication
- **Training Engine Mode**: Acts as DUT's link parameter training engine via register access
- **Configurable Parameters**: Comprehensive configuration system for timing and behavior
- **Error Handling**: Timeout detection, protocol error handling, and recovery mechanisms

### Initial Flow Protocol Steps
1. **Clock Pattern Generation**: Continuous clock pattern transmission on TX driver
2. **Clock Pattern Detection**: Detection of two back-to-back clock patterns on RX monitor
3. **Pattern Completion**: Stop clock pattern after 4 additional patterns when detected
4. **SBINIT Out of Reset**: Send SBINIT OOR messages (Result=4'h1) until detected or 8ms timeout
5. **OOR Detection**: Stop SBINIT OOR when detected on RX monitor
6. **Done Request/Response**: Exchange SBINIT done req/rsp messages
7. **Flow Completion**: Initial flow complete when both req/rsp exchanged

## Architecture

### Component Hierarchy
```
ucie_sb_model (UVM Component)
├── ucie_sb_driver (Driver Component)
├── ucie_sb_monitor (Monitor Component)
├── ucie_sb_config (Configuration Object)
└── Analysis Ports & TLM FIFOs
```

### State Machine
The model implements a comprehensive state machine with the following states:
- `IDLE`: Initial state
- `SEND_CLOCK_PATTERN`: Continuously sending clock patterns
- `CLOCK_PATTERN_FOUND`: Two patterns detected, sending remaining patterns
- `SEND_SBINIT_OOR`: Sending SBINIT Out of Reset messages
- `SEND_SBINIT_DONE_REQ`: Sending SBINIT Done Request
- `WAIT_SBINIT_DONE_RSP`: Waiting for SBINIT Done Response
- `SEND_SBINIT_DONE_RSP`: Sending SBINIT Done Response
- `INITIAL_FLOW_DONE`: Initial flow completed successfully
- `TIMEOUT_ERROR`: Timeout occurred during flow
- `PROTOCOL_ERROR`: Protocol violation detected

## File Structure

### Core Implementation Files
- **`ucie_sb_model.sv`**: Main UVM component implementing the sideband model
- **`ucie_sb_config.sv`**: Configuration class with parameters and constraints
- **`ucie_sb_model_test.sv`**: Comprehensive test example with multiple scenarios

### Supporting Files
- **`ucie_sb_interface.sv`**: Sideband interface definition (existing)
- **`ucie_sb_reg_access_checker.sv`**: Register access checker (existing)

## Configuration

### Basic Configuration
```systemverilog
ucie_sb_config cfg = ucie_sb_config::type_id::create("cfg");
cfg.configure_for_initial_flow_test();  // Set up for testing
cfg.srcid = 3'h1;                       // Source ID
cfg.dstid = 3'h2;                       // Destination ID
```

### Timing Parameters
```systemverilog
cfg.timeout_8ms = 8_000_000.0;          // 8ms timeout in ns
cfg.clock_pattern_period = 1250.0;      // 800MHz clock period
cfg.sbinit_message_period = 1000.0;     // 1µs message period
```

### Clock Pattern Configuration
```systemverilog
cfg.remaining_clock_patterns = 4;       // Patterns after detection
cfg.required_pattern_detections = 2;    // Back-to-back patterns
cfg.clock_pattern_data = 32'h55555555;  // Alternating pattern
cfg.clock_pattern_addr = 24'hAAAAAA;    // Alternating address
```

### SBINIT Message Configuration
```systemverilog
cfg.sbinit_oor_tag = 5'h10;            // SBINIT OOR tag
cfg.sbinit_done_req_tag = 5'h11;       // Done request tag
cfg.sbinit_done_rsp_tag = 5'h12;       // Done response tag
cfg.sbinit_oor_result = 4'h1;          // OOR result value
```

## Usage Examples

### Basic Model Instantiation
```systemverilog
class my_test extends uvm_test;
  ucie_sb_model sb_model;
  ucie_sb_config cfg;
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    // Create configuration
    cfg = ucie_sb_config::type_id::create("cfg");
    cfg.configure_for_initial_flow_test();
    
    // Create model
    sb_model = ucie_sb_model::type_id::create("sb_model", this);
    
    // Set configuration
    uvm_config_db#(ucie_sb_config)::set(this, "sb_model", "cfg", cfg);
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    
    // Start initial flow
    sb_model.start_initial_flow();
    
    // Wait for completion
    wait(sb_model.initial_flow_complete);
    
    phase.drop_objection(this);
  endtask
endclass
```

### Two-Model Communication Test
```systemverilog
// Create two models for link simulation
ucie_sb_model sb_model_a, sb_model_b;

// Configure with cross-communication IDs
cfg_a.srcid = 3'h1; cfg_a.dstid = 3'h2;
cfg_b.srcid = 3'h2; cfg_b.dstid = 3'h1;

// Start both models
fork
  sb_model_a.start_initial_flow();
  sb_model_b.start_initial_flow();
join

// Wait for both to complete
wait(sb_model_a.initial_flow_complete && sb_model_b.initial_flow_complete);
```

## Test Scenarios

The test suite includes comprehensive scenarios:

### 1. Basic Initial Flow
- Sequential start of two models
- Complete initial flow execution
- Success verification

### 2. Simultaneous Start
- Both models start simultaneously
- Race condition handling
- Proper completion verification

### 3. Timeout Testing
- Single model without responder
- Timeout detection verification
- Error handling validation

## API Reference

### Control Functions
```systemverilog
// Start the initial flow process
function void start_initial_flow();

// Stop the initial flow process
function void stop_initial_flow();

// Reset all initial flow state
function void reset_initial_flow();

// Get current status string
function string get_status();
```

### Status Signals
```systemverilog
bit initial_flow_active;     // Flow is currently running
bit initial_flow_complete;   // Flow completed successfully
bit initial_flow_timeout;    // Flow timed out
bit initial_flow_error;      // Protocol error occurred
```

### State Information
```systemverilog
sb_init_state_t current_state;  // Current state machine state
string state_name;              // Human-readable state name
```

## Configuration Options

### Pre-defined Configurations
```systemverilog
cfg.configure_for_initial_flow_test();  // Basic initial flow testing
cfg.configure_for_training_engine();    // Training engine mode
cfg.configure_for_performance_test();   // High-performance testing
cfg.configure_for_debug();              // Debug mode with verbose logging
```

### Validation
```systemverilog
if (!cfg.validate_config()) begin
  `uvm_error("CONFIG", "Configuration validation failed")
end
```

## Message Protocol

### Clock Pattern Messages
- **Opcode**: `MEM_READ_32B`
- **Address**: `24'hAAAAAA` (alternating pattern)
- **Data**: `32'h55555555` (alternating pattern)
- **Tag**: `5'h0`

### SBINIT Messages
- **SBINIT Out of Reset**
  - Tag: `5'h10`, Address: `24'h000010`, Data: `32'h00000001` (Result=4'h1)
- **SBINIT Done Request**
  - Tag: `5'h11`, Address: `24'h000011`, Data: `32'h00000000`
- **SBINIT Done Response**
  - Tag: `5'h12`, Address: `24'h000012`, Data: `32'h00000000`

## Timing Specifications

### Default Timing
- **8ms Timeout**: 8,000,000 ns for SBINIT message phase
- **Clock Pattern Period**: 1,250 ns (800 MHz)
- **SBINIT Message Period**: 1,000 ns (1 µs intervals)

### Configurable Ranges
- **Timeout**: 1ms to 100ms
- **Clock Period**: 500ns to 5000ns (200MHz to 2GHz)
- **Message Period**: 100ns to 10000ns (100KHz to 10MHz)

## Debug and Monitoring

### Logging Levels
- **UVM_LOW**: Major state transitions and completion
- **UVM_MEDIUM**: Message transmission and reception
- **UVM_HIGH**: Detailed state machine activity
- **UVM_DEBUG**: All internal operations

### Status Monitoring
```systemverilog
// Print current model status
$display("Model Status: %s", sb_model.get_status());

// Monitor state changes
always @(sb_model.current_state) begin
  $display("State changed to: %s", sb_model.state_name);
end
```

## Error Handling

### Timeout Detection
- Automatic timeout detection after 8ms (configurable)
- Timeout events trigger state machine transition to `TIMEOUT_ERROR`
- Proper cleanup and status reporting

### Protocol Errors
- Invalid state transitions detected
- Protocol violations logged and handled
- Graceful error recovery mechanisms

## Integration with Existing Components

### Register Access Checker Integration
The model works seamlessly with the existing `ucie_sb_reg_access_checker`:
```systemverilog
// Both components can coexist in the same testbench
ucie_sb_model sb_model;
ucie_sb_reg_access_checker sb_checker;

// Model handles initial flow, checker validates register access
```

### Interface Compatibility
Uses the existing `ucie_sb_interface` without modifications, ensuring compatibility with existing testbenches and DUTs.

## Future Enhancements

### Training Engine Mode
- Register access training implementation
- Link parameter negotiation
- Advanced training sequences

### Performance Optimizations
- Parallel processing capabilities
- High-speed pattern detection
- Optimized message handling

### Additional Features
- CRC checking implementation
- Advanced error injection
- Performance monitoring and statistics

## Compilation and Simulation

### Required Files
```bash
# Core UVM model files
ucie_sb_model.sv
ucie_sb_config.sv
ucie_sb_model_test.sv

# Supporting files (existing)
ucie_sb_interface.sv
ucie_sb_reg_access_checker.sv
```

### Compilation Example
```bash
# Using your preferred SystemVerilog simulator
vcs -sverilog +incdir+$UVM_HOME/src \
    $UVM_HOME/src/uvm_pkg.sv \
    ucie_sb_interface.sv \
    ucie_sb_config.sv \
    ucie_sb_model.sv \
    ucie_sb_model_test.sv \
    -o simv
```

### Running Tests
```bash
# Run the basic test
./simv +UVM_TESTNAME=ucie_sb_model_test

# Run with different verbosity
./simv +UVM_TESTNAME=ucie_sb_model_test +UVM_VERBOSITY=UVM_HIGH

# Generate waveforms
./simv +UVM_TESTNAME=ucie_sb_model_test +vcd+ucie_sb_model_test.vcd
```

## Support and Maintenance

This implementation provides a solid foundation for UCIe sideband protocol testing and can be extended for additional functionality as needed. The modular UVM-based design ensures easy integration with existing verification environments and supports future enhancements.

For questions or enhancements, refer to the inline documentation and UVM methodology guidelines.