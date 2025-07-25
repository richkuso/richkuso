# 🔄 Migration Guide - Restructuring UCIe Sideband Agent

## 🎯 **Migration Overview**

This guide provides step-by-step instructions to migrate your current UCIe sideband agent files to the recommended professional structure.

## 📋 **Current State Analysis**

### **Existing Files** (Root Directory):
```
/workspace/
├── sideband_transaction.sv          # Transaction class
├── sideband_driver.sv               # Driver class  
├── sideband_monitor.sv              # Monitor class
├── sideband_agent.sv                # Agent class
├── sideband_interface.sv            # Interface definition
├── sideband_sequencer.sv            # Sequencer class
├── sideband_source_sync_example.sv  # Example/demo
├── sideband_files.f                 # File list
├── sideband_Makefile                # Build script
├── sideband_README.md               # Documentation
└── *.md files                       # Various documentation
```

## 🚀 **Migration Steps**

### **Step 1: Create Directory Structure**

```bash
# Create the professional directory structure
mkdir -p ucie_sideband_agent/{src,tests,examples,doc,scripts,config,tools,validation,release}

# Create source subdirectories
mkdir -p ucie_sideband_agent/src/{interfaces,packages,transaction,driver,monitor,sequencer,agent,env}

# Create test subdirectories  
mkdir -p ucie_sideband_agent/tests/{unit,integration,regression,testbenches}

# Create documentation subdirectories
mkdir -p ucie_sideband_agent/doc/{specification,user_guide,design,api}

# Create script subdirectories
mkdir -p ucie_sideband_agent/scripts/{build,regression,utils}

# Create config subdirectories
mkdir -p ucie_sideband_agent/config/{simulator,coverage,lint}

# Create tools subdirectories
mkdir -p ucie_sideband_agent/tools/{makefiles,docker}

# Create validation subdirectories
mkdir -p ucie_sideband_agent/validation/{protocols,assertions}

# Create examples subdirectories
mkdir -p ucie_sideband_agent/examples/{simple_example,advanced_example,timing_example}
```

### **Step 2: Migrate Core Source Files**

```bash
# Move source files to appropriate directories
mv sideband_interface.sv ucie_sideband_agent/src/interfaces/
mv sideband_transaction.sv ucie_sideband_agent/src/transaction/
mv sideband_driver.sv ucie_sideband_agent/src/driver/
mv sideband_monitor.sv ucie_sideband_agent/src/monitor/
mv sideband_sequencer.sv ucie_sideband_agent/src/sequencer/
mv sideband_agent.sv ucie_sideband_agent/src/agent/
```

### **Step 3: Migrate Build and Configuration Files**

```bash
# Move build files
mv sideband_Makefile ucie_sideband_agent/tools/makefiles/Makefile.sideband
mv sideband_files.f ucie_sideband_agent/config/simulator/sideband.f

# Move documentation
mv sideband_README.md ucie_sideband_agent/doc/user_guide/getting_started.md
mv *.md ucie_sideband_agent/doc/design/
```

### **Step 4: Create Package Structure**

Create the main package file:

```systemverilog
// ucie_sideband_agent/src/packages/sideband_pkg.sv
//=============================================================================
// PACKAGE: sideband_pkg
//
// DESCRIPTION:
//   Main package for UCIe sideband UVM agent containing all type definitions,
//   enumerations, and class includes for the complete verification IP.
//
// AUTHOR: UCIe Sideband UVM Agent
// VERSION: 1.0
//=============================================================================

package sideband_pkg;
  
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  
  //=============================================================================
  // TYPE DEFINITIONS AND ENUMERATIONS
  //=============================================================================
  
  // UCIe sideband opcodes (19 total)
  typedef enum bit [4:0] {
    MEM_READ_32B    = 5'b00000,
    CFG_READ_32B    = 5'b00001,
    MEM_WRITE_32B   = 5'b00010,
    CFG_WRITE_32B   = 5'b00011,
    MEM_READ_64B    = 5'b00100,
    CFG_READ_64B    = 5'b00101,
    MEM_WRITE_64B   = 5'b00110,
    CFG_WRITE_64B   = 5'b00111,
    DMS_READ_32B    = 5'b01000,
    DMS_WRITE_32B   = 5'b01001,
    DMS_READ_64B    = 5'b01010,
    DMS_WRITE_64B   = 5'b01011,
    COMPLETION_NO_DATA = 5'b01100,
    COMPLETION_32B  = 5'b01101,
    COMPLETION_64B  = 5'b01110,
    MESSAGE_NO_DATA = 5'b01111,
    MESSAGE_64B     = 5'b10000,
    MGMT_MSG_NO_DATA = 5'b10001,
    MGMT_MSG_DATA   = 5'b10010
  } sideband_opcode_e;
  
  // Packet types
  typedef enum bit [1:0] {
    REGISTER_ACCESS = 2'b00,
    COMPLETION     = 2'b01,
    MESSAGE        = 2'b10
  } packet_type_e;
  
  //=============================================================================
  // CLASS INCLUDES
  //=============================================================================
  
  // Include all component classes
  `include "../transaction/sideband_transaction.sv"
  `include "../sequencer/sideband_sequencer.sv"
  `include "../driver/sideband_driver.sv"
  `include "../monitor/sideband_monitor.sv"
  `include "../agent/sideband_agent.sv"
  
endpackage : sideband_pkg
```

### **Step 5: Create Type Definitions File**

```systemverilog
// ucie_sideband_agent/src/packages/sideband_types.sv
//=============================================================================
// FILE: sideband_types.sv
//
// DESCRIPTION:
//   Type definitions and enumerations for UCIe sideband protocol
//
// AUTHOR: UCIe Sideband UVM Agent
// VERSION: 1.0
//=============================================================================

// UCIe sideband opcodes (complete set of 19)
typedef enum bit [4:0] {
  MEM_READ_32B    = 5'b00000,  // Memory read 32-bit
  CFG_READ_32B    = 5'b00001,  // Config read 32-bit
  MEM_WRITE_32B   = 5'b00010,  // Memory write 32-bit
  CFG_WRITE_32B   = 5'b00011,  // Config write 32-bit
  MEM_READ_64B    = 5'b00100,  // Memory read 64-bit
  CFG_READ_64B    = 5'b00101,  // Config read 64-bit
  MEM_WRITE_64B   = 5'b00110,  // Memory write 64-bit
  CFG_WRITE_64B   = 5'b00111,  // Config write 64-bit
  DMS_READ_32B    = 5'b01000,  // DMS read 32-bit
  DMS_WRITE_32B   = 5'b01001,  // DMS write 32-bit
  DMS_READ_64B    = 5'b01010,  // DMS read 64-bit
  DMS_WRITE_64B   = 5'b01011,  // DMS write 64-bit
  COMPLETION_NO_DATA = 5'b01100,  // Completion without data
  COMPLETION_32B  = 5'b01101,  // Completion with 32-bit data
  COMPLETION_64B  = 5'b01110,  // Completion with 64-bit data
  MESSAGE_NO_DATA = 5'b01111,  // Message without data
  MESSAGE_64B     = 5'b10000,  // Message with 64-bit data
  MGMT_MSG_NO_DATA = 5'b10001,  // Management message without data
  MGMT_MSG_DATA   = 5'b10010   // Management message with data
} sideband_opcode_e;

// Packet type classification
typedef enum bit [1:0] {
  REGISTER_ACCESS = 2'b00,
  COMPLETION     = 2'b01,
  MESSAGE        = 2'b10
} packet_type_e;

// Source/Destination ID definitions
typedef enum bit [2:0] {
  LOCAL_DIE       = 3'b000,
  D2D_ADAPTER     = 3'b001,
  PHYSICAL_LAYER  = 3'b010,
  MGMT_PORT_GATEWAY = 3'b011,
  REMOTE_DIE_1    = 3'b001,
  REMOTE_DIE_2    = 3'b010,
  REMOTE_DIE_3    = 3'b011
} sideband_id_e;
```

### **Step 6: Update File Lists**

```bash
# ucie_sideband_agent/config/simulator/vcs.f
+incdir+src/packages
+incdir+src/interfaces
+incdir+src/transaction
+incdir+src/driver
+incdir+src/monitor
+incdir+src/sequencer
+incdir+src/agent

src/packages/sideband_pkg.sv
src/interfaces/sideband_interface.sv
```

### **Step 7: Create Build Scripts**

```bash
#!/bin/bash
# ucie_sideband_agent/scripts/build/compile.sh

echo "Compiling UCIe Sideband Agent..."

# Set simulator (default to VCS)
SIMULATOR=${SIMULATOR:-vcs}

# Set paths
SRC_DIR="../../src"
CONFIG_DIR="../../config"

case $SIMULATOR in
  "vcs")
    vcs -sverilog -ntb_opts uvm-1.2 \
        -f ${CONFIG_DIR}/simulator/vcs.f \
        -timescale=1ns/1ps \
        -debug_access+all
    ;;
  "questa")
    vlog -sv -f ${CONFIG_DIR}/simulator/questa.f \
         +incdir+${SRC_DIR}/packages \
         -timescale 1ns/1ps
    ;;
  *)
    echo "Unsupported simulator: $SIMULATOR"
    exit 1
    ;;
esac

echo "Compilation complete!"
```

### **Step 8: Create Examples**

```systemverilog
// ucie_sideband_agent/examples/simple_example/simple_test.sv
//=============================================================================
// SIMPLE EXAMPLE: Basic UCIe Sideband Test
//=============================================================================

class simple_sideband_test extends uvm_test;
  `uvm_component_utils(simple_sideband_test)
  
  sideband_agent agent;
  
  function new(string name = "simple_sideband_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    // Create agent
    agent = sideband_agent::type_id::create("agent", this);
    
    // Configure for 800MHz operation
    sideband_agent_config cfg = sideband_agent_config::type_id::create("cfg");
    cfg.set_800mhz_config();
    uvm_config_db#(sideband_agent_config)::set(this, "agent", "cfg", cfg);
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    
    `uvm_info("TEST", "Starting simple sideband test", UVM_LOW)
    
    // Run for some time
    #1000ns;
    
    `uvm_info("TEST", "Simple sideband test complete", UVM_LOW)
    phase.drop_objection(this);
  endtask
  
endclass
```

### **Step 9: Create Documentation Structure**

```markdown
# ucie_sideband_agent/doc/user_guide/getting_started.md

# Getting Started with UCIe Sideband Agent

## Overview
The UCIe Sideband UVM Agent provides a complete verification solution for UCIe sideband protocol interfaces.

## Quick Start

### 1. Compilation
```bash
cd scripts/build
./compile.sh
```

### 2. Run Simple Example
```bash
cd examples/simple_example
make run
```

### 3. Configuration
The agent supports 800MHz and 400MHz operation modes.
```systemverilog
// 800MHz configuration
cfg.set_800mhz_config();

// 400MHz configuration  
cfg.set_400mhz_config();
```
```

### **Step 10: Create Makefile Structure**

```makefile
# ucie_sideband_agent/tools/makefiles/Makefile.common

# Common variables
PROJECT_ROOT = ../..
SRC_DIR = $(PROJECT_ROOT)/src
CONFIG_DIR = $(PROJECT_ROOT)/config
TEST_DIR = $(PROJECT_ROOT)/tests
SCRIPTS_DIR = $(PROJECT_ROOT)/scripts

# Default simulator
SIMULATOR ?= vcs

# Common targets
.PHONY: compile clean help

compile:
	@echo "Compiling with $(SIMULATOR)..."
	@$(SCRIPTS_DIR)/build/compile.sh

clean:
	@echo "Cleaning build artifacts..."
	@rm -rf simv* csrc *.log *.vpd *.fsdb

help:
	@echo "Available targets:"
	@echo "  compile - Compile the design"
	@echo "  clean   - Clean build artifacts"
	@echo "  help    - Show this help"
```

## 📊 **Migration Verification**

### **Directory Structure Check**:
```bash
# Verify the new structure
tree ucie_sideband_agent/

# Expected output:
ucie_sideband_agent/
├── src/
│   ├── interfaces/
│   │   └── sideband_interface.sv
│   ├── packages/
│   │   ├── sideband_pkg.sv
│   │   └── sideband_types.sv
│   ├── transaction/
│   │   └── sideband_transaction.sv
│   ├── driver/
│   │   └── sideband_driver.sv
│   ├── monitor/
│   │   └── sideband_monitor.sv
│   ├── sequencer/
│   │   └── sideband_sequencer.sv
│   └── agent/
│       └── sideband_agent.sv
├── config/
│   └── simulator/
│       └── vcs.f
├── scripts/
│   └── build/
│       └── compile.sh
└── examples/
    └── simple_example/
        └── simple_test.sv
```

### **Compilation Test**:
```bash
# Test compilation with new structure
cd ucie_sideband_agent/scripts/build
./compile.sh
```

## ✅ **Migration Benefits**

### **Before Migration**:
- ❌ All files in root directory
- ❌ No clear organization
- ❌ Difficult to scale
- ❌ Hard to maintain

### **After Migration**:
- ✅ **Professional Structure**: Industry-standard organization
- ✅ **Scalable**: Easy to add new components
- ✅ **Maintainable**: Clear separation of concerns
- ✅ **Tool Compatible**: Works with all major simulators
- ✅ **Well Documented**: Comprehensive documentation structure

## 🎯 **Next Steps**

1. **Complete Migration**: Follow all steps above
2. **Test Compilation**: Verify everything builds correctly
3. **Add More Examples**: Create additional usage examples
4. **Enhance Documentation**: Add more detailed API docs
5. **Set Up CI/CD**: Implement automated testing

**This migration will transform your agent into a professional, industry-standard UVM verification IP!** 🔄✨🚀