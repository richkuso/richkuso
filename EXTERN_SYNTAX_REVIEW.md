# Extern Syntax Review and Corrections

## ❌ **CRITICAL ISSUES FOUND**

### **Issue 1: Mixed Extern and Inline Declarations**
**Problem**: The code has both extern declarations AND inline implementations in the same class.

#### **Current (INCORRECT)**:
```systemverilog
class sideband_driver extends uvm_driver #(sideband_transaction);
  
  // Extern declarations
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);
  
  // BUT THEN INLINE IMPLEMENTATION IN SAME CLASS - WRONG!
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // ... implementation
  endfunction
  
  virtual task run_phase(uvm_phase phase);
    // ... implementation
  endtask
endclass
```

**This is INVALID SystemVerilog syntax!**

### **Issue 2: Missing Implementation Scope Resolution**
**Problem**: Some implementations use scope resolution (correct) while others don't.

#### **Current (INCONSISTENT)**:
```systemverilog
// CORRECT:
function sideband_driver::new(string name = "sideband_driver", uvm_component parent = null);
  super.new(name, parent);
endfunction

// INCORRECT (missing scope resolution):
virtual function void build_phase(uvm_phase phase);
  super.build_phase(phase);
  // ...
endfunction
```

### **Issue 3: Virtual Keyword in Extern Declarations**
**Problem**: Using `virtual` in extern declarations is redundant and potentially problematic.

## ✅ **CORRECT EXTERN SYNTAX**

### **Option 1: Pure Extern Approach (RECOMMENDED)**
```systemverilog
class sideband_driver extends uvm_driver #(sideband_transaction);
  
  //------------------------------------------
  // Class Members
  //------------------------------------------
  virtual sideband_interface vif;
  sideband_driver_config cfg;
  
  //------------------------------------------
  // Extern Function/Task Declarations
  //------------------------------------------
  
  // Constructor
  extern function new(string name = "sideband_driver", uvm_component parent = null);
  
  // UVM Phases (NO virtual keyword in extern)
  extern function void build_phase(uvm_phase phase);
  extern task run_phase(uvm_phase phase);
  extern function void report_phase(uvm_phase phase);
  extern function void final_phase(uvm_phase phase);
  
  // Core Driver Tasks
  extern task drive_transaction(sideband_transaction trans);
  extern function bit drive_packet_with_clock(bit [63:0] packet);
  extern task drive_gap(int num_cycles = MIN_GAP_CYCLES);
  
  // NO INLINE IMPLEMENTATIONS HERE!
  
endclass

//------------------------------------------
// Implementation Section (OUTSIDE class)
//------------------------------------------

// Constructor
function sideband_driver::new(string name = "sideband_driver", uvm_component parent = null);
  super.new(name, parent);
endfunction

// UVM Phases (virtual keyword goes here)
virtual function void sideband_driver::build_phase(uvm_phase phase);
  super.build_phase(phase);
  // ... implementation
endfunction

virtual task sideband_driver::run_phase(uvm_phase phase);
  // ... implementation
endtask

// Other implementations...
```

### **Option 2: Mixed Approach (ALSO VALID)**
```systemverilog
class sideband_driver extends uvm_driver #(sideband_transaction);
  
  //------------------------------------------
  // Class Members
  //------------------------------------------
  virtual sideband_interface vif;
  sideband_driver_config cfg;
  
  //------------------------------------------
  // Constructor
  //------------------------------------------
  
  function new(string name = "sideband_driver", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  //------------------------------------------
  // Extern Function/Task Declarations
  //------------------------------------------
  
  // Only complex functions/tasks as extern
  extern task drive_transaction(sideband_transaction trans);
  extern function bit validate_transaction(sideband_transaction trans);
  
  //------------------------------------------
  // Simple Inline Implementations
  //------------------------------------------
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // Simple implementation here
  endfunction
  
endclass

//------------------------------------------
// Extern Implementations
//------------------------------------------

task sideband_driver::drive_transaction(sideband_transaction trans);
  // Complex implementation here
endtask

function bit sideband_driver::validate_transaction(sideband_transaction trans);
  // Complex implementation here
endfunction
```

## 🔧 **REQUIRED FIXES**

### **Fix 1: Remove Inline Implementations from Driver Class**

I need to move all inline implementations outside the class or remove extern declarations.

### **Fix 2: Add Proper Scope Resolution**

All extern implementations must use `ClassName::FunctionName` syntax.

### **Fix 3: Fix Virtual Keyword Usage**

- Remove `virtual` from extern declarations
- Add `virtual` to implementations when needed

## ✅ **CORRECTED IMPLEMENTATION**

Let me provide the corrected versions of the key issues I found: