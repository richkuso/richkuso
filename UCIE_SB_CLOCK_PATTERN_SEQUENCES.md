# 🕐 UCIe Sideband Clock Pattern Sequences

## 🎯 **Enhancement Summary**

Added comprehensive clock pattern sequence support for UCIe sideband timing synchronization and protocol compliance testing. This includes dedicated sequences for clock pattern generation, UCIe initialization with clock patterns, and integrated examples.

## 📋 **New Sequences Added**

### **✅ ucie_sb_clock_pattern_seq**
- **Purpose**: Generates clock pattern transactions for timing synchronization
- **Features**: Configurable number of patterns, gap timing, source/destination IDs
- **Use Cases**: Link initialization, clock recovery, timing alignment

### **✅ ucie_sb_init_seq**  
- **Purpose**: Complete UCIe sideband initialization sequence
- **Features**: Clock patterns + SBINIT messages + done handshake
- **Use Cases**: Protocol-compliant initialization, system bring-up

### **✅ Enhanced ucie_sb_random_seq**
- **Purpose**: Mixed traffic generation including clock patterns
- **Features**: Weighted distribution with clock pattern support
- **Use Cases**: Comprehensive protocol testing

## 🔧 **Implementation Details**

### **1. Clock Pattern Sequence**

#### **Class Definition**:
```systemverilog
class ucie_sb_clock_pattern_seq extends ucie_sb_base_sequence;
  `uvm_object_utils(ucie_sb_clock_pattern_seq)
  
  rand int num_patterns;        // Number of clock patterns to generate
  rand int gap_cycles;          // Gap between patterns (UI cycles)
  rand bit [2:0] pattern_srcid; // Source ID for patterns
  rand bit [2:0] pattern_dstid; // Destination ID for patterns
  
  constraint pattern_c { 
    num_patterns inside {[1:5]};
    gap_cycles inside {[32:100]};  // Minimum 32 UI gap per spec
  }
endclass
```

#### **Key Features**:
- **Configurable Pattern Count**: 1-5 patterns per sequence
- **Gap Control**: 32-100 UI gap between patterns (UCIe compliant)
- **Source/Destination Control**: Full 3-bit ID support
- **Timing Awareness**: 1.25ns UI timing for 800MHz operation

#### **Usage Example**:
```systemverilog
ucie_sb_clock_pattern_seq clock_seq;
clock_seq = ucie_sb_clock_pattern_seq::type_id::create("clock_seq");
assert(clock_seq.randomize() with {
  num_patterns == 3;
  gap_cycles == 50;
  pattern_srcid == 3'b001;  // D2D_ADAPTER
  pattern_dstid == 3'b000;  // LOCAL_DIE
});
clock_seq.start(sequencer);
```

### **2. UCIe Initialization Sequence**

#### **Class Definition**:
```systemverilog
class ucie_sb_init_seq extends ucie_sb_base_sequence;
  `uvm_object_utils(ucie_sb_init_seq)
  
  rand bit [2:0] init_srcid;           // Initialization source ID
  rand bit [2:0] init_dstid;           // Initialization destination ID
  rand bit [3:0] reset_result;         // SBINIT reset result code
  rand int num_clock_patterns;         // Clock patterns for sync
  rand bit include_done_handshake;     // Include done request/response
  
  constraint init_c { 
    num_clock_patterns inside {[1:3]};
    reset_result inside {[0:15]};      // 4-bit result field
    init_srcid != init_dstid;          // Source != Destination
  }
endclass
```

#### **Initialization Flow**:
1. **Clock Pattern Generation**: 1-3 sync patterns for timing alignment
2. **SBINIT Out of Reset**: Message with result code (Table 7-8)
3. **Optional Done Handshake**: Request/response pair for completion

#### **Message Sequence**:
```systemverilog
// Step 1: Clock patterns for synchronization
repeat(num_clock_patterns) begin
  // Generate CLOCK_PATTERN transactions
end

// Step 2: SBINIT out of reset message
trans.opcode = MESSAGE_NO_DATA;
trans.msgcode = MSG_SBINIT_OUT_OF_RESET;  // 0x91
trans.msgsubcode = SUBCODE_SBINIT_OUT_OF_RESET;  // 0x00
trans.msginfo = {12'h000, reset_result};

// Step 3: Optional done handshake
if (include_done_handshake) begin
  // SBINIT done request (0x95/0x01)
  // SBINIT done response (0x9A/0x01)
end
```

### **3. Enhanced Random Sequence**

#### **Clock Pattern Integration**:
```systemverilog
class ucie_sb_random_seq extends ucie_sb_base_sequence;
  rand bit enable_clock_patterns;  // NEW: Enable clock patterns
  
  virtual task body();
    assert(trans.randomize() with {
      opcode dist {
        [MEM_READ_32B:CFG_WRITE_64B] := 65,
        [COMPLETION_NO_DATA:COMPLETION_64B] := (enable_completions ? 20 : 0),
        [MESSAGE_NO_DATA:MESSAGE_64B] := (enable_messages ? 5 : 0),
        [MGMT_MSG_NO_DATA:MGMT_MSG_DATA] := (enable_mgmt ? 5 : 0),
        CLOCK_PATTERN := (enable_clock_patterns ? 5 : 0)  // NEW
      };
    });
  endtask
endclass
```

## 📊 **Clock Pattern Specifications**

### **Packet Format**:
- **Phase 0**: `32'h5555_5555` (alternating 1010... pattern)
- **Phase 1**: `32'h5555_5555` (alternating 1010... pattern)
- **Total Pattern**: `64'h5555555555555555`

### **Timing Characteristics**:
- **Pattern Duration**: 64 UI (80ns at 800MHz)
- **Minimum Gap**: 32 UI (40ns at 800MHz)
- **UI Period**: 1.25ns (800MHz operation)
- **Recognition**: Fixed pattern value for auto-detection

### **Protocol Compliance**:
- **UCIe Specification**: Exact pattern format per spec
- **Gap Requirements**: Minimum 32 UI low period
- **Clock Toggling**: No clock during gap (CLK/DATA both low)
- **Synchronization**: Used for receiver clock recovery

## 🎯 **Usage Scenarios**

### **1. Basic Clock Pattern Generation**:
```systemverilog
ucie_sb_clock_pattern_seq clock_seq;
clock_seq = ucie_sb_clock_pattern_seq::type_id::create("clock_seq");
assert(clock_seq.randomize() with {
  num_patterns == 1;           // Single pattern
  gap_cycles == 32;            // Minimum gap
  pattern_srcid == 3'b001;     // D2D_ADAPTER
  pattern_dstid == 3'b000;     // LOCAL_DIE
});
clock_seq.start(sequencer);
```

### **2. Multiple Synchronization Patterns**:
```systemverilog
ucie_sb_clock_pattern_seq sync_seq;
sync_seq = ucie_sb_clock_pattern_seq::type_id::create("sync_seq");
assert(sync_seq.randomize() with {
  num_patterns == 5;           // Multiple patterns
  gap_cycles == 64;            // Longer gap
  pattern_srcid == 3'b010;     // PHYSICAL_LAYER
  pattern_dstid == 3'b001;     // D2D_ADAPTER
});
sync_seq.start(sequencer);
```

### **3. Complete UCIe Initialization**:
```systemverilog
ucie_sb_init_seq init_seq;
init_seq = ucie_sb_init_seq::type_id::create("init_seq");
assert(init_seq.randomize() with {
  init_srcid == 3'b001;        // D2D_ADAPTER
  init_dstid == 3'b000;        // LOCAL_DIE
  reset_result == 4'h0;        // Success result
  num_clock_patterns == 3;     // 3 sync patterns
  include_done_handshake == 1; // Full handshake
});
init_seq.start(sequencer);
```

### **4. Mixed Traffic with Clock Patterns**:
```systemverilog
ucie_sb_random_seq random_seq;
random_seq = ucie_sb_random_seq::type_id::create("random_seq");
assert(random_seq.randomize() with {
  num_transactions == 20;
  enable_clock_patterns == 1;  // Include in random mix
  enable_messages == 1;
  enable_completions == 1;
});
random_seq.start(sequencer);
```

## 🛠️ **Example and Testing**

### **Comprehensive Test Example**:
```systemverilog
class ucie_sb_clock_pattern_test extends uvm_test;
  virtual task run_phase(uvm_phase phase);
    // Test 1: Basic clock pattern generation
    clock_seq.start(agent.sequencer);
    
    // Test 2: UCIe initialization sequence
    init_seq.start(agent.sequencer);
    
    // Test 3: Mixed traffic with clock patterns
    random_seq.start(agent.sequencer);
  endtask
endclass
```

### **Makefile Integration**:
```makefile
# Clock pattern example
clock_pattern_demo:
	@echo "Running clock pattern demonstration..."
	vcs -sverilog -ntb_opts uvm-1.2 +incdir+$(UVM_HOME)/src \
	    ucie_sb_clock_pattern_example.sv -o clock_pattern_demo
	./clock_pattern_demo +UVM_VERBOSITY=UVM_LOW \
	    +UVM_TESTNAME=ucie_sb_clock_pattern_test
```

### **Running the Demo**:
```bash
make clock_pattern_demo
```

## 📈 **Advanced Features**

### **Smart Timing Control**:
```systemverilog
// Automatic gap timing based on UI period
#(gap_cycles * 1.25ns); // 1.25ns per UI for 800MHz

// Pattern spacing for multiple patterns
if (num_patterns > 1) begin
  #(40 * 1.25ns); // 40 UI gap between patterns
end
```

### **Comprehensive Logging**:
```systemverilog
`uvm_info("CLOCK_PATTERN_SEQ", $sformatf(
  "Starting clock pattern sequence: %0d patterns, %0d gap cycles", 
  num_patterns, gap_cycles), UVM_MEDIUM)

`uvm_info("CLOCK_PATTERN_SEQ", $sformatf(
  "Generated clock pattern: srcid=%0d, dstid=%0d", 
  trans.srcid, trans.dstid), UVM_HIGH)
```

### **Integration with UCIe Messages**:
- **Seamless Flow**: Clock Pattern → SBINIT → Clock Pattern → Done Handshake
- **Timing Coordination**: Proper gaps and synchronization
- **Protocol Compliance**: Exact UCIe specification adherence

## ✅ **Validation and Benefits**

### **Protocol Compliance**:
- ✅ **UCIe Clock Pattern Format** - Exact 0x5555555555555555 pattern
- ✅ **Timing Requirements** - 64 UI duration, 32 UI minimum gap
- ✅ **Initialization Sequence** - Complete SBINIT message flow
- ✅ **Gap Behavior** - No clock toggling during gaps

### **Testing Capabilities**:
- ✅ **Link Initialization** - Complete bring-up sequence
- ✅ **Clock Recovery** - Receiver synchronization patterns
- ✅ **Timing Margin** - Variable gap testing
- ✅ **Mixed Traffic** - Clock patterns with regular transactions

### **Code Quality**:
- ✅ **Modular Design** - Reusable sequence components
- ✅ **Configurable Parameters** - Flexible pattern generation
- ✅ **Comprehensive Logging** - Detailed sequence tracking
- ✅ **Example Integration** - Complete demonstration framework

## 🚀 **Final Status**

**Status**: ✅ **CLOCK PATTERN SEQUENCES COMPLETE**

The UCIe sideband agent now provides:
- **✅ Dedicated Clock Pattern Sequence** - `ucie_sb_clock_pattern_seq`
- **✅ Complete Initialization Sequence** - `ucie_sb_init_seq` with clock patterns
- **✅ Enhanced Random Traffic** - Clock pattern integration
- **✅ Comprehensive Examples** - Full demonstration framework
- **✅ Makefile Integration** - `make clock_pattern_demo` target
- **✅ Protocol Compliance** - Exact UCIe specification adherence
- **✅ Timing Accuracy** - 800MHz operation with 1.25ns UI

**Ready for**: Complete UCIe sideband protocol testing including link initialization, clock recovery, timing synchronization, and mixed traffic scenarios! 🕐⚡✨