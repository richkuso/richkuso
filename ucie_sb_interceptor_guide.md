# UCIe Sideband Transaction Interceptor - Architecture & Transaction Flow Guide

## 🏗️ **Interceptor Structure Overview**

The UCIe Sideband Transaction Interceptor is a sophisticated UVM component designed to monitor, intercept, and modify UCIe sideband transactions in real-time. It provides intelligent transaction handling with configurable matching criteria and custom response generation.

---

## 🔧 **Component Architecture**

### **📦 Core Components**

```
┌─────────────────────────────────────────────────────────────────┐
│                UCIe Sideband Transaction Interceptor            │
├─────────────────────────────────────────────────────────────────┤
│  ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐  │
│  │   TX Agent      │  │   RX Agent      │  │  Driver Agent   │  │
│  │   (Monitor)     │  │   (Monitor)     │  │   (Active)      │  │
│  │                 │  │                 │  │                 │  │
│  │ • CFG_READ_32B  │  │ • COMPLETION_   │  │ • Custom        │  │
│  │   Detection     │  │   32B Monitor   │  │   Completion    │  │
│  │ • TX Path       │  │ • RX Path       │  │   Generation    │  │
│  │   Monitoring    │  │   Monitoring    │  │ • Response TX   │  │
│  └─────────────────┘  └─────────────────┘  └─────────────────┘  │
│           │                     │                     ▲          │
│           ▼                     ▼                     │          │
│  ┌─────────────────────────────────────────────────────────────┐ │
│  │              Transaction Processing Core               │ │
│  │                                                       │ │
│  │  ┌─────────────────┐  ┌─────────────────┐            │ │
│  │  │ Pending Trans   │  │ Matching        │            │ │
│  │  │ Tracking        │  │ Engine          │            │ │
│  │  │                 │  │                 │            │ │
│  │  │ • Tag-indexed   │  │ • Address       │            │ │
│  │  │   Queue         │  │   Matching      │            │ │
│  │  │ • Timeout       │  │ • Source ID     │            │ │
│  │  │   Management    │  │   Filtering     │            │ │
│  │  │ • Cleanup       │  │ • Tag-based     │            │ │
│  │  └─────────────────┘  └─────────────────┘            │ │
│  └─────────────────────────────────────────────────────────────┘ │
├─────────────────────────────────────────────────────────────────┤
│  ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐  │
│  │  Configuration  │  │   Statistics    │  │  Analysis       │  │
│  │   Management    │  │   Collection    │  │   Ports         │  │
│  │                 │  │                 │  │                 │  │
│  │ • Matching      │  │ • Performance   │  │ • TX Monitor    │  │
│  │   Criteria      │  │   Metrics       │  │ • RX Monitor    │  │
│  │ • Response      │  │ • Error         │  │ • Intercepted   │  │
│  │   Generation    │  │   Tracking      │  │   Transactions  │  │
│  └─────────────────┘  └─────────────────┘  └─────────────────┘  │
└─────────────────────────────────────────────────────────────────┘
```

### **🔗 Class Hierarchy**

```systemverilog
ucie_sb_transaction_interceptor (extends uvm_component)
├── ucie_sb_interceptor_config (extends uvm_object)
│   ├── Operational Mode Control
│   ├── Matching Criteria Configuration  
│   ├── Completion Generation Parameters
│   └── Timing and Performance Parameters
│
├── ucie_sb_pending_transaction (extends uvm_object)
│   ├── Transaction Identification Fields
│   ├── Timestamp Management
│   └── Utility Methods
│
└── Main Interceptor Infrastructure
    ├── Agent Integration (tx_agent, rx_agent, driver_agent)
    ├── Transaction Tracking (pending_transactions[], pending_queue[])
    ├── Statistics Collection (counters, performance metrics)
    └── Analysis Port Connectivity (tx_monitor_ap, rx_monitor_ap, intercepted_ap)
```

---

## 🔄 **Transaction Flow Architecture**

### **📊 High-Level Transaction Flow**

```
DUT/Testbench                    Interceptor                    Custom Response
     │                               │                               │
     │ ①CFG_READ_32B                │                               │
     ├──────────────────────────────►│                               │
     │    (TX Path)                  │ ②Match Check                 │
     │                               │ ┌─────────────────────────┐   │
     │                               │ │ Address: 0x100000-      │   │
     │                               │ │ Source ID: 0x1          │   │
     │                               │ │ Tag: 0x10-0x1F          │   │
     │                               │ └─────────────────────────┘   │
     │                               │                               │
     │                               │ ③Store Pending              │
     │                               │ ┌─────────────────────────┐   │
     │                               │ │ pending_queue[tag] =    │   │
     │                               │ │ {addr, srcid, dstid,    │   │
     │                               │ │  be, timestamp}         │   │
     │                               │ └─────────────────────────┘   │
     │                               │                               │
     │ ④COMPLETION_32B               │                               │
     ├──────────────────────────────►│                               │
     │    (RX Path)                  │ ⑤Lookup Pending             │
     │                               │ ┌─────────────────────────┐   │
     │                               │ │ Find by tag & srcid     │   │
     │                               │ │ Check if matched        │   │
     │                               │ └─────────────────────────┘   │
     │                               │                               │
     │                               │ ⑥Generate Custom            │
     │                               │ ┌─────────────────────────┐   │
     │                               │ │ Custom data: 0xDEADBEEF │   │
     │                               │ │ Status: SUCCESS         │   │
     │                               │ │ Swap src/dst IDs        │   │
     │                               │ └─────────────────────────┘   │
     │                               │                               │
     │                               │ ⑦Send Response              │
     │                               ├──────────────────────────────►│
     │                               │                               │
     │ ⑧Custom Completion            │                               │
     │◄──────────────────────────────┼───────────────────────────────┤
     │                               │                               │
```

### **⚙️ Detailed Transaction Processing Flow**

#### **Phase 1: CFG Read Detection**
```systemverilog
task monitor_tx_transactions();
  forever begin
    tx_agent.monitor.ap.get(trans);           // ① Get transaction from TX monitor
    tx_monitor_ap.write(trans);               // Forward to analysis port
    
    if (trans.opcode == CFG_READ_32B) begin   // ② Check for CFG read
      process_cfg_read(trans);                // ③ Process CFG read
    end
  end
endtask
```

#### **Phase 2: Transaction Matching & Storage**
```systemverilog
task process_cfg_read(ucie_sb_transaction trans);
  bit matches = matches_criteria(trans);     // ④ Check matching criteria
  
  if (matches && cfg.enable_interception) begin
    pending = ucie_sb_pending_transaction::type_id::create("pending");
    pending.tag = trans.tag;                 // ⑤ Store transaction details
    pending.srcid = trans.srcid;
    pending.dstid = trans.dstid;
    pending.addr = trans.addr;
    pending.matched = 1;
    
    pending_queue[trans.tag] = pending;      // ⑥ Store in tag-indexed queue
    pending_transactions.push_back(pending); // ⑦ Add to cleanup list
  end
endtask
```

#### **Phase 3: Completion Interception**
```systemverilog
task monitor_rx_transactions();
  forever begin
    rx_agent.monitor.ap.get(trans);          // ⑧ Get completion from RX monitor
    rx_monitor_ap.write(trans);              // Forward to analysis port
    
    if (trans.opcode == COMPLETION_32B) begin // ⑨ Check for completion
      process_completion(trans);             // ⑩ Process completion
    end
  end
endtask
```

#### **Phase 4: Custom Response Generation**
```systemverilog
task process_completion(ucie_sb_transaction trans);
  pending = find_pending_transaction(trans.tag, trans.srcid); // ⑪ Find matching request
  
  if (pending != null && pending.matched) begin
    custom_completion = generate_custom_completion(pending);   // ⑫ Generate custom response
    send_completion(custom_completion);                        // ⑬ Send via driver
    completions_modified++;                                    // ⑭ Update statistics
    
    // Clean up pending transaction
    pending_queue.delete(trans.tag);                          // ⑮ Remove from tracking
  end else begin
    send_completion(trans);                                    // ⑯ Pass through original
    completions_passed_through++;
  end
endtask
```

---

## 🎯 **Matching Criteria Engine**

### **🔍 Multi-Criteria Matching**

```systemverilog
function bit matches_criteria(ucie_sb_transaction trans);
  bit addr_match = 1;
  bit srcid_match = 1;
  bit tag_match = 1;
  
  // Address-based matching
  if (cfg.enable_addr_match) begin
    addr_match = ((trans.addr & cfg.match_addr_mask) == 
                  (cfg.match_addr_base & cfg.match_addr_mask));
  end
  
  // Source ID matching  
  if (cfg.enable_srcid_match) begin
    srcid_match = (trans.srcid == cfg.match_srcid);
  end
  
  // Tag-based matching
  if (cfg.enable_tag_match) begin
    tag_match = ((trans.tag & cfg.match_tag_mask) == 
                 (cfg.match_tag_base & cfg.match_tag_mask));
  end
  
  return (addr_match && srcid_match && tag_match);
endfunction
```

### **📋 Matching Examples**

| Criteria | Configuration | Transaction | Match? | Reason |
|----------|--------------|-------------|--------|---------|
| **Address** | Base: 0x100000<br>Mask: 0xFFF000 | Addr: 0x100800 | ✅ Yes | 0x100800 & 0xFFF000 = 0x100000 |
| **Address** | Base: 0x100000<br>Mask: 0xFFF000 | Addr: 0x200000 | ❌ No | 0x200000 & 0xFFF000 ≠ 0x100000 |
| **Source ID** | Match: 0x1 | SrcID: 0x1 | ✅ Yes | Exact match |
| **Tag** | Base: 0x10<br>Mask: 0x1F | Tag: 0x15 | ✅ Yes | 0x15 & 0x1F = 0x15, 0x10 & 0x1F = 0x10 |

---

## 📊 **Pending Transaction Management**

### **🗃️ Storage Architecture**

```systemverilog
// Dual storage for efficiency
ucie_sb_pending_transaction pending_transactions[$];     // Sequential list for cleanup
ucie_sb_pending_transaction pending_queue[bit [4:0]];    // Tag-indexed for fast lookup

// Storage operation
pending_queue[trans.tag] = pending;           // O(1) insertion
pending_transactions.push_back(pending);      // O(1) append

// Lookup operation  
pending = pending_queue[completion.tag];      // O(1) lookup by tag

// Cleanup operation (periodic)
for (int i = pending_transactions.size() - 1; i >= 0; i--) begin
  if (pending_transactions[i].is_expired(cfg.timeout_ns)) begin
    expired = pending_transactions[i];
    pending_queue.delete(expired.tag);        // Remove from hash
    pending_transactions.delete(i);           // Remove from list
  end
end
```

### **⏰ Timeout Management**

```systemverilog
class ucie_sb_pending_transaction extends uvm_object;
  realtime timestamp;                         // Transaction creation time
  
  function new(string name = "ucie_sb_pending_transaction");
    super.new(name);
    timestamp = $realtime;                    // Capture current time
  endfunction
  
  function bit is_expired(real timeout_ns);
    realtime current_time = $realtime;
    return ((current_time - timestamp) > (timeout_ns * 1ns));
  endfunction
endclass
```

---

## 🎨 **Custom Completion Generation**

### **🔧 Response Construction**

```systemverilog
function ucie_sb_transaction generate_custom_completion(ucie_sb_pending_transaction pending);
  ucie_sb_transaction completion;
  
  completion = ucie_sb_transaction::type_id::create("custom_completion");
  
  // UCIe protocol compliance
  completion.opcode = COMPLETION_32B;
  completion.srcid = pending.dstid;           // Original destination becomes source
  completion.dstid = pending.srcid;           // Original source becomes destination  
  completion.tag = pending.tag;               // Match original tag
  completion.be = pending.be;                 // Match original byte enables
  
  // Custom response data
  if (cfg.generate_error_completion) begin
    completion.status[2:0] = cfg.error_status;
    completion.data = 32'h0;                  // No data for error completions
  end else begin
    completion.status[2:0] = cfg.custom_completion_status;
    completion.data[31:0] = cfg.custom_completion_data;  // Custom data payload
  end
  
  completion.update_packet_info();            // Calculate packet fields
  return completion;
endfunction
```

### **📈 Response Types**

| Response Type | Status | Data | Use Case |
|---------------|--------|------|----------|
| **Success** | 3'b000 | Custom Data | Normal interception |
| **Unsupported Request** | 3'b001 | 32'h0 | Error simulation |
| **Completer Abort** | 3'b100 | 32'h0 | Fault injection |
| **Custom Debug** | 3'b000 | 32'hDEADBEEF | Debug/test patterns |

---

## 📊 **Statistics & Performance Monitoring**

### **📈 Performance Metrics**

```systemverilog
// Transaction counters
int cfg_reads_detected = 0;                  // CFG read transactions detected
int completions_intercepted = 0;             // Completions intercepted  
int completions_modified = 0;                // Completions modified
int completions_passed_through = 0;          // Completions passed through
int transactions_timed_out = 0;              // Timed out transactions

// Performance metrics
realtime total_intercept_time = 0;           // Total interception processing time
realtime max_intercept_time = 0;             // Maximum interception time
realtime min_intercept_time = 0;             // Minimum interception time

// Statistics reporting
function void print_statistics();
  real avg_intercept_time = total_intercept_time / completions_intercepted / 1ns;
  
  `uvm_info("INTERCEPTOR", "=== Transaction Interceptor Statistics ===", UVM_LOW)
  `uvm_info("INTERCEPTOR", $sformatf("CFG reads detected: %0d", cfg_reads_detected), UVM_LOW)
  `uvm_info("INTERCEPTOR", $sformatf("Completions modified: %0d", completions_modified), UVM_LOW)
  `uvm_info("INTERCEPTOR", $sformatf("Average intercept time: %0.3f ns", avg_intercept_time), UVM_LOW)
endfunction
```

---

## 🔧 **Configuration Management**

### **⚙️ Configuration Structure**

```systemverilog
class ucie_sb_interceptor_config extends uvm_object;
  // Operational controls
  bit enable_interception = 1;               // Master enable/disable
  bit pass_through_mode = 0;                 // Transparent forwarding mode
  bit enable_debug = 1;                      // Debug logging
  
  // Matching criteria
  bit [23:0] match_addr_base = 24'h100000;   // Address range base
  bit [23:0] match_addr_mask = 24'hFFF000;   // Address mask (4KB blocks)
  bit [2:0] match_srcid = 3'h1;              // Source ID filter
  bit [4:0] match_tag_base = 5'h10;          // Tag range base
  
  // Response generation
  bit [31:0] custom_completion_data = 32'hDEADBEEF;  // Custom data payload
  bit [2:0] custom_completion_status = 3'b000;       // Success status
  bit generate_error_completion = 0;                 // Error mode
  
  // Timing parameters
  int completion_delay_cycles = 10;          // Response delay
  real timeout_ns = 1000.0;                  // Transaction timeout
endclass
```

### **🎛️ Configuration Presets**

```systemverilog
// Address-based interception (4KB range at 1MB)
cfg.set_address_range(24'h100000, 24'h1000);
cfg.set_custom_data(32'hCAFEBABE);

// Debug mode with extended timeouts
cfg.set_debug_mode();  // timeout_ns = 10000.0, enable_debug = 1

// Pass-through mode for debugging
cfg.set_pass_through_mode();  // enable_interception = 0, pass_through_mode = 1
```

---

## 🚀 **Integration Example**

### **🏗️ Testbench Integration**

```systemverilog
class ucie_sb_interceptor_env extends uvm_env;
  ucie_sb_agent tx_agent;                    // Monitor CFG reads
  ucie_sb_agent rx_agent;                    // Monitor completions
  ucie_sb_agent response_agent;              // Send custom responses
  ucie_sb_transaction_interceptor interceptor;
  
  function void connect_phase(uvm_phase phase);
    // Connect monitors to interceptor
    tx_agent.monitor.ap.connect(interceptor.tx_monitor_ap);
    rx_agent.monitor.ap.connect(interceptor.rx_monitor_ap);
    
    // Connect interceptor to response driver
    // (via TLM FIFOs in actual implementation)
  endfunction
endclass

class interceptor_test extends uvm_test;
  virtual task run_phase(uvm_phase phase);
    // Send CFG reads to intercepted address range
    for (int i = 0; i < 10; i++) begin
      send_cfg_read(24'h100000 + (i*4), i[4:0]);  // Will be intercepted
      send_cfg_read(24'h200000 + (i*4), i[4:0]);  // Will pass through
      #1us;
    end
  endtask
endclass
```

---

## 🎯 **Key Benefits & Use Cases**

### **✅ Benefits**

- **🔍 Selective Interception**: Only intercepts transactions matching specific criteria
- **⚡ High Performance**: O(1) lookup using tag-indexed queues  
- **🛡️ Robust**: Timeout management prevents memory leaks
- **🔧 Configurable**: Flexible matching and response generation
- **📊 Observable**: Comprehensive statistics and analysis ports
- **🐛 Debuggable**: Pass-through mode and detailed logging

### **🎯 Use Cases**

- **Fault Injection**: Generate error completions for robustness testing
- **Performance Testing**: Custom response timing and data patterns
- **Protocol Validation**: Verify correct handling of various completion scenarios  
- **Debug Support**: Intercept and analyze specific transaction flows
- **Regression Testing**: Consistent response patterns for automated testing
- **Coverage Enhancement**: Force specific corner cases and error conditions

---

This comprehensive architecture enables sophisticated verification scenarios while maintaining high performance and UCIe protocol compliance.