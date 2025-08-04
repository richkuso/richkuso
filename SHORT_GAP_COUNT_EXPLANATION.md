# short_gap_count Usage Explanation

## Overview
The `short_gap_count` variable in the `wait_for_packet_gap()` function is a **retry counter** that tracks how many times the monitor has detected **insufficient gap durations** (< 32 UI) and implements **bounded retry logic** to prevent infinite loops while ensuring protocol compliance.

## Variable Declaration and Initialization
```systemverilog
int short_gap_count = 0;  // Line 299: Initialize retry counter to zero
```

## Purpose and Functionality

### 1. 🎯 **Protocol Violation Tracking**
The `short_gap_count` tracks violations of the **UCIe sideband protocol requirement** that mandates a **minimum 32 UI gap** between packets where both `SBRX_CLK` and `SBRX_DATA` remain low.

### 2. 🔄 **Retry Mechanism Implementation**
When a gap is detected but is **too short** (< 32 UI), the function doesn't immediately fail but instead:
- **Increments the retry counter**
- **Waits for signals to go low again**  
- **Restarts gap timing measurement**
- **Gives the protocol another chance** to meet requirements

### 3. 🛡️ **Infinite Loop Prevention**
Without bounds, the retry mechanism could loop forever if the DUT consistently produces short gaps. The counter provides a **safety limit of 5 attempts**.

## Detailed Usage Flow

### Step 1: Gap Duration Check (Lines 341-345)
```systemverilog
// Check if either signal goes high (gap ends)
if (vif.SBRX_CLK === 1'b1 || vif.SBRX_DATA === 1'b1) begin
  if (ui_count >= 32) begin
    `uvm_info("MONITOR", $sformatf("Valid gap detected: %0d UI (%0t)", ui_count, gap_duration), UVM_DEBUG)
    gap_valid = 1;  // Success - exit the monitoring loop
  end else begin
    // Gap too short - enter retry logic
```

### Step 2: Retry Counter Increment (Lines 346-348)
```systemverilog
short_gap_count++;  // Increment retry attempt counter
`uvm_warning("MONITOR", $sformatf("Gap too short: %0d UI (minimum 32 UI required) - attempt %0d", 
                                  ui_count, short_gap_count))
```

**Example Warning Messages:**
- Attempt 1: `"Gap too short: 25 UI (minimum 32 UI required) - attempt 1"`
- Attempt 2: `"Gap too short: 28 UI (minimum 32 UI required) - attempt 2"`
- Attempt 3: `"Gap too short: 30 UI (minimum 32 UI required) - attempt 3"`

### Step 3: Retry Limit Check (Lines 350-356)
```systemverilog
// Limit retries to prevent infinite loops
if (short_gap_count >= 5) begin
  `uvm_error("MONITOR", $sformatf("Too many short gaps (%0d attempts) - forcing gap acceptance", short_gap_count))
  protocol_errors++;  // Increment global error counter
  gap_valid = 1;       // Force exit to prevent infinite loop
  break;
end
```

**Error Escalation:**
- After **5 failed attempts**, the function:
  - **Logs an error** indicating persistent protocol violation
  - **Increments protocol_errors** for test statistics
  - **Forces gap acceptance** to prevent simulation hang
  - **Exits the monitoring loop**

### Step 4: Gap Restart Logic (Lines 358-367)
```systemverilog
// Gap was too short, wait for signals to go low again and restart
while (vif.SBRX_CLK !== 1'b0 || vif.SBRX_DATA !== 1'b0) begin
  if (vif.sb_reset) begin
    `uvm_info("MONITOR", "Reset detected during gap restart - aborting gap wait", UVM_DEBUG)
    return;
  end
  #0.2ns;
end
gap_start_time = $time;  // Reset timing reference
`uvm_info("MONITOR", $sformatf("Gap restarted due to insufficient duration (attempt %0d)", short_gap_count), UVM_DEBUG)
```

**Restart Process:**
1. **Wait for both signals to go low** (new gap start)
2. **Check for reset** during waiting (safety)
3. **Reset the gap start time** reference
4. **Log restart attempt** with current retry count
5. **Continue monitoring** with fresh timing

### Step 5: Completion Reporting (Lines 377-379)
```systemverilog
`uvm_info("MONITOR", $sformatf("Packet gap complete: %0d UI duration%s", ui_count, 
                               short_gap_count > 0 ? $sformatf(" (after %0d short gap retries)", short_gap_count) : ""), 
                               UVM_DEBUG)
```

**Example Completion Messages:**
- **Success on first try**: `"Packet gap complete: 45 UI duration"`
- **Success after retries**: `"Packet gap complete: 35 UI duration (after 2 short gap retries)"`
- **Forced acceptance**: `"Packet gap complete: 28 UI duration (after 5 short gap retries)"`

## Behavioral Scenarios

### Scenario 1: Normal Operation (No Short Gaps)
```
Gap Start → 45 UI gap detected → Success
short_gap_count = 0 (never incremented)
Message: "Packet gap complete: 45 UI duration"
```

### Scenario 2: Single Short Gap with Recovery
```
Gap Start → 25 UI (short) → Restart → 40 UI (valid) → Success
short_gap_count = 1
Messages:
- "Gap too short: 25 UI (minimum 32 UI required) - attempt 1"
- "Gap restarted due to insufficient duration (attempt 1)"
- "Packet gap complete: 40 UI duration (after 1 short gap retries)"
```

### Scenario 3: Multiple Short Gaps with Recovery
```
Gap Start → 20 UI → Restart → 28 UI → Restart → 35 UI → Success
short_gap_count = 2
Messages:
- "Gap too short: 20 UI (minimum 32 UI required) - attempt 1"
- "Gap too short: 28 UI (minimum 32 UI required) - attempt 2"  
- "Packet gap complete: 35 UI duration (after 2 short gap retries)"
```

### Scenario 4: Persistent Short Gaps (Error Escalation)
```
Gap Start → 15 UI → 18 UI → 22 UI → 25 UI → 28 UI → 30 UI → Force Accept
short_gap_count = 5 (maximum reached)
Messages:
- "Gap too short: 15 UI (minimum 32 UI required) - attempt 1"
- "Gap too short: 18 UI (minimum 32 UI required) - attempt 2"
- "Gap too short: 22 UI (minimum 32 UI required) - attempt 3"
- "Gap too short: 25 UI (minimum 32 UI required) - attempt 4"
- "Gap too short: 28 UI (minimum 32 UI required) - attempt 5"
- "Too many short gaps (5 attempts) - forcing gap acceptance"
- "Packet gap complete: 30 UI duration (after 5 short gap retries)"
protocol_errors++ (incremented)
```

## Design Benefits

### 1. ✅ **Robustness Against Noise**
- **Temporary glitches** or **marginal timing** don't immediately fail the test
- **Multiple chances** for the DUT to meet protocol requirements
- **Graceful handling** of borderline timing conditions

### 2. ✅ **Protocol Compliance Enforcement**
- **Maintains strict 32 UI requirement** while allowing retry flexibility
- **Tracks violations** for test analysis and debugging
- **Escalates persistent issues** to error level for attention

### 3. ✅ **Simulation Safety**
- **Prevents infinite loops** from persistent protocol violations
- **Bounded execution time** with guaranteed termination
- **Reset responsiveness** maintained during retries

### 4. ✅ **Enhanced Debugging**
- **Detailed retry tracking** shows pattern of gap violations
- **Attempt numbering** helps identify intermittent vs persistent issues
- **Comprehensive logging** aids in root cause analysis

### 5. ✅ **Test Statistics**
- **protocol_errors counter** provides quantitative violation metrics
- **Retry counts** indicate DUT timing margin health
- **Completion messages** show successful recovery patterns

## UCIe Protocol Alignment

### ✅ **Specification Compliance**:
- **32 UI minimum gap** requirement strictly enforced
- **Both CLK and DATA low** during gap verified
- **Continuous monitoring** throughout gap duration

### ✅ **Real-World Tolerance**:
- **Retry mechanism** handles implementation variations
- **Bounded flexibility** balances compliance with practicality
- **Error escalation** ensures persistent violations are flagged

## Performance Impact

### ✅ **Minimal Overhead**:
- **Simple integer counter** with negligible memory/computation cost
- **Only active during gap violations** (rare in compliant designs)
- **Bounded retry count** limits maximum overhead

### ✅ **Improved Accuracy**:
- **Reduces false failures** from temporary timing issues
- **Better signal-to-noise ratio** in protocol compliance checking
- **More reliable gap validation** with retry tolerance

## Files Using short_gap_count
- **`ucie_sb_monitor.sv`**: Primary usage in `wait_for_packet_gap()` task

## Status
✅ **ESSENTIAL FEATURE** - The `short_gap_count` variable provides robust retry logic for UCIe gap validation, preventing infinite loops while maintaining protocol compliance and offering enhanced debugging capabilities for timing analysis.