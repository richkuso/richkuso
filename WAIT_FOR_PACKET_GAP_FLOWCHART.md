# wait_for_packet_gap Function Flowchart

## Complete Flow Diagram

```
                                    START
                                      │
                                      ▼
                            ┌─────────────────────┐
                            │   Initialize        │
                            │ • short_gap_count=0 │
                            │ • gap_valid = 0     │
                            │ • timeout_time calc │
                            └─────────────────────┘
                                      │
                                      ▼
                            ┌─────────────────────┐
                            │  Log startup info   │
                            │ "Waiting for gap... │
                            │  precision=0.2ns"   │
                            └─────────────────────┘
                                      │
                                      ▼
                          ┌─────────────────────────┐
                          │   WAIT FOR GAP START    │
                          │ While (CLK≠0 OR DATA≠0) │
                          └─────────────────────────┘
                                      │
                                      ▼
                            ┌─────────────────────┐
                            │   Reset Check?      │
                            │  (vif.sb_reset)     │
                            └─────────────────────┘
                                   Yes │    │ No
                          ┌─────────────┘    │
                          ▼                  ▼
                  ┌─────────────────┐   ┌─────────────┐
                  │ Log: "Reset     │   │   #0.2ns    │
                  │  detected..."   │   │   delay     │
                  │     RETURN      │   └─────────────┘
                  └─────────────────┘         │
                                              │
                                              ▼
                                    ┌─────────────────┐
                                    │ Both signals    │
                                    │ now low?        │
                                    └─────────────────┘
                                         No │    │ Yes
                                    ┌───────┘    │
                                    │            ▼
                                    │  ┌─────────────────────┐
                                    │  │ gap_start_time =    │
                                    │  │     $time           │
                                    │  │ Log: "Gap started"  │
                                    │  └─────────────────────┘
                                    │            │
                                    │            ▼
                                    │  ┌─────────────────────┐
                                    │  │   MAIN GAP MONITOR  │
                                    │  │  While (!gap_valid) │
                                    │  └─────────────────────┘
                                    │            │
                                    │            ▼
                                    │  ┌─────────────────────┐
                                    │  │   Reset Check?      │
                                    │  │  (vif.sb_reset)     │
                                    │  └─────────────────────┘
                                    │         Yes │    │ No
                                    │    ┌────────┘    │
                                    │    ▼             ▼
                                    │ ┌─────────────┐ ┌─────────────┐
                                    │ │Log: "Reset  │ │   #0.2ns    │
                                    │ │ detected"   │ │   delay     │
                                    │ │   RETURN    │ └─────────────┘
                                    │ └─────────────┘       │
                                    │                       ▼
                                    │             ┌─────────────────────┐
                                    │             │ Calculate:          │
                                    │             │ • current_time      │
                                    │             │ • gap_duration      │
                                    │             │ • ui_count          │
                                    │             └─────────────────────┘
                                    │                       │
                                    │                       ▼
                                    │             ┌─────────────────────┐
                                    │             │   Timeout Check?    │
                                    │             │ (duration > timeout)│
                                    │             └─────────────────────┘
                                    │                    Yes │    │ No
                                    │               ┌────────┘    │
                                    │               ▼             ▼
                                    │      ┌─────────────────┐   ┌─────────────────────┐
                                    │      │ Log: "Timeout"  │   │   Signal Change?    │
                                    │      │ gap_valid = 1   │   │ (CLK=1 OR DATA=1)   │
                                    │      │     BREAK       │   └─────────────────────┘
                                    │      └─────────────────┘          No │    │ Yes
                                    │                                ┌─────┘    │
                                    │                                │          ▼
                                    │                                │ ┌─────────────────────┐
                                    │                                │ │   Gap Duration      │
                                    │                                │ │   Check             │
                                    │                                │ │ (ui_count >= 32?)   │
                                    │                                │ └─────────────────────┘
                                    │                                │        Yes │    │ No
                                    │                                │   ┌────────┘    │
                                    │                                │   ▼             ▼
                                    │                                │ ┌─────────────┐ ┌─────────────────┐
                                    │                                │ │Log: "Valid  │ │short_gap_count++│
                                    │                                │ │ gap found"  │ │Log: "Gap too    │
                                    │                                │ │gap_valid=1  │ │short - attempt" │
                                    │                                │ └─────────────┘ └─────────────────┘
                                    │                                │                         │
                                    │                                │                         ▼
                                    │                                │               ┌─────────────────────┐
                                    │                                │               │  Retry Limit Check  │
                                    │                                │               │(short_gap_count>=5?)│
                                    │                                │               └─────────────────────┘
                                    │                                │                      Yes │    │ No
                                    │                                │                 ┌────────┘    │
                                    │                                │                 ▼             ▼
                                    │                                │        ┌─────────────────┐   ┌─────────────────────┐
                                    │                                │        │ Log: "Too many  │   │   WAIT FOR SIGNALS  │
                                    │                                │        │ short gaps"     │   │     TO GO LOW       │
                                    │                                │        │ protocol_errors++│   │While(CLK≠0|DATA≠0) │
                                    │                                │        │ gap_valid = 1   │   └─────────────────────┘
                                    │                                │        │     BREAK       │             │
                                    │                                │        └─────────────────┘             ▼
                                    │                                │                                ┌─────────────────────┐
                                    │                                │                                │   Reset Check?      │
                                    │                                │                                │  (vif.sb_reset)     │
                                    │                                │                                └─────────────────────┘
                                    │                                │                                     Yes │    │ No
                                    │                                │                            ┌────────────┘    │
                                    │                                │                            ▼                 ▼
                                    │                                │                   ┌─────────────────┐ ┌─────────────┐
                                    │                                │                   │ Log: "Reset     │ │   #0.2ns    │
                                    │                                │                   │  detected"      │ │   delay     │
                                    │                                │                   │    RETURN       │ └─────────────┘
                                    │                                │                   └─────────────────┘       │
                                    │                                │                                               │
                                    │                                │                                               ▼
                                    │                                │                                     ┌─────────────────┐
                                    │                                │                                     │ Both signals    │
                                    │                                │                                     │ now low?        │
                                    │                                │                                     └─────────────────┘
                                    │                                │                                          No │    │ Yes
                                    │                                │                                     ┌───────┘    │
                                    │                                │                                     │            ▼
                                    │                                │                              ┌─────────────────────┐
                                    │                                │                              │gap_start_time=$time │
                                    │                                │                              │Log: "Gap restarted" │
                                    │                                │                              └─────────────────────┘
                                    │                                │                                        │
                                    │                                ▼                                        │
                                    │                      ┌─────────────────────┐                          │
                                    │                      │ Progress Logging    │                          │
                                    │                      │ (ui_count > 32 &&   │                          │
                                    │                      │  ui_count % 64 = 0) │                          │
                                    │                      └─────────────────────┘                          │
                                    │                                │                                        │
                                    └────────────────────────────────┼────────────────────────────────────────┘
                                                                     │
                                                                     ▼
                                                           ┌─────────────────────┐
                                                           │   COMPLETION        │
                                                           │ Log final message   │
                                                           │ with retry count    │
                                                           └─────────────────────┘
                                                                     │
                                                                     ▼
                                                                    END
```

## Simplified Decision Tree

```
START
├── Initialize variables (short_gap_count=0, gap_valid=0)
├── Log startup message
├── PHASE 1: Wait for Gap Start
│   ├── While (CLK≠0 OR DATA≠0)
│   │   ├── Reset? → RETURN
│   │   └── #0.2ns delay → Continue
│   └── Both signals low → Record gap_start_time
├── PHASE 2: Monitor Gap Duration
│   └── While (!gap_valid)
│       ├── Reset? → RETURN
│       ├── #0.2ns delay
│       ├── Calculate ui_count
│       ├── Timeout (>1000 UI)? → Force valid, BREAK
│       ├── Signal change (CLK=1 OR DATA=1)?
│       │   ├── YES: Gap ended
│       │   │   ├── ui_count >= 32? → Valid gap, EXIT
│       │   │   └── ui_count < 32? → Short gap
│       │   │       ├── short_gap_count++
│       │   │       ├── short_gap_count >= 5? → Error, Force valid, EXIT
│       │   │       └── RESTART: Wait for signals low, reset timer
│       │   └── NO: Continue monitoring
│       └── Progress logging (every 64 UI)
└── Log completion message with retry count
```

## Key Decision Points

### 1. **Reset Detection Points** (3 locations)
- **Gap Start Wait**: Before gap timing begins
- **Gap Monitoring**: During active gap measurement  
- **Gap Restart**: During retry signal waiting

### 2. **Gap Validation Logic**
```
Gap End Detected (CLK=1 OR DATA=1)
├── ui_count >= 32? → SUCCESS (gap_valid = 1)
└── ui_count < 32? → SHORT GAP
    ├── short_gap_count < 5? → RETRY
    └── short_gap_count >= 5? → ERROR + FORCE ACCEPT
```

### 3. **Retry Mechanism Flow**
```
Short Gap Detected
├── Increment short_gap_count
├── Log warning with attempt number
├── Check retry limit (>= 5)
│   ├── YES: Log error, increment protocol_errors, force valid
│   └── NO: Wait for signals low, restart timing
└── Continue monitoring with fresh timer
```

### 4. **Exit Conditions** (5 ways to exit)
1. **Reset during gap start wait** → RETURN
2. **Reset during gap monitoring** → RETURN  
3. **Reset during gap restart** → RETURN
4. **Valid gap found** (≥32 UI) → Normal completion
5. **Timeout or retry limit** → Forced completion

## Timing Precision Details

### **Monitoring Frequency**: 0.2ns intervals
### **Reset Responsiveness**: Up to 0.2ns detection latency
### **Gap Measurement**: Sub-nanosecond precision with UI calculation

## Loop Control Summary

### **Primary Loop**: `while (!gap_valid)`
- **Entry**: After gap start detected
- **Exit**: Valid gap found, timeout, or retry limit reached

### **Nested Loops**: 
1. **Gap Start Wait**: `while (CLK≠0 OR DATA≠0)`
2. **Gap Restart Wait**: `while (CLK≠0 OR DATA≠0)` (during retries)

### **Safety Mechanisms**:
- **Reset checks** in all loops
- **Timeout protection** (1000 UI maximum)
- **Retry limit** (5 attempts maximum)
- **0.2ns delays** prevent infinite spinning

This flowchart shows the complete decision logic, error handling, and safety mechanisms that make the `wait_for_packet_gap` function robust and reliable for UCIe protocol validation!