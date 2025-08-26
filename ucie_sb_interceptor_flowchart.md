# UCIe Sideband Transaction Interceptor - Flow Chart

## 🔄 **Transaction Interceptor Decision Flow**

### **📊 Main Flow Chart**

```mermaid
flowchart TD
    A[Start Interceptor] --> B[Initialize Agents]
    B --> C{TX Agent Monitor<br/>Detects Transaction?}
    
    C -->|Yes| D{Is CFG_READ_32B<br/>Transaction?}
    C -->|No| C
    
    D -->|No| E[Forward Transaction<br/>to Driver Agent]
    D -->|Yes| F{Does Transaction<br/>Match Criteria?}
    
    F -->|No| E
    F -->|Yes| G[Store Pending Transaction<br/>in Tag-indexed Queue]
    
    G --> H[Set Transaction as<br/>Matched/Intercepted]
    H --> I[Wait for RX Agent<br/>to Monitor Completion]
    
    I --> J{RX Agent Monitor<br/>Detects COMPLETION_32B?}
    
    J -->|No| K{Timeout<br/>Expired?}
    J -->|Yes| L{Find Matching Pending<br/>Transaction by Tag?}
    
    K -->|No| J
    K -->|Yes| M[Remove Expired<br/>Transaction from Queue]
    M --> N[Log Timeout Event]
    N --> C
    
    L -->|Not Found| O[Forward Original<br/>Completion via Driver]
    L -->|Found & Matched| P[Intercept Original<br/>Completion]
    
    P --> Q[Generate Custom<br/>Completion Response]
    Q --> R[Send Custom Completion<br/>via Driver Agent]
    R --> S[Remove Transaction<br/>from Pending Queue]
    S --> T[Update Statistics<br/>completions_modified++]
    
    O --> U[Update Statistics<br/>completions_passed_through++]
    E --> V[Update Statistics<br/>transactions_forwarded++]
    
    T --> C
    U --> C
    V --> C
```

---

## 🔍 **Detailed Decision Logic**

### **📋 TX Agent Monitoring Flow**

```mermaid
flowchart TD
    A[TX Agent Monitor<br/>Receives Transaction] --> B{Transaction Type<br/>Check}
    
    B -->|CFG_READ_32B| C[Extract Transaction<br/>Details]
    B -->|Other Types| D[Forward to<br/>Driver Agent]
    
    C --> E[Check Matching<br/>Criteria]
    E --> F{Address Match?}
    
    F -->|Yes| G{Source ID Match?}
    F -->|No| H[Forward to<br/>Driver Agent]
    
    G -->|Yes| I{Tag Match?}
    G -->|No| H
    
    I -->|Yes| J[Create Pending<br/>Transaction Entry]
    I -->|No| H
    
    J --> K[Store in Tag-indexed<br/>Queue: pending_queue[tag]]
    K --> L[Add to Sequential<br/>List: pending_transactions[]]
    L --> M[Set matched = 1<br/>timestamp = $realtime]
    M --> N[Trigger Event:<br/>new_cfg_read_event]
    
    H --> O[Statistics:<br/>transactions_forwarded++]
    N --> P[Statistics:<br/>cfg_reads_detected++]
```

---

### **📋 RX Agent Monitoring Flow**

```mermaid
flowchart TD
    A[RX Agent Monitor<br/>Receives Transaction] --> B{Transaction Type<br/>Check}
    
    B -->|COMPLETION_32B| C[Extract Completion<br/>Details: tag, srcid]
    B -->|Other Types| D[Forward to<br/>Driver Agent]
    
    C --> E[Lookup Pending Transaction<br/>pending_queue[tag]]
    E --> F{Pending Transaction<br/>Found?}
    
    F -->|No| G[Forward Original<br/>Completion to Driver]
    F -->|Yes| H{Source ID<br/>Matches?}
    
    H -->|No| G
    H -->|Yes| I{Transaction<br/>Marked as Matched?}
    
    I -->|No| G
    I -->|Yes| J[INTERCEPT<br/>Original Completion]
    
    J --> K[Generate Custom<br/>Completion Response]
    K --> L[Set Custom Data:<br/>cfg.custom_completion_data]
    L --> M[Set Custom Status:<br/>cfg.custom_completion_status]
    M --> N[Swap Source/Destination<br/>IDs for Response]
    N --> O[Send Custom Completion<br/>via Driver Agent]
    
    O --> P[Remove from<br/>pending_queue[tag]]
    P --> Q[Remove from<br/>pending_transactions[]]
    Q --> R[Update Statistics<br/>completions_modified++]
    
    G --> S[Update Statistics<br/>completions_passed_through++]
    D --> T[Update Statistics<br/>other_transactions_forwarded++]
```

---

## 🎯 **Matching Criteria Decision Tree**

```mermaid
flowchart TD
    A[CFG_READ_32B<br/>Transaction Received] --> B{Address Matching<br/>Enabled?}
    
    B -->|No| C{Source ID Matching<br/>Enabled?}
    B -->|Yes| D{Address in Range?<br/>(addr & mask) == (base & mask)}
    
    D -->|No| E[❌ No Match<br/>Forward Transaction]
    D -->|Yes| C
    
    C -->|No| F{Tag Matching<br/>Enabled?}
    C -->|Yes| G{Source ID Match?<br/>srcid == match_srcid}
    
    G -->|No| E
    G -->|Yes| F
    
    F -->|No| H[✅ Match Found<br/>Store as Pending]
    F -->|Yes| I{Tag in Range?<br/>(tag & mask) == (base & mask)}
    
    I -->|No| E
    I -->|Yes| H
    
    H --> J[Create Pending Entry:<br/>tag, srcid, dstid, addr, be]
    J --> K[Set matched = 1<br/>timestamp = $realtime]
    K --> L[Store in pending_queue[tag]]
    L --> M[Add to pending_transactions[]]
```

---

## ⏰ **Timeout Management Flow**

```mermaid
flowchart TD
    A[Timeout Cleanup Task<br/>Periodic Execution] --> B[Iterate Through<br/>pending_transactions[]]
    
    B --> C{More Transactions<br/>to Check?}
    C -->|No| D[Wait for Next<br/>Cleanup Cycle]
    C -->|Yes| E[Get Next Transaction<br/>pending_transactions[i]]
    
    E --> F[Check Age:<br/>$realtime - timestamp]
    F --> G{Age > Timeout<br/>Threshold?}
    
    G -->|No| H[Continue to<br/>Next Transaction]
    G -->|Yes| I[Remove from<br/>pending_queue[tag]]
    
    I --> J[Remove from<br/>pending_transactions[i]]
    J --> K[Update Statistics<br/>transactions_timed_out++]
    K --> L[Log Timeout Event<br/>if Debug Enabled]
    
    L --> H
    H --> C
    D --> A
```

---

## 📊 **Complete System Flow with Statistics**

```mermaid
flowchart TD
    subgraph "TX Path Monitoring"
        A1[TX Agent Monitor] --> A2{CFG_READ_32B?}
        A2 -->|Yes| A3{Match Criteria?}
        A2 -->|No| A4[Forward → Driver]
        A3 -->|Yes| A5[Store Pending]
        A3 -->|No| A4
        A5 --> A6[cfg_reads_detected++]
    end
    
    subgraph "RX Path Monitoring"  
        B1[RX Agent Monitor] --> B2{COMPLETION_32B?}
        B2 -->|Yes| B3{Find Pending?}
        B2 -->|No| B4[Forward → Driver]
        B3 -->|Found & Matched| B5[INTERCEPT]
        B3 -->|Not Found| B6[Forward → Driver]
        B5 --> B7[Generate Custom]
        B7 --> B8[Send via Driver]
        B8 --> B9[completions_modified++]
        B6 --> B10[completions_passed_through++]
        B4 --> B11[other_forwarded++]
    end
    
    subgraph "Timeout Management"
        C1[Periodic Cleanup] --> C2{Check Age}
        C2 -->|Expired| C3[Remove Transaction]
        C2 -->|Valid| C4[Keep Transaction]
        C3 --> C5[transactions_timed_out++]
    end
    
    subgraph "Driver Output"
        D1[Driver Agent] --> D2[Send to DUT/Interface]
        D2 --> D3[Update Performance<br/>Metrics]
    end
    
    A4 --> D1
    A6 --> B1
    B8 --> D1
    B6 --> D1
    B4 --> D1
    C5 --> D3
    B9 --> D3
    B10 --> D3
```

---

## 🔧 **Configuration-Based Flow Control**

```mermaid
flowchart TD
    A[Transaction Received] --> B{Pass-through<br/>Mode Enabled?}
    
    B -->|Yes| C[Forward All<br/>Transactions to Driver]
    B -->|No| D{Interception<br/>Enabled?}
    
    D -->|No| C
    D -->|Yes| E{Debug Mode<br/>Enabled?}
    
    E -->|Yes| F[Log Debug Info<br/>Extended Timeout]
    E -->|No| G[Normal Processing]
    
    F --> H[Process Transaction<br/>with Detailed Logging]
    G --> I[Process Transaction<br/>Standard Mode]
    
    H --> J{Statistics<br/>Enabled?}
    I --> J
    
    J -->|Yes| K[Update Counters<br/>Performance Metrics]
    J -->|No| L[Skip Statistics]
    
    K --> M[Continue Processing]
    L --> M
    C --> N[Update Pass-through<br/>Statistics]
```

---

## 📈 **Performance Monitoring Flow**

```mermaid
flowchart TD
    A[Transaction Processing<br/>Start] --> B[Record Start Time<br/>start_time = $realtime]
    
    B --> C[Execute Interception<br/>Logic]
    C --> D[Record End Time<br/>end_time = $realtime]
    D --> E[Calculate Duration<br/>process_time = end_time - start_time]
    
    E --> F[Update Total Time<br/>total_intercept_time += process_time]
    F --> G{process_time ><br/>max_intercept_time?}
    
    G -->|Yes| H[Update Max<br/>max_intercept_time = process_time]
    G -->|No| I{min_intercept_time == 0<br/>OR process_time < min?}
    
    H --> I
    I -->|Yes| J[Update Min<br/>min_intercept_time = process_time]
    I -->|No| K[Calculate Average<br/>avg = total_time / count]
    
    J --> K
    K --> L[Update Statistics<br/>Report if Enabled]
    L --> M[Continue Processing]
```

---

## 🎯 **Key Decision Points Summary**

| Decision Point | Condition | Action | Statistics Updated |
|----------------|-----------|--------|-------------------|
| **TX Monitor** | Non-CFG_READ | Forward to Driver | `transactions_forwarded++` |
| **TX Monitor** | CFG_READ + No Match | Forward to Driver | `cfg_reads_detected++` |
| **TX Monitor** | CFG_READ + Match | Store Pending | `cfg_reads_detected++` |
| **RX Monitor** | Non-COMPLETION | Forward to Driver | `other_forwarded++` |
| **RX Monitor** | COMPLETION + No Pending | Forward to Driver | `completions_passed_through++` |
| **RX Monitor** | COMPLETION + Pending Match | Intercept & Generate Custom | `completions_modified++` |
| **Timeout** | Expired Transaction | Remove from Queue | `transactions_timed_out++` |

---

This flow chart provides a complete visual representation of the transaction interceptor's decision logic, showing exactly when transactions are intercepted versus passed through, and how the system maintains performance statistics throughout the process.