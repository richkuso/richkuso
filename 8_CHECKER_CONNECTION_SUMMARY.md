# 8 Register Checker Architecture Summary

## Architecture Overview

### Connection Pattern: 16 Agents → 8 Checkers (2 agents per checker)

```
Agent 0  → reg_checker_0.tx_fifo
Agent 1  → reg_checker_0.rx_fifo

Agent 2  → reg_checker_1.tx_fifo  
Agent 3  → reg_checker_1.rx_fifo

Agent 4  → reg_checker_2.tx_fifo
Agent 5  → reg_checker_2.rx_fifo

Agent 6  → reg_checker_3.tx_fifo
Agent 7  → reg_checker_3.rx_fifo

Agent 8  → reg_checker_4.tx_fifo
Agent 9  → reg_checker_4.rx_fifo

Agent 10 → reg_checker_5.tx_fifo
Agent 11 → reg_checker_5.rx_fifo

Agent 12 → reg_checker_6.tx_fifo
Agent 13 → reg_checker_6.rx_fifo

Agent 14 → reg_checker_7.tx_fifo
Agent 15 → reg_checker_7.rx_fifo
```

## Implementation Details

### 1. Environment Structure (`ucie_sb_env.sv`)

**Register Checker Array:**
```systemverilog
// 8 register checkers (each handles 2 agents)
ucie_sb_reg_access_checker reg_checkers[8];
```

**Checker Creation:**
```systemverilog
// Create 8 register access checkers
for (int j = 0; j < 8; j++) begin
  string checker_name = $sformatf("reg_checker_%0d", j);
  reg_checkers[j] = ucie_sb_reg_access_checker::type_id::create(checker_name, this);
end
```

### 2. Connection Logic

**Pattern Implementation:**
```systemverilog
// Connect 16 agents to 8 register checkers in pairs
// Pattern: agent(2*i) → checker[i].tx_fifo, agent(2*i+1) → checker[i].rx_fifo
for (int i = 0; i < 8; i++) begin
  int agent_tx_idx = 2 * i;      // Even agents (0,2,4,6,8,10,12,14)
  int agent_rx_idx = 2 * i + 1;  // Odd agents (1,3,5,7,9,11,13,15)
  
  // Connect even agent to TX FIFO
  agents[agent_tx_idx].monitor.ap.connect(reg_checkers[i].tx_fifo.analysis_export);
  
  // Connect odd agent to RX FIFO
  agents[agent_rx_idx].monitor.ap.connect(reg_checkers[i].rx_fifo.analysis_export);
end
```

### 3. Testbench Interface Configuration

**Checker Interface Assignment:**
```systemverilog
// Set interfaces for 8 register checkers (each gets interface from first agent in pair)
for (int m = 0; m < 8; m++) begin
  string checker_path = $sformatf("uvm_test_top.sb_env.reg_checker_%0d", m);
  uvm_config_db#(virtual ucie_sb_interface)::set(null, checker_path, "vif", sb_intf[2*m]); // Use even agent's interface
end
```

## Connection Validation

### Agent-to-Checker Mapping
| Checker | TX Agent | RX Agent | Interface Used |
|---------|----------|----------|----------------|
| reg_checker_0 | Agent 0 | Agent 1 | sb_intf[0] |
| reg_checker_1 | Agent 2 | Agent 3 | sb_intf[2] |
| reg_checker_2 | Agent 4 | Agent 5 | sb_intf[4] |
| reg_checker_3 | Agent 6 | Agent 7 | sb_intf[6] |
| reg_checker_4 | Agent 8 | Agent 9 | sb_intf[8] |
| reg_checker_5 | Agent 10 | Agent 11 | sb_intf[10] |
| reg_checker_6 | Agent 12 | Agent 13 | sb_intf[12] |
| reg_checker_7 | Agent 14 | Agent 15 | sb_intf[14] |

### Interface Distribution
- **Agents**: Each agent gets its own dedicated interface (sb_intf[i])
- **Checkers**: Each checker gets the interface from its first agent (even-numbered agent)

### Config Database Paths
```
Agent Interfaces:
"uvm_test_top.sb_env.agent_0*"  → sb_intf[0]
"uvm_test_top.sb_env.agent_1*"  → sb_intf[1]
...
"uvm_test_top.sb_env.agent_15*" → sb_intf[15]

Checker Interfaces:
"uvm_test_top.sb_env.reg_checker_0" → sb_intf[0]
"uvm_test_top.sb_env.reg_checker_1" → sb_intf[2]
"uvm_test_top.sb_env.reg_checker_2" → sb_intf[4]
"uvm_test_top.sb_env.reg_checker_3" → sb_intf[6]
"uvm_test_top.sb_env.reg_checker_4" → sb_intf[8]
"uvm_test_top.sb_env.reg_checker_5" → sb_intf[10]
"uvm_test_top.sb_env.reg_checker_6" → sb_intf[12]
"uvm_test_top.sb_env.reg_checker_7" → sb_intf[14]
```

## Architecture Benefits

### 1. **Balanced Load Distribution**
- Each checker handles exactly 2 agents
- Even distribution of monitoring workload
- Paired TX/RX analysis per checker

### 2. **Logical Grouping**
- Adjacent agents are paired together
- Consistent checker numbering
- Easy to understand agent-to-checker mapping

### 3. **Scalable Design**
- Formula-based connection: checker[i] handles agents[2*i] and [2*i+1]
- Easy to modify number of checkers/agents
- Clear mathematical relationship

### 4. **Independent Analysis**
- Each checker can independently analyze its agent pair
- No cross-checker dependencies
- Parallel processing capabilities

## Validation Results ✅

### Connection Verification
- ✅ **16 Agents Created**: agent_0 through agent_15
- ✅ **8 Checkers Created**: reg_checker_0 through reg_checker_7
- ✅ **TX Connections**: Even agents (0,2,4,6,8,10,12,14) → respective checker tx_fifo
- ✅ **RX Connections**: Odd agents (1,3,5,7,9,11,13,15) → respective checker rx_fifo
- ✅ **Interface Distribution**: Each agent has dedicated interface, checkers use even agent interfaces

### Mathematical Validation
For checker index `i` (0 ≤ i ≤ 7):
- **TX Agent**: `2*i` (even numbers: 0,2,4,6,8,10,12,14)
- **RX Agent**: `2*i+1` (odd numbers: 1,3,5,7,9,11,13,15)
- **Interface**: `sb_intf[2*i]` (even interfaces: 0,2,4,6,8,10,12,14)

### Coverage Verification
- ✅ All 16 agents are connected
- ✅ All 8 checkers have both TX and RX inputs
- ✅ No agent is connected to multiple checkers
- ✅ No checker is missing connections

## Debug and Monitoring

### Connection Tracing
Each connection is logged during connect_phase:
```
Agent[0] Monitor → reg_checker_0.tx_fifo
Agent[1] Monitor → reg_checker_0.rx_fifo
Agent[2] Monitor → reg_checker_1.tx_fifo
Agent[3] Monitor → reg_checker_1.rx_fifo
...
```

### Checker Identification
Checkers are named systematically:
- `reg_checker_0`, `reg_checker_1`, ..., `reg_checker_7`
- Clear mapping to agent pairs
- Easy identification in logs and debug

This architecture provides optimal load balancing with clear, predictable connections between agents and checkers, enabling efficient parallel analysis of sideband transactions.