# SystemVerilog UVM 1.2 Counter Testbench

这是一个使用SystemVerilog和UVM 1.2编写的完整验证环境示例，用于验证一个简单的8位计数器模块。

## 项目结构

```
.
├── counter.sv              # 计数器设计模块 (DUT)
├── counter_interface.sv    # SystemVerilog接口定义
├── counter_pkg.sv         # UVM包 (包含所有UVM组件)
├── testbench.sv           # 顶层测试台
├── Makefile              # 编译和仿真脚本
└── README.md             # 项目说明
```

## 设计特性

### 计数器模块 (counter.sv)
- 8位可参数化宽度计数器
- 支持异步复位
- 支持使能控制
- 支持并行加载
- 溢出检测功能

### SystemVerilog接口 (counter_interface.sv)
- 定义了DUT的所有信号
- 包含驱动和监控的时钟域
- 内置SVA断言用于协议检查
- 模块端口定义

### UVM验证环境 (counter_pkg.sv)
完整的UVM 1.2验证环境包括：

#### Transaction Item
- `counter_transaction`: 定义事务项
- 包含随机化约束
- UVM字段宏支持

#### Sequences
- `counter_sequence`: 主要测试序列
- `counter_reset_sequence`: 复位序列
- 随机化测试向量生成

#### UVM组件
- `counter_driver`: 驱动器
- `counter_monitor`: 监控器
- `counter_scoreboard`: 记分板
- `counter_agent`: 代理
- `counter_env`: 环境
- `counter_test`: 测试用例

## 编译和运行

### 前提条件
- SystemVerilog仿真器 (VCS或Questa/ModelSim)
- UVM 1.2库
- 设置环境变量 `UVM_HOME`

### 使用Makefile

```bash
# 查看帮助
make help

# 编译和运行 (默认使用VCS)
make all

# 仅编译
make compile

# 仅运行
make run

# 使用不同的仿真器
make all SIM=vcs      # 使用VCS
make all SIM=questa   # 使用Questa/ModelSim

# 不同详细程度运行
make run_low          # UVM_LOW
make run_medium       # UVM_MEDIUM  
make run_high         # UVM_HIGH
make run_full         # UVM_FULL

# 清理生成文件
make clean
```

### 手动编译 (VCS示例)

```bash
# 编译
vcs -sverilog -ntb_opts uvm-1.2 +incdir+$UVM_HOME/src \
    -timescale=1ns/1ps -full64 -debug_access+all \
    counter.sv counter_interface.sv counter_pkg.sv testbench.sv \
    -o simv

# 运行
./simv +UVM_TESTNAME=counter_test +UVM_VERBOSITY=UVM_MEDIUM
```

## UVM验证方法学

### 验证策略
1. **功能覆盖**: 使用约束随机化生成测试向量
2. **断言检查**: SystemVerilog断言验证协议
3. **自检查**: 记分板自动比较期望值和实际值
4. **分层测试**: 模块化的UVM架构

### 测试场景
- 复位功能测试
- 正常计数测试
- 并行加载测试
- 溢出检测测试
- 随机混合操作测试

### 覆盖率
- 功能覆盖点定义
- 代码覆盖率收集
- 断言覆盖率

## 波形查看

仿真完成后会生成 `counter_test.vcd` 波形文件，可以使用以下工具查看：

```bash
# 使用DVE (VCS)
dve -vpd counter_test.vcd

# 使用GTKWave
gtkwave counter_test.vcd
```

## 扩展和自定义

### 添加新的测试序列
1. 在 `counter_pkg.sv` 中定义新的sequence类
2. 在测试用例中调用新序列
3. 重新编译运行

### 修改设计参数
- 修改 `counter_pkg.sv` 中的 `WIDTH` 参数
- 支持不同位宽的计数器验证

### 添加新的验证组件
- 可以添加覆盖率收集器
- 可以添加更多的检查器
- 可以添加性能监控组件

## 故障排除

### 常见问题
1. **UVM_HOME未设置**: 确保环境变量指向UVM库路径
2. **编译错误**: 检查仿真器版本和UVM版本兼容性
3. **仿真挂起**: 检查时钟生成和复位逻辑

### 调试技巧
- 使用 `+UVM_VERBOSITY=UVM_HIGH` 获取详细日志
- 查看波形文件分析时序
- 使用UVM调试功能

## 许可和版权

本项目仅用于教学和学习目的。