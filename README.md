# SystemVerilog UVM 1.2 Counter Testbench

这是一个使用SystemVerilog和UVM 1.2编写的完整验证环境示例，用于验证一个简单的8位计数器模块。

## 项目结构

```
.
├── counter.sv              # 计数器设计模块 (DUT)
├── counter_interface.sv    # SystemVerilog接口定义
├── counter_pkg.sv         # UVM包 (包含所有UVM组件)
├── advanced_tests.sv      # 高级测试序列和覆盖率
├── custom_report_server.sv # 自定义UVM报告服务器
├── custom_report_demo.sv  # 报告服务器演示
├── testbench.sv           # 顶层测试台
├── testbench_demo.sv      # 演示测试台
├── Makefile              # 编译和仿真脚本
├── run_sim.sh            # 仿真运行脚本
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

### 自定义报告服务器

项目提供了两种UVM报告服务器的实现方法：

#### 方法1: custom_report_server.sv
- **继承**: `uvm_default_report_server`
- **重写方法**: `format_action`
- **特点**: 简单实现，主要修改消息格式

#### 方法2: custom_report_server_v2.sv (推荐)
- **继承**: `uvm_default_report_server`
- **重写方法**: `process_report`
- **特点**: 完全控制报告处理流程，更灵活

#### 支持的路径显示模式
1. **完整路径**: 显示完整的文件路径
2. **仅文件名**: 只显示文件名，不显示路径
3. **相对路径**: 显示从src/tb/test开始的相对路径
4. **缩写路径**: 显示`.../<parent_dir>/<filename>`格式

#### 为什么选择继承uvm_default_report_server？
- `uvm_report_server`是抽象基类，包含纯虚函数
- `uvm_default_report_server`是具体实现，提供了完整的功能
- 继承`uvm_default_report_server`可以选择性重写特定方法，而不需要实现所有接口

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

# 自定义报告服务器演示
make run_demo          # 基本演示
make run_config_demo   # 配置演示
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

## 自定义UVM报告服务器使用指南

### 基本用法
项目已经集成了自定义报告服务器，会自动在testbench启动时安装。

### 消息格式
自定义报告服务器会将UVM消息格式化为：
```
# UVM_INFO @ 1000: [ID] 消息内容 (.../<parent_dir>/<filename>:行号)
```

### 高级配置
使用高级报告服务器可以在运行时动态配置：

```systemverilog
// 在测试中使用
advanced_report_config::setup_advanced_report_server();

// 设置路径显示模式
advanced_report_config::set_path_display_mode("filename");    // 仅文件名
advanced_report_config::set_path_display_mode("full");        // 完整路径  
advanced_report_config::set_path_display_mode("relative");    // 相对路径
advanced_report_config::set_path_display_mode("abbreviated"); // 缩写路径

// 其他配置选项
advanced_report_config::enable_color_coding(1);  // 启用颜色
advanced_report_config::show_line_numbers(0);    // 禁用行号
advanced_report_config::show_timestamps(0);      // 禁用时间戳
```

### 自定义格式
可以通过继承`custom_report_server`类来实现自己的消息格式：

```systemverilog
class my_report_server extends custom_report_server;
    virtual function string compose_custom_message(...);
        // 实现自定义格式
        return $sformatf("MY_FORMAT: %s", message);
    endfunction
endclass
```

## 许可和版权

本项目仅用于教学和学习目的。