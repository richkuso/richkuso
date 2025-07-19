#!/bin/bash

# SystemVerilog UVM Counter Testbench Runner
# 使用方法: ./run_sim.sh [test_name] [verbosity]

# 设置默认值
TEST_NAME=${1:-counter_test}
VERBOSITY=${2:-UVM_MEDIUM}
SIM=${SIM:-vcs}

echo "=========================================="
echo "SystemVerilog UVM 1.2 Counter Testbench"
echo "=========================================="
echo "Test: $TEST_NAME"
echo "Verbosity: $VERBOSITY"
echo "Simulator: $SIM"
echo "=========================================="

# 检查UVM_HOME环境变量
if [ -z "$UVM_HOME" ]; then
    echo "警告: UVM_HOME 环境变量未设置"
    echo "请设置 UVM_HOME 指向您的UVM安装路径"
    echo "例如: export UVM_HOME=/path/to/uvm"
    exit 1
fi

# 清理之前的文件
echo "清理之前的仿真文件..."
make clean

# 编译
echo "编译设计..."
if ! make compile SIM=$SIM; then
    echo "编译失败!"
    exit 1
fi

# 运行仿真
echo "运行仿真..."
if [ "$SIM" = "vcs" ]; then
    ./simv +UVM_TESTNAME=$TEST_NAME +UVM_VERBOSITY=$VERBOSITY
elif [ "$SIM" = "questa" ]; then
    vsim -c -do "run -all; quit" testbench +UVM_TESTNAME=$TEST_NAME +UVM_VERBOSITY=$VERBOSITY
else
    echo "不支持的仿真器: $SIM"
    echo "支持的仿真器: vcs, questa"
    exit 1
fi

# 检查仿真结果
if [ $? -eq 0 ]; then
    echo "=========================================="
    echo "仿真完成!"
    echo "=========================================="
    if [ -f "counter_test.vcd" ]; then
        echo "波形文件: counter_test.vcd"
        echo "使用以下命令查看波形:"
        echo "  gtkwave counter_test.vcd"
        echo "  或"
        echo "  make waves"
    fi
else
    echo "=========================================="
    echo "仿真失败!"
    echo "=========================================="
    exit 1
fi