// UVM Report Server Implementation Comparison
// 比较不同UVM报告服务器实现方法

package report_comparison_pkg;
    
    import uvm_pkg::*;
    import custom_report_pkg::*;
    import custom_report_v2_pkg::*;
    `include "uvm_macros.svh"
    
    // 测试类用于演示不同的报告服务器实现
    class report_comparison_test extends uvm_test;
        
        `uvm_component_utils(report_comparison_test)
        
        function new(string name = "report_comparison_test", uvm_component parent = null);
            super.new(name, parent);
        endfunction
        
        virtual task run_phase(uvm_phase phase);
            phase.raise_objection(this);
            
            `uvm_info("COMPARISON", "=== UVM Report Server Implementation Comparison ===", UVM_LOW)
            
            // 说明两种实现方法
            `uvm_info("METHOD1", "方法1: 继承uvm_default_report_server，重写format_action", UVM_LOW)
            `uvm_info("METHOD2", "方法2: 继承uvm_default_report_server，重写process_report", UVM_LOW)
            
            // 演示消息
            `uvm_info("DEMO", "这是一个演示消息", UVM_LOW)
            `uvm_warning("DEMO", "这是一个警告消息")
            
            #100;
            `uvm_info("DEMO", "测试不同的消息ID", UVM_MEDIUM)
            
            phase.drop_objection(this);
        endtask
        
    endclass
    
endpackage

// 比较测试台
module report_comparison_tb;
    
    import uvm_pkg::*;
    import report_comparison_pkg::*;
    import custom_report_pkg::*;
    import custom_report_v2_pkg::*;
    `include "uvm_macros.svh"
    
    initial begin
        string implementation;
        
        // 从命令行获取实现方式选择
        if ($value$plusargs("IMPL=%s", implementation)) begin
            case (implementation)
                "v1": begin
                    `uvm_info("SETUP", "Using implementation v1 (format_action method)", UVM_LOW)
                    custom_report_config::setup_custom_report_server();
                end
                "v2": begin
                    `uvm_info("SETUP", "Using implementation v2 (process_report method)", UVM_LOW)
                    custom_report_config_v2::setup();
                end
                default: begin
                    `uvm_info("SETUP", "Using default implementation v2", UVM_LOW)
                    custom_report_config_v2::setup();
                end
            endcase
        end else begin
            `uvm_info("SETUP", "Using default implementation v2", UVM_LOW)
            custom_report_config_v2::setup();
        end
        
        // 运行测试
        run_test("report_comparison_test");
    end
    
endmodule