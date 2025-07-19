// Custom Report Server Demo
// 展示如何使用不同的文件路径显示模式

package custom_report_demo_pkg;
    
    import uvm_pkg::*;
    import counter_pkg::*;
    import custom_report_pkg::*;
    `include "uvm_macros.svh"
    
    // 演示不同路径显示模式的测试
    class report_demo_test extends uvm_test;
        
        counter_env env;
        
        `uvm_component_utils(report_demo_test)
        
        function new(string name = "report_demo_test", uvm_component parent = null);
            super.new(name, parent);
        endfunction
        
        virtual function void build_phase(uvm_phase phase);
            super.build_phase(phase);
            env = counter_env::type_id::create("env", this);
        endfunction
        
        virtual task run_phase(uvm_phase phase);
            phase.raise_objection(this);
            
            `uvm_info(get_type_name(), "=== Custom Report Server Demo ===", UVM_LOW)
            `uvm_info("DEMO", "这是一个UVM_INFO消息示例", UVM_LOW)
            `uvm_info("DEMO", "文件路径将按照自定义格式显示", UVM_MEDIUM)
            
            // 演示不同类型的消息
            `uvm_warning("DEMO", "这是一个UVM_WARNING消息示例")
            
            // 从不同的组件发送消息
            `uvm_info("BUILD", "构建阶段完成", UVM_HIGH)
            `uvm_info("CONFIG", "配置数据库设置完成", UVM_HIGH)
            
            // 模拟一些测试活动
            #100;
            `uvm_info("TEST", "开始测试序列", UVM_LOW)
            
            #200;
            `uvm_info("TEST", "测试进行中...", UVM_MEDIUM)
            
            #300;
            `uvm_info("TEST", "测试完成", UVM_LOW)
            
            `uvm_info(get_type_name(), "=== Demo Complete ===", UVM_LOW)
            
            phase.drop_objection(this);
        endtask
        
    endclass
    
    // 高级自定义报告服务器，支持运行时配置
    class advanced_custom_report_server extends custom_report_server;
        
        typedef enum {
            PATH_FULL,          // 显示完整路径
            PATH_FILENAME_ONLY, // 只显示文件名
            PATH_RELATIVE,      // 显示相对路径
            PATH_ABBREVIATED    // 显示缩写路径
        } path_display_mode_e;
        
        path_display_mode_e current_mode;
        bit show_line_numbers;
        bit show_time_stamp;
        bit use_color_coding;
        
        `uvm_object_utils(advanced_custom_report_server)
        
        function new(string name = "advanced_custom_report_server");
            super.new(name);
            current_mode = PATH_ABBREVIATED;
            show_line_numbers = 1;
            show_time_stamp = 1;
            use_color_coding = 0;
        endfunction
        
        // 设置路径显示模式
        function void set_path_mode(path_display_mode_e mode);
            current_mode = mode;
            `uvm_info("REPORT_CONFIG", $sformatf("Path display mode set to: %s", mode.name()), UVM_LOW)
        endfunction
        
        // 重写文件名处理函数
        virtual function string process_filename(string original_filename);
            case (current_mode)
                PATH_FULL:          return original_filename;
                PATH_FILENAME_ONLY: return extract_filename_only(original_filename);
                PATH_RELATIVE:      return extract_relative_path(original_filename);
                PATH_ABBREVIATED:   return create_abbreviated_path(original_filename);
                default:            return create_abbreviated_path(original_filename);
            endcase
        endfunction
        
        // 重写消息组合函数以支持更多选项
        virtual function string compose_custom_message(string severity_str,
                                                     string time_str,
                                                     string filename,
                                                     int line_num,
                                                     string id_str,
                                                     string object_name,
                                                     string message);
            string formatted_message;
            string time_part = show_time_stamp ? $sformatf(" @ %s", time_str) : "";
            string line_part = show_line_numbers ? $sformatf(":%0d", line_num) : "";
            string color_start = "", color_end = "";
            
            // 添加颜色编码（如果启用）
            if (use_color_coding) begin
                case (severity_str)
                    "UVM_INFO":    begin color_start = "\033[32m"; color_end = "\033[0m"; end // 绿色
                    "UVM_WARNING": begin color_start = "\033[33m"; color_end = "\033[0m"; end // 黄色
                    "UVM_ERROR":   begin color_start = "\033[31m"; color_end = "\033[0m"; end // 红色
                    "UVM_FATAL":   begin color_start = "\033[35m"; color_end = "\033[0m"; end // 紫色
                endcase
            end
            
            formatted_message = $sformatf("%s# %s%s: [%s] %s (%s%s)%s",
                                        color_start, severity_str, time_part, id_str, 
                                        message, filename, line_part, color_end);
            
            return formatted_message;
        endfunction
        
    endclass
    
    // 高级配置类
    class advanced_report_config;
        
        static advanced_custom_report_server adv_server;
        
        // 设置高级自定义报告服务器
        static function void setup_advanced_report_server();
            adv_server = advanced_custom_report_server::type_id::create("adv_server");
            uvm_report_server::set_server(adv_server);
            `uvm_info("CUSTOM_REPORT", "Advanced custom report server installed", UVM_LOW)
        endfunction
        
        // 运行时配置函数
        static function void set_path_display_mode(string mode);
            if (adv_server == null) return;
            
            case (mode)
                "full":         adv_server.set_path_mode(advanced_custom_report_server::PATH_FULL);
                "filename":     adv_server.set_path_mode(advanced_custom_report_server::PATH_FILENAME_ONLY);
                "relative":     adv_server.set_path_mode(advanced_custom_report_server::PATH_RELATIVE);
                "abbreviated":  adv_server.set_path_mode(advanced_custom_report_server::PATH_ABBREVIATED);
                default:        adv_server.set_path_mode(advanced_custom_report_server::PATH_ABBREVIATED);
            endcase
        endfunction
        
        static function void enable_color_coding(bit enable = 1);
            if (adv_server == null) return;
            adv_server.use_color_coding = enable;
            `uvm_info("REPORT_CONFIG", $sformatf("Color coding %s", enable ? "enabled" : "disabled"), UVM_LOW)
        endfunction
        
        static function void show_line_numbers(bit show = 1);
            if (adv_server == null) return;
            adv_server.show_line_numbers = show;
            `uvm_info("REPORT_CONFIG", $sformatf("Line numbers %s", show ? "enabled" : "disabled"), UVM_LOW)
        endfunction
        
        static function void show_timestamps(bit show = 1);
            if (adv_server == null) return;
            adv_server.show_time_stamp = show;
            `uvm_info("REPORT_CONFIG", $sformatf("Timestamps %s", show ? "enabled" : "disabled"), UVM_LOW)
        endfunction
        
    endclass
    
    // 配置演示测试
    class report_config_demo_test extends uvm_test;
        
        counter_env env;
        
        `uvm_component_utils(report_config_demo_test)
        
        function new(string name = "report_config_demo_test", uvm_component parent = null);
            super.new(name, parent);
        endfunction
        
        virtual function void build_phase(uvm_phase phase);
            super.build_phase(phase);
            env = counter_env::type_id::create("env", this);
        endfunction
        
        virtual task run_phase(uvm_phase phase);
            phase.raise_objection(this);
            
            `uvm_info("DEMO", "=== 报告格式配置演示 ===", UVM_LOW)
            
            // 演示不同的路径显示模式
            `uvm_info("DEMO", "当前使用缩写路径模式", UVM_LOW)
            
            #100;
            advanced_report_config::set_path_display_mode("filename");
            `uvm_info("DEMO", "切换到只显示文件名模式", UVM_LOW)
            
            #100;
            advanced_report_config::set_path_display_mode("full");
            `uvm_info("DEMO", "切换到完整路径模式", UVM_LOW)
            
            #100;
            advanced_report_config::set_path_display_mode("relative");
            `uvm_info("DEMO", "切换到相对路径模式", UVM_LOW)
            
            #100;
            advanced_report_config::enable_color_coding(1);
            `uvm_info("DEMO", "启用颜色编码", UVM_LOW)
            `uvm_warning("DEMO", "这是带颜色的警告消息")
            
            #100;
            advanced_report_config::show_line_numbers(0);
            `uvm_info("DEMO", "禁用行号显示", UVM_LOW)
            
            #100;
            advanced_report_config::show_timestamps(0);
            `uvm_info("DEMO", "禁用时间戳显示", UVM_LOW)
            
            `uvm_info("DEMO", "=== 演示完成 ===", UVM_LOW)
            
            phase.drop_objection(this);
        endtask
        
    endclass

endpackage