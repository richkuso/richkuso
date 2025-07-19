// Custom UVM Report Server
// 用于修改UVM_INFO等宏的输出格式，特别是文件路径部分

package custom_report_pkg;
    
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    // 自定义报告服务器类
    class custom_report_server extends uvm_default_report_server;
        
        `uvm_object_utils(custom_report_server)
        
        function new(string name = "custom_report_server");
            super.new(name);
        endfunction
        
        // 重写format_action方法来自定义消息格式
        virtual function string format_action(uvm_severity severity,
                                             uvm_report_object ro,
                                             string filename,
                                             int line,
                                             string id,
                                             uvm_action action,
                                             string message);
            
            string time_str, severity_str, custom_filename;
            string object_name;
            
            // 获取仿真时间
            time_str = $sformatf("%0t", $time);
            
            // 获取对象名称
            object_name = (ro != null) ? ro.get_full_name() : "";
            
            // 转换severity为字符串
            case (severity)
                UVM_INFO:    severity_str = "UVM_INFO";
                UVM_WARNING: severity_str = "UVM_WARNING";
                UVM_ERROR:   severity_str = "UVM_ERROR";
                UVM_FATAL:   severity_str = "UVM_FATAL";
                default:     severity_str = "UVM_UNKNOWN";
            endcase
            
            // 自定义文件路径处理
            custom_filename = process_filename(filename);
            
            // 构造自定义格式的消息
            return compose_custom_message(severity_str, time_str, custom_filename, 
                                        line, id, object_name, message);
        endfunction
        
        // 处理文件名的函数 - 可以根据需要修改
        virtual function string process_filename(string original_filename);
            string processed_filename;
            int slash_pos, last_slash_pos;
            
            // 选项1: 只显示文件名，不显示路径
            // processed_filename = extract_filename_only(original_filename);
            
            // 选项2: 显示相对路径（从src开始）
            // processed_filename = extract_relative_path(original_filename);
            
            // 选项3: 自定义缩写路径
            processed_filename = create_abbreviated_path(original_filename);
            
            return processed_filename;
        endfunction
        
        // 只提取文件名
        function string extract_filename_only(string full_path);
            int slash_pos;
            string filename;
            
            // 找到最后一个斜杠的位置
            for (int i = full_path.len() - 1; i >= 0; i--) begin
                if (full_path[i] == "/" || full_path[i] == "\\") begin
                    slash_pos = i + 1;
                    break;
                end
            end
            
            filename = full_path.substr(slash_pos, full_path.len() - 1);
            return filename;
        endfunction
        
        // 提取相对路径
        function string extract_relative_path(string full_path);
            string relative_path;
            int src_pos, tb_pos, test_pos;
            
            // 寻找常见的目录标识符
            src_pos = full_path.search("src/");
            tb_pos = full_path.search("tb/");
            test_pos = full_path.search("test/");
            
            if (src_pos != -1) begin
                relative_path = full_path.substr(src_pos, full_path.len() - 1);
            end
            else if (tb_pos != -1) begin
                relative_path = full_path.substr(tb_pos, full_path.len() - 1);
            end
            else if (test_pos != -1) begin
                relative_path = full_path.substr(test_pos, full_path.len() - 1);
            end
            else begin
                relative_path = extract_filename_only(full_path);
            end
            
            return relative_path;
        endfunction
        
        // 创建缩写路径
        function string create_abbreviated_path(string full_path);
            string abbreviated_path;
            string filename;
            int slash_count = 0;
            int last_slash_pos = -1, second_last_slash_pos = -1;
            
            // 计算斜杠数量并找到位置
            for (int i = full_path.len() - 1; i >= 0; i--) begin
                if (full_path[i] == "/" || full_path[i] == "\\") begin
                    slash_count++;
                    if (slash_count == 1) last_slash_pos = i;
                    else if (slash_count == 2) second_last_slash_pos = i;
                    else break;
                end
            end
            
            filename = extract_filename_only(full_path);
            
            // 根据路径长度决定显示策略
            if (slash_count >= 2 && second_last_slash_pos > 0) begin
                string parent_dir = full_path.substr(second_last_slash_pos + 1, last_slash_pos - 1);
                abbreviated_path = $sformatf(".../%s/%s", parent_dir, filename);
            end
            else if (slash_count >= 1 && last_slash_pos > 0) begin
                string parent_dir = full_path.substr(last_slash_pos + 1, full_path.len() - 1);
                abbreviated_path = $sformatf(".../%s", filename);
            end
            else begin
                abbreviated_path = filename;
            end
            
            return abbreviated_path;
        endfunction
        
        // 组合自定义消息格式
        virtual function string compose_custom_message(string severity_str,
                                                     string time_str,
                                                     string filename,
                                                     int line_num,
                                                     string id_str,
                                                     string object_name,
                                                     string message);
            string formatted_message;
            
            // 自定义格式选项 - 可以根据需要修改
            
            // 格式1: 简洁格式
            formatted_message = $sformatf("# %s @ %s: [%s] %s (%s:%0d)",
                                        severity_str, time_str, id_str, message, filename, line_num);
            
            // 格式2: 详细格式（注释掉的备选方案）
            /*
            if (object_name != "") begin
                formatted_message = $sformatf("# %s @ %s ns: [%s] %s - %s\n#   File: %s, Line: %0d",
                                            severity_str, time_str, id_str, object_name, message, filename, line_num);
            end
            else begin
                formatted_message = $sformatf("# %s @ %s ns: [%s] %s\n#   File: %s, Line: %0d",
                                            severity_str, time_str, id_str, message, filename, line_num);
            end
            */
            
            // 格式3: 类似传统格式但带自定义路径
            /*
            formatted_message = $sformatf("%s @ %s: (%s) [%s] %s",
                                        severity_str, time_str, filename, id_str, message);
            */
            
            return formatted_message;
        endfunction
        
    endclass
    
    // 报告服务器配置类
    class custom_report_config;
        
        // 设置自定义报告服务器
        static function void setup_custom_report_server();
            custom_report_server custom_server;
            
            custom_server = custom_report_server::type_id::create("custom_server");
            uvm_report_server::set_server(custom_server);
            
            `uvm_info("CUSTOM_REPORT", "Custom report server has been installed", UVM_LOW)
        endfunction
        
        // 配置报告格式选项
        static function void configure_report_format(bit show_time = 1,
                                                   bit show_verbosity = 0,
                                                   bit show_color = 0);
            uvm_report_server server;
            
            server = uvm_report_server::get_server();
            
            // 这些是UVM标准的配置选项
            if (show_time) begin
                // 启用时间显示（如果支持）
            end
            
            if (show_verbosity) begin
                // 启用详细级别显示（如果支持）
            end
            
            if (show_color) begin
                // 启用颜色显示（如果终端支持）
            end
        endfunction
        
        // 设置文件路径显示模式
        static function void set_path_display_mode(string mode = "abbreviated");
            // 这可以用来在运行时改变路径显示模式
            // 需要在custom_report_server中添加相应的成员变量和逻辑
        endfunction
        
    endclass

endpackage