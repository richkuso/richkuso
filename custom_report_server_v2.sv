// Accurate Custom UVM Report Server Implementation
// 正确的UVM报告服务器自定义实现

package custom_report_v2_pkg;
    
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    // 自定义报告服务器类 - 继承uvm_default_report_server
    class custom_report_server_v2 extends uvm_default_report_server;
        
        typedef enum {
            PATH_FULL,          // 显示完整路径
            PATH_FILENAME_ONLY, // 只显示文件名
            PATH_RELATIVE,      // 显示相对路径
            PATH_ABBREVIATED    // 显示缩写路径
        } path_display_mode_e;
        
        path_display_mode_e path_mode;
        bit show_time;
        bit show_line_numbers;
        bit use_color;
        
        `uvm_object_utils(custom_report_server_v2)
        
        function new(string name = "custom_report_server_v2");
            super.new(name);
            path_mode = PATH_ABBREVIATED;
            show_time = 1;
            show_line_numbers = 1;
            use_color = 0;
        endfunction
        
        // 重写process_report方法 - 这是UVM报告处理的核心方法
        virtual function void process_report(uvm_severity severity,
                                           string id,
                                           string message,
                                           int verbosity,
                                           string filename,
                                           int line,
                                           uvm_report_object client);
            
            uvm_action action;
            UVM_FILE file_handle;
            string formatted_message;
            
            // 获取该报告的动作
            action = client.get_report_action(severity, id);
            
            // 如果动作包含显示，则格式化并显示消息
            if (action & UVM_DISPLAY) begin
                formatted_message = format_message(severity, id, message, verbosity, 
                                                 filename, line, client);
                $display("%s", formatted_message);
            end
            
            // 如果动作包含日志记录，则写入文件
            if (action & UVM_LOG) begin
                file_handle = client.get_report_file_handle(severity, id);
                if (file_handle != 0) begin
                    formatted_message = format_message(severity, id, message, verbosity, 
                                                     filename, line, client);
                    $fdisplay(file_handle, "%s", formatted_message);
                end
            end
            
            // 如果动作包含计数，则增加计数器
            if (action & UVM_COUNT) begin
                incr_severity_count(severity);
            end
            
            // 如果是错误或致命错误，检查是否需要退出
            if (action & UVM_EXIT) begin
                uvm_report_server::get_server().report_summarize();
                $finish;
            end
            
            // 如果是致命错误且动作包含停止
            if (severity == UVM_FATAL && (action & UVM_STOP)) begin
                $stop;
            end
        endfunction
        
        // 格式化消息的函数
        virtual function string format_message(uvm_severity severity,
                                             string id,
                                             string message,
                                             int verbosity,
                                             string filename,
                                             int line,
                                             uvm_report_object client);
            
            string severity_str, time_str, object_name, processed_filename;
            string color_start = "", color_end = "";
            string formatted_msg;
            
            // 转换severity为字符串
            case (severity)
                UVM_INFO:    severity_str = "UVM_INFO";
                UVM_WARNING: severity_str = "UVM_WARNING";
                UVM_ERROR:   severity_str = "UVM_ERROR";
                UVM_FATAL:   severity_str = "UVM_FATAL";
                default:     severity_str = "UVM_UNKNOWN";
            endcase
            
            // 获取时间戳
            if (show_time) begin
                time_str = $sformatf(" @ %0t", $time);
            end else begin
                time_str = "";
            end
            
            // 获取对象名称
            object_name = (client != null) ? client.get_full_name() : "";
            
            // 处理文件名
            processed_filename = process_filename(filename);
            
            // 添加颜色编码
            if (use_color) begin
                case (severity)
                    UVM_INFO:    begin color_start = "\033[32m"; color_end = "\033[0m"; end // 绿色
                    UVM_WARNING: begin color_start = "\033[33m"; color_end = "\033[0m"; end // 黄色
                    UVM_ERROR:   begin color_start = "\033[31m"; color_end = "\033[0m"; end // 红色
                    UVM_FATAL:   begin color_start = "\033[35m"; color_end = "\033[0m"; end // 紫色
                endcase
            end
            
            // 组合最终消息
            if (show_line_numbers) begin
                if (object_name != "") begin
                    formatted_msg = $sformatf("%s# %s%s: (%s) [%s] %s - %s (%s:%0d)%s",
                                            color_start, severity_str, time_str, object_name,
                                            id, message, processed_filename, line, color_end);
                end else begin
                    formatted_msg = $sformatf("%s# %s%s: [%s] %s (%s:%0d)%s",
                                            color_start, severity_str, time_str,
                                            id, message, processed_filename, line, color_end);
                end
            end else begin
                if (object_name != "") begin
                    formatted_msg = $sformatf("%s# %s%s: (%s) [%s] %s - %s%s",
                                            color_start, severity_str, time_str, object_name,
                                            id, message, processed_filename, color_end);
                end else begin
                    formatted_msg = $sformatf("%s# %s%s: [%s] %s (%s)%s",
                                            color_start, severity_str, time_str,
                                            id, message, processed_filename, color_end);
                end
            end
            
            return formatted_msg;
        endfunction
        
        // 处理文件名的函数
        virtual function string process_filename(string original_filename);
            case (path_mode)
                PATH_FULL:          return original_filename;
                PATH_FILENAME_ONLY: return extract_filename_only(original_filename);
                PATH_RELATIVE:      return extract_relative_path(original_filename);
                PATH_ABBREVIATED:   return create_abbreviated_path(original_filename);
                default:            return create_abbreviated_path(original_filename);
            endcase
        endfunction
        
        // 只提取文件名
        function string extract_filename_only(string full_path);
            int slash_pos = -1;
            
            // 找到最后一个斜杠的位置
            for (int i = full_path.len() - 1; i >= 0; i--) begin
                if (full_path[i] == "/" || full_path[i] == "\\") begin
                    slash_pos = i + 1;
                    break;
                end
            end
            
            if (slash_pos >= 0) begin
                return full_path.substr(slash_pos, full_path.len() - 1);
            end else begin
                return full_path;
            end
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
                abbreviated_path = $sformatf(".../%s", filename);
            end
            else begin
                abbreviated_path = filename;
            end
            
            return abbreviated_path;
        endfunction
        
        // 配置方法
        function void set_path_mode(path_display_mode_e mode);
            path_mode = mode;
        endfunction
        
        function void set_show_time(bit enable);
            show_time = enable;
        endfunction
        
        function void set_show_line_numbers(bit enable);
            show_line_numbers = enable;
        endfunction
        
        function void set_use_color(bit enable);
            use_color = enable;
        endfunction
        
    endclass
    
    // 配置类
    class custom_report_config_v2;
        
        static custom_report_server_v2 server;
        
        // 安装自定义报告服务器
        static function void setup();
            server = custom_report_server_v2::type_id::create("custom_server_v2");
            uvm_report_server::set_server(server);
            `uvm_info("CUSTOM_REPORT", "Custom report server v2 installed", UVM_LOW)
        endfunction
        
        // 配置方法
        static function void set_path_mode(string mode);
            if (server == null) return;
            
            case (mode)
                "full":         server.set_path_mode(custom_report_server_v2::PATH_FULL);
                "filename":     server.set_path_mode(custom_report_server_v2::PATH_FILENAME_ONLY);
                "relative":     server.set_path_mode(custom_report_server_v2::PATH_RELATIVE);
                "abbreviated":  server.set_path_mode(custom_report_server_v2::PATH_ABBREVIATED);
                default:        server.set_path_mode(custom_report_server_v2::PATH_ABBREVIATED);
            endcase
        endfunction
        
        static function void enable_timestamps(bit enable);
            if (server != null) server.set_show_time(enable);
        endfunction
        
        static function void enable_line_numbers(bit enable);
            if (server != null) server.set_show_line_numbers(enable);
        endfunction
        
        static function void enable_color(bit enable);
            if (server != null) server.set_use_color(enable);
        endfunction
        
    endclass

endpackage