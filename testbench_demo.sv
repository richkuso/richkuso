// Demo testbench for custom report server
module testbench_demo;
    
    import uvm_pkg::*;
    import counter_pkg::*;
    import custom_report_pkg::*;
    import custom_report_demo_pkg::*;
    `include "uvm_macros.svh"
    
    // Clock generation
    logic clk;
    initial begin
        clk = 0;
        forever #5 clk = ~clk; // 100MHz clock
    end
    
    // Interface instantiation
    counter_if #(.WIDTH(counter_pkg::WIDTH)) counter_if_inst (clk);
    
    // DUT instantiation
    counter #(.WIDTH(counter_pkg::WIDTH)) dut (
        .clk(clk),
        .rst_n(counter_if_inst.rst_n),
        .enable(counter_if_inst.enable),
        .load(counter_if_inst.load),
        .load_data(counter_if_inst.load_data),
        .count(counter_if_inst.count),
        .overflow(counter_if_inst.overflow)
    );
    
    // Test execution
    initial begin
        string test_name;
        
        // Get test name from command line or use default
        if ($value$plusargs("UVM_TESTNAME=%s", test_name)) begin
            case (test_name)
                "report_config_demo_test": begin
                    // Setup advanced report server for configuration demo
                    advanced_report_config::setup_advanced_report_server();
                end
                default: begin
                    // Setup basic custom report server
                    custom_report_config::setup_custom_report_server();
                end
            endcase
        end
        else begin
            // Default setup
            custom_report_config::setup_custom_report_server();
            test_name = "report_demo_test";
        end
        
        // Set interface in config_db
        uvm_config_db#(virtual counter_if)::set(null, "*", "vif", counter_if_inst);
        
        // Enable waveform dumping
        $dumpfile("report_demo.vcd");
        $dumpvars(0, testbench_demo);
        
        // Print demo information
        `uvm_info("DEMO_TB", "=== Custom Report Server Demo Testbench ===", UVM_LOW)
        `uvm_info("DEMO_TB", $sformatf("Running test: %s", test_name), UVM_LOW)
        
        // Run the test
        run_test(test_name);
    end
    
    // Timeout watchdog
    initial begin
        #500000; // 500us timeout
        `uvm_error("TIMEOUT", "Demo timeout!")
        $finish;
    end
    
endmodule