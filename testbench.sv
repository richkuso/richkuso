// Top-level testbench module
module testbench;
    
    import uvm_pkg::*;
    import counter_pkg::*;
    import advanced_tests_pkg::*;
    `include "uvm_macros.svh"
    
    // Clock and reset generation
    logic clk;
    logic rst_n;
    
    // Clock generation
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
        // Set interface in config_db
        uvm_config_db#(virtual counter_if)::set(null, "*", "vif", counter_if_inst);
        
        // Enable waveform dumping
        $dumpfile("counter_test.vcd");
        $dumpvars(0, testbench);
        
        // Run the test
        run_test("counter_test");
    end
    
    // Timeout watchdog
    initial begin
        #1000000; // 1ms timeout
        `uvm_error("TIMEOUT", "Test timeout!")
        $finish;
    end
    
endmodule